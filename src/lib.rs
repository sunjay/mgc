mod trace;
mod alloc;
mod gc;

pub use trace::*;
pub use alloc::*;
pub use gc::*;

use std::iter;
use std::mem;
use std::cmp::max;
use std::ptr::{self, NonNull};
use std::alloc::{Layout, handle_alloc_error};
use std::sync::atomic::{AtomicBool, Ordering};

use parking_lot::{Mutex, const_mutex};

#[doc(hidden)] // Not part of the public API of this crate, but needed in all modules
#[macro_export]
macro_rules! gc_debug {
    ($($arg:tt)*) => {{
        #[cfg(feature = "debug")]
        println!($($arg)*);
    }};
}

/// An arbitrary value. The goal is to make it so that as the amount of memory the program uses
/// grows, the threshold moves farther out to limit the total time spent re-traversing the larger
/// live set. Could be tuned with some real-world programs.
const GC_HEAP_GROW_FACTOR: usize = 2;

/// An arbitrary value. The goal is to not trigger the first few GCs too quickly but also to not
/// wait too long. Could be tuned with some real-world programs.
const GC_DEFAULT_THRESHOLD: usize = 1024 * 1024; // bytes

#[derive(Debug)]
struct InnerState {
    /// A linked list of allocations managed by the GC
    alloc_list: Option<NonNull<GcHeader>>,
    /// The number of bytes needed to trigger a collection
    threshold: usize,
    /// The number of bytes currently allocated
    allocated: usize,
}

// Safety: This state is explicitly managed behind a Mutex to guarantee thread-safety
unsafe impl Send for InnerState {}

impl Default for InnerState {
    fn default() -> Self {
        Self::new()
    }
}

impl InnerState {
    const fn new() -> Self {
        Self {
            alloc_list: None,
            threshold: GC_DEFAULT_THRESHOLD,
            // Nothing has been allocated yet
            allocated: 0,
        }
    }
}

/// A single heap allocated entry managed by the GC
#[repr(C)]
struct GcEntry<T: ?Sized> {
    /// A header containing extra metadata needed by the GC
    ///
    /// Due to the `repr(C)` attribute, the address of this header is the same as the address
    /// returned by the heap allocation. This allows headers to be operated on independently from
    /// the type T.
    header: GcHeader,
    /// The actual allocated value
    value: T,
}

impl<T: ?Sized + Trace> Trace for GcEntry<T> {
    // GcEntry types are not traced, but they need to implement Trace so we can create a trait object
    fn trace(&self) {}
}

#[derive(Debug)]
struct GcHeader {
    /// The number of values allocated
    len: usize,
    /// The size of each allocated value
    size: usize,
    /// The pointer to the vtable for the type T stored in this allocation
    ///
    /// Optimization: Set to null if `T` does not need to be dropped
    vtable: Option<NonNull<()>>,
    /// The layout used to allocate the entire `GcEntry<T>`
    layout: Layout,
    /// The address of the previous allocation (makes this an intrusive list node)
    next: Option<NonNull<GcHeader>>,
    /// if true, the allocation is still reachable from a root
    is_reachable: bool,
}

impl GcHeader {
    fn array<T>(len: usize, vtable: *mut (), layout: Layout) -> Self {
        Self {
            len,
            size: mem::size_of::<T>(),
            vtable: NonNull::new(vtable),
            layout,
            next: None,
            // Presume not reachable until proven otherwise
            is_reachable: false,
        }
    }
}

/// Marks a value managed by the GC as reachable
///
/// Returns true if the value was already marked previously.
///
/// # Safety
///
/// This function may only be used with pointers returned from `allocate`. It should not be called
/// concurrently with `sweep`.
unsafe fn mark<T: ?Sized>(ptr: NonNull<T>) -> bool {
    gc_debug!("{:p} mark", ptr);

    // Safety: Since `GcEntry` is #[repr(C)], the fields are laid out with `GcHeader` before `T`.
    // That means that we *should* be able to just subtract the size of `GcHeader` to get to the
    // `header` field from the `value` field. Note: sub(1) == -(sizeof(GcHeader)*1).
    //
    //TODO: Not actually sure if this offset will always work. A more implementation independent way
    //  would be to construct a fake `GcEntry` and then find out the actual offset between the
    //  `header` and `value` fields.
    let header_ptr = (ptr.as_ptr() as *mut GcHeader).sub(1);
    let mut header = &mut *header_ptr;

    let prev_reachable = header.is_reachable;
    header.is_reachable = true;
    prev_reachable
}

pub struct GcState<A: Allocator = GlobalAlloc> {
    allocator: A,
    inner: Mutex<InnerState>,
    /// true if the threshold has been reached for the next collection
    needs_collect: AtomicBool,
}

impl GcState {
    pub const fn new() -> Self {
        Self {
            allocator: GlobalAlloc::new(),
            inner: const_mutex(InnerState::new()),
            needs_collect: AtomicBool::new(false),
        }
    }
}

impl<A: Allocator> GcState<A> {
    /// Creates a new `GcState` with the given allocator
    pub fn with_alloc(allocator: A) -> Self {
        Self {
            allocator,
            inner: const_mutex(InnerState::new()),
            needs_collect: AtomicBool::new(false),
        }
    }

    /// Returns true if `sweep` should be called as soon as possible
    pub fn needs_collect(&self) -> bool {
        self.needs_collect.load(Ordering::Relaxed)
    }

    /// Allocates memory managed by the GC and initializes it to the given values
    ///
    /// Returns a GC pointer to the values or aborts on memory allocation failure
    pub fn alloc_array<T, I>(&self, values: I) -> Gc<[T]>
        where T: Trace,
              I: ExactSizeIterator<Item=T>,
    {
        let ptr = self.alloc_array_ptr(values);
        // Safety: Pointer is coming from our internal allocation function, so it is definitely
        // valid for the `Gc` type
        unsafe { Gc::from_raw(ptr) }
    }

    /// Attempts to allocate memory managed by the GC and initialize it to the given values
    ///
    /// Returns a GC pointer to the values or an error if the allocation failed
    pub fn try_alloc_array<T, I>(&self, values: I) -> Result<Gc<[T]>, AllocError>
        where T: Trace,
              I: ExactSizeIterator<Item=T>,
    {
        let ptr = self.try_alloc_array_ptr(values)?;
        // Safety: Pointer is coming from our internal allocation function, so it is definitely
        // valid for the `Gc` type
        Ok(unsafe { Gc::from_raw(ptr) })
    }

    fn alloc_array_ptr<T, I>(&self, values: I) -> NonNull<[T]>
        where T: Trace,
              I: ExactSizeIterator<Item=T>,
    {
        self.try_alloc_array_ptr(values)
            .unwrap_or_else(|err| handle_alloc_error(err.into_inner()))
    }

    /// Allocate memory managed by the GC and initialize it to the given values
    ///
    /// Returns a non-null pointer to the values
    fn try_alloc_array_ptr<T, I>(&self, values: I) -> Result<NonNull<[T]>, AllocError>
        where T: Trace,
              I: ExactSizeIterator<Item=T>,
    {
        // Start by generating the layout for the array, essentially `GcEntry<[T]>`
        let len = values.len();

        // Safety: The layout being generated here must match the layout of `GcEntry`
        let header_layout = Layout::new::<GcHeader>();
        let array_layout = Layout::array::<T>(len).expect("bug: failed to create array layout");
        let (layout, array_start_bytes) = header_layout.extend(array_layout).expect("bug: failed to create `GcEntry` layout");
        // Always need to finish a layout with `pad_to_align`
        let layout = layout.pad_to_align();

        debug_assert_eq!(array_start_bytes, mem::size_of::<GcHeader>(),
            "bug: `mgc::mark` depends on the allocated value starting right after the header with no padding");

        // Allocate the `GcEntry<[T]>`
        // Safety: Due to the header, the layout passed to `alloc` cannot be zero-sized
        let entry_ptr = unsafe { self.allocator.alloc(layout)? };

        // Extract the vtable only if we have at least one element and that element needs to be dropped
        let mut values = values.peekable();
        let vtable = if len == 0 || !mem::needs_drop::<T>() {
            ptr::null_mut()
        } else {
            // This unwrap is fine because we just checked the length
            extract_vtable(values.peek().unwrap())
        };

        // Initialize the header (`header` field of `GcEntry<[T]>`)
        // Safety: #[repr(C)] guarantees that a pointer to `GcEntry` is the same as a pointer to
        // `GcHeader` (since `header` is the first field)
        let header_ptr: NonNull<GcHeader> = entry_ptr.cast();
        let header = GcHeader::array::<T>(len, vtable, layout);
        unsafe { header_ptr.as_ptr().write(header); }

        // Initialize the array (`value` field of `GcEntry<[T]>`)
        // Safety: Any offsets we take here must match the layouts used to allocate above
        let array = unsafe { entry_ptr.as_ptr().add(array_start_bytes) } as *mut T;
        for (i, value) in values.enumerate() {
            // Safety: We just allocated and checked `entry_ptr`, so this should work
            unsafe { array.add(i).write(value); }
        }

        // Safety: We initialized the `array` pointer earlier so it should still allow us to make a
        // valid slice with the given length. We already checked if the original `entry_ptr` was null.
        let value_ptr = unsafe { NonNull::new_unchecked(ptr::slice_from_raw_parts_mut(array, len)) };

        // Append onto the list of all allocations
        //
        // Note that this critical section is kept as small as possible to allow allocation and
        // initialiation to occur in parallel as much as possible
        let mut gc_state = self.inner.lock();
        let next = gc_state.alloc_list;
        gc_state.alloc_list = Some(header_ptr);
        // Safety: The header was initialized above, so it should still be valid to assign to
        unsafe { (*header_ptr.as_ptr()).next = next; }

        // Record the amount of memory that was allocated
        gc_state.allocated += layout.size();
        if gc_state.allocated > gc_state.threshold {
            // Notify that a collection should take place ASAP
            self.needs_collect.store(true, Ordering::Relaxed);
        }

        gc_debug!("{:p} allocate - size: {} bytes, type: {}, len: {}", value_ptr, array_layout.size(),
            std::any::type_name::<T>(), len);

        Ok(value_ptr)
    }

    /// Frees the memory associated with the given allocation
    ///
    /// Returns the number of bytes that were deallocated as well as a pointer to the next allocation in
    /// the allocation list after the one that was freed.
    ///
    /// # Safety
    ///
    /// This function may only be used with pointers from the allocation list in `GC_STATE`.
    unsafe fn free(&self, ptr: NonNull<GcHeader>) -> (usize, Option<NonNull<GcHeader>>) {
        // Extract info from the header
        // Safety: The pointer should be valid because it is currently in the allocation list. Note that
        // in order to avoid aliasing issues we are careful to copy the values out (avoids references).
        let GcHeader {len, size, vtable, layout, next, ..} = *ptr.as_ref();

        gc_debug!("{:p} free - size: {} bytes, len: {}", ptr.as_ptr().add(1), size, len);

        // Only drop if a vtable was provided for that
        if let Some(vtable) = vtable {
            // Free each item in the array by constructing a trait object for each item and calling
            // `drop_in_place`

            // Safety: Much like `mark`, this assumes that the `value` begins immediately after the
            // header field with no padding
            let array = (ptr.as_ptr() as *mut GcHeader).add(1) as *mut u8;

            for i in 0..len {
                let data = array.add(i*size) as *mut ();
                let obj: &mut dyn Trace = mem::transmute(TraitObject {
                    data,
                    vtable: vtable.as_ptr(),
                });
                ptr::drop_in_place(obj);
            }
        }

        // Free the memory
        self.allocator.dealloc(ptr.cast(), layout);

        (layout.size(), next)
    }

    /// Sweeps/collects all allocations that have been not been marked as reachable
    ///
    /// # Safety
    ///
    /// This function pauses all other GC functions while it is running. No calls to `trace` should
    /// take place while this is running.
    pub fn sweep(&self) {
        // Keep the GC state locked so no allocations can be registered while this takes place
        let mut gc_state = self.inner.lock();

        gc_debug!("sweep start: {} bytes allocated", gc_state.allocated);

        // Register ASAP that we are currently collecting so no other thread starts a `sweep`
        self.needs_collect.store(false, Ordering::Relaxed);

        let mut prev = None;
        let mut current = gc_state.alloc_list;
        while let Some(mut header) = current {
            // We need to be careful to keep the lifetime of &GcHeader short so we don't break the
            // aliasing rules when `free` takes ownership of the data.
            let is_reachable = {
                // Safety: the header should be a valid pointer or it would not be in the list.
                let header = unsafe { header.as_mut() };
                // Advance the loop
                current = header.next;

                // Store the reachable status of this allocation
                let is_reachable = header.is_reachable;
                // Reset `is_reachable` for next collection
                header.is_reachable = false;

                is_reachable
            };

            if is_reachable {
                // Only update prev with the allocations we aren't freeing
                prev = Some(header);
                continue;
            }

            // Safety: All the pointers we are going through are from `alloc_list`.
            let (bytes_freed, next) = unsafe { self.free(header) };
            gc_state.allocated -= bytes_freed;

            // Remove the freed allocation from the linked list
            match prev {
                // Assign the next pointer of the previous item to the list to the item just after the
                // item that was just freed
                Some(mut prev_header) => unsafe {
                    prev_header.as_mut().next = next;
                },

                // No previous, must be the head of the list
                None => gc_state.alloc_list = next,
            }
        }

        gc_debug!("sweep end: {} bytes allocated", gc_state.allocated);

        // Adjust the threshold based on how much is still allocated
        //
        // If all memory gets deallocated, we don't want the threshold to get set to zero
        gc_state.threshold = max(gc_state.allocated * GC_HEAP_GROW_FACTOR, GC_DEFAULT_THRESHOLD);
    }
}

pub trait GcStateAlloc<T> {
    type Output: Trace + ?Sized;

    /// Attempts to allocate memory managed by the GC and initialize it to the given value
    ///
    /// Returns a GC pointer to the value or an error if the allocation failed
    fn try_alloc(&self, value: T) -> Result<Gc<Self::Output>, AllocError>;

    /// Allocates memory managed by the GC and initializes it to the given value
    ///
    /// Returns a GC pointer to the value or aborts on memory allocation failure
    fn alloc(&self, value: T) -> Gc<Self::Output> {
        self.try_alloc(value)
            .unwrap_or_else(|err| handle_alloc_error(err.into_inner()))
    }
}

impl<T: Trace> GcStateAlloc<T> for GcState {
    type Output = T;

    fn try_alloc(&self, value: T) -> Result<Gc<Self::Output>, AllocError> {
        // Allocate the value as an array of one value
        let ptr = self.try_alloc_array_ptr(iter::once(value))?.cast();
        // Safety: Pointer is coming from our internal allocation function, so it is definitely
        // valid for the `Gc` type
        Ok(unsafe { Gc::from_raw(ptr) })
    }
}

impl<'a, T: Trace + Clone> GcStateAlloc<&'a [T]> for GcState {
    type Output = [T];

    #[inline]
    fn try_alloc(&self, slice: &'a [T]) -> Result<Gc<Self::Output>, AllocError> {
        self.try_alloc_array(slice.iter().cloned())
    }
}

impl<T: Trace> GcStateAlloc<Vec<T>> for GcState {
    type Output = [T];

    #[inline]
    fn try_alloc(&self, items: Vec<T>) -> Result<Gc<Self::Output>, AllocError> {
        self.try_alloc_array(items.into_iter())
    }
}

// This code is similar to the From impl for Arc<str>
impl GcStateAlloc<&str> for GcState {
    type Output = str;

    #[inline]
    fn try_alloc(&self, value: &str) -> Result<Gc<Self::Output>, AllocError> {
        use std::str;

        let ptr = Gc::into_raw(self.try_alloc(value.as_bytes())?);

        // Safety: Since the bytes came from a valid `str`, we must still be producing a valid `str`.
        let str_ptr = unsafe { NonNull::new_unchecked(ptr.as_ptr() as *mut str) };

        // Safety: A pointer produced from `Gc::into_raw` is valid for `from_raw`.
        Ok(unsafe { Gc::from_raw(str_ptr) })
    }
}

// This code is similar to the From impl for Arc<str>
impl GcStateAlloc<String> for GcState {
    type Output = str;

    #[inline]
    fn try_alloc(&self, value: String) -> Result<Gc<Self::Output>, AllocError> {
        self.try_alloc(&value[..])
    }
}

impl GcStateAlloc<&std::sync::Arc<str>> for GcState {
    type Output = str;

    #[inline]
    fn try_alloc(&self, value: &std::sync::Arc<str>) -> Result<Gc<Self::Output>, AllocError> {
        self.try_alloc(&**value)
    }
}

impl GcStateAlloc<std::sync::Arc<str>> for GcState {
    type Output = str;

    #[inline]
    fn try_alloc(&self, value: std::sync::Arc<str>) -> Result<Gc<Self::Output>, AllocError> {
        self.try_alloc(&*value)
    }
}

/// Copied from: https://doc.rust-lang.org/std/raw/struct.TraitObject.html
//TODO: Will need to be updated in the future when the representation changes.
//  See: https://github.com/rust-lang/rust/issues/27751
#[repr(C)]
#[derive(Copy, Clone)]
pub struct TraitObject {
    pub data: *mut (),
    pub vtable: *mut (),
}

fn extract_vtable<T: Trace>(value: &T) -> *mut () {
    // Source: https://github.com/withoutboats/shifgrethor/blob/ab1873fc3e76e6b9fd9a96b11746617e14bd7c1c/src/lib/gc/alloc.rs#L110-L115
    unsafe {
        let obj = value as &dyn Trace;
        // Safety: This will continue to work as long as the unstable trait object layout does not change
        let TraitObject {vtable, ..} = mem::transmute(obj);
        vtable
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::{Arc, atomic::{AtomicU8, Ordering}};

    #[test]
    fn gc_alloc() {
        let gc_state = GcState::new();

        let value1 = gc_state.alloc(2i8);
        let value2 = gc_state.alloc(42i16);
        let value3 = gc_state.alloc(-33i32);
        let value4 = gc_state.alloc(54i64);
        let value5 = gc_state.alloc(-12931i128);

        // Check that all the values are as we expect
        assert_eq!(*value1, 2);
        assert_eq!(*value2, 42);
        assert_eq!(*value3, -33);
        assert_eq!(*value4, 54);
        assert_eq!(*value5, -12931);

        // Make sure we don't free pointers that have been traced
        value2.trace();
        value3.trace();

        gc_state.sweep();

        assert_eq!(*value2, 42);
        assert_eq!(*value3, -33);

        // Should clean up all memory at the end
        gc_state.sweep();
    }

    #[test]
    fn gc_str() {
        let gc_state = GcState::new();

        let value = gc_state.alloc("abc123 woooo");
        assert_eq!(&*value, "abc123 woooo");

        // Should not clean up anything because we've traced
        value.trace();
        gc_state.sweep();

        // Value should still be the same
        assert_eq!(&*value, "abc123 woooo");

        // Should clean up all memory at the end
        gc_state.sweep();
    }

    #[test]
    fn gc_array() {
        let gc_state = GcState::new();

        let values1: &[Gc<u16>] = &[
            gc_state.alloc(2),
            gc_state.alloc(3),
            gc_state.alloc(123),
            gc_state.alloc(70),
            gc_state.alloc(42),
        ];

        let values2: &[u16] = &[
            2,
            3,
            123,
            70,
            42,
        ];

        // These type annotations are unnecessary, but good for testing
        let array1: Gc<[Gc<u16>]> = gc_state.alloc(values1);
        let array2: Gc<[u16]> = gc_state.alloc(values2);

        // Check all values are as we expect
        assert_eq!(array1.len(), array2.len());
        for (a, b) in array1.iter().zip(array2.iter()) {
            assert_eq!(**a, *b);
        }

        array1.trace();
        array2.trace();

        // Should not clean up anything
        gc_state.sweep();

        // Check all values are still as we expect
        assert_eq!(array1.len(), array2.len());
        for (a, b) in array1.iter().zip(array2.iter()) {
            assert_eq!(**a, *b);
        }

        // Should clean up all memory at the end
        gc_state.sweep();
    }

    #[derive(Debug, Clone)]
    struct NeedsDrop {
        value: u8,
        counter: Arc<AtomicU8>,
    }

    impl Trace for NeedsDrop {
        fn trace(&self) {}
    }

    impl Drop for NeedsDrop {
        fn drop(&mut self) {
            self.counter.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn gc_array_drop() {
        let gc_state = GcState::new();

        let counter = Arc::new(AtomicU8::new(0));

        let values1: &[NeedsDrop] = &[
            NeedsDrop {value: 1, counter: counter.clone()},
            NeedsDrop {value: 2, counter: counter.clone()},
            NeedsDrop {value: 3, counter: counter.clone()},
            NeedsDrop {value: 4, counter: counter.clone()},
            NeedsDrop {value: 5, counter: counter.clone()},
        ];

        let array1: Gc<[NeedsDrop]> = gc_state.alloc(values1);

        assert_eq!(counter.load(Ordering::Relaxed), 0);
        assert_eq!(array1.len(), 5);
        for (a, b) in array1.iter().zip(1u8..) {
            assert_eq!(a.value, b);
        }

        // mark the value to prevent it from being collected
        array1.trace();

        // Should not clean up anything
        gc_state.sweep();
        assert_eq!(counter.load(Ordering::Relaxed), 0);

        // Should clean up all the memory at the end and call drop
        gc_state.sweep();
        assert_eq!(counter.load(Ordering::Relaxed), values1.len() as u8);
    }

    #[test]
    fn gc_zero_sized_types() {
        let gc_state = GcState::new();

        let value1 = gc_state.alloc(());
        let value2 = gc_state.alloc(&[] as &[i32]);

        // Should be able to access the value as normal
        assert_eq!(*value1, ());
        println!("{:?}", *value1);
        assert_eq!(*value2, []);
        println!("{:?}", &*value2);

        // marking the value should work even though it is zero-sized
        value1.trace();
        value2.trace();

        // Should not clean up anything
        gc_state.sweep();

        // Should be able to access the value as normal
        assert_eq!(*value1, ());
        println!("{:?}", *value1);
        assert_eq!(*value2, []);
        println!("{:?}", &*value2);

        // Should clean up all the memory at the end
        gc_state.sweep();
    }

    #[test]
    fn gc_cycles() {
        let gc_state = GcState::new();

        // Source: https://doc.rust-lang.org/book/ch15-06-reference-cycles.html
        use parking_lot::Mutex;

        #[derive(Debug)]
        enum List {
            Cons(i32, Mutex<Gc<List>>),
            Nil,
        }

        use List::*;

        impl Trace for List {
            fn trace(&self) {
                use List::*;
                match self {
                    Cons(_, rest) => rest.lock().trace(),
                    Nil => {},
                }
            }
        }

        impl List {
            pub fn value(&self) -> Option<i32> {
                match *self {
                    Cons(value, _) => Some(value),
                    Nil => None,
                }
            }

            pub fn tail(&self) -> Option<&Mutex<Gc<List>>> {
                match self {
                    Cons(_, item) => Some(item),
                    Nil => None,
                }
            }
        }

        let a = gc_state.alloc(Cons(5, Mutex::new(gc_state.alloc(Nil))));
        let b = gc_state.alloc(Cons(10, Mutex::new(Gc::clone(&a))));
        // Create reference cycle
        if let Some(link) = a.tail() {
            *link.lock() = Gc::clone(&b);
        }

        // Values should be as we initialized
        assert_eq!(a.value(), Some(5));
        assert_eq!(b.value(), Some(10));

        // Should not loop infinitely
        a.trace();

        // Values should still be the same
        assert_eq!(a.value(), Some(5));
        assert_eq!(b.value(), Some(10));

        // Should not clean up anything (since `trace` marks the values)
        gc_state.sweep();

        // Values should still be the same
        assert_eq!(a.value(), Some(5));
        assert_eq!(b.value(), Some(10));

        // Should clean up all the memory at the end
        gc_state.sweep();
    }
}
