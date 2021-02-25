mod trace;
mod alloc;
mod gc;
mod state;

pub use trace::*;
pub use alloc::*;
pub use gc::*;

use std::iter;
use std::ptr::NonNull;
use std::alloc::handle_alloc_error;
use std::sync::atomic::{AtomicBool, Ordering};

use parking_lot::{Mutex, const_mutex};

use state::InnerState;

#[doc(hidden)] // Not part of the public API of this crate, but needed in all modules
#[macro_export]
macro_rules! gc_debug {
    ($($arg:tt)*) => {{
        #[cfg(feature = "debug")]
        println!($($arg)*);
    }};
}

static GLOBAL_GC: GcState<GlobalAlloc> = GcState::with_global();

pub struct GcState<A: Alloc = GlobalAlloc> {
    alloc: A,
    inner: Mutex<InnerState>,
    /// true if the threshold has been reached for the next collection
    needs_collect: AtomicBool,
}

impl GcState<GlobalAlloc> {
    pub(crate) const fn with_global() -> Self {
        Self {
            alloc: GlobalAlloc::new(),
            inner: const_mutex(InnerState::new()),
            needs_collect: AtomicBool::new(false),
        }
    }
}

impl<A: Alloc + Default> GcState<A> {
    pub fn new() -> Self {
        Self::with_alloc(Default::default())
    }
}

impl<A: Alloc> GcState<A> {
    pub fn with_alloc(alloc: A) -> Self {
        Self {
            alloc,
            inner: const_mutex(InnerState::new()),
            needs_collect: AtomicBool::new(false),
        }
    }

    /// Returns true if `sweep` should be called as soon as possible
    pub fn needs_collect(&self) -> bool {
        self.needs_collect.load(Ordering::Relaxed)
    }

    /// Allocates memory managed by the GC and initializes it to the given value
    ///
    /// Returns a GC pointer to the value or aborts on memory allocation failure
    pub fn alloc<T: Trace>(&self, value: T) -> Gc<T> {
        // Allocate the value as an array of one value
        let ptr = self.alloc_array_ptr(iter::once(value)).cast();
        // Safety: Pointer is coming from our internal allocation function, so it is definitely
        // valid for the `Gc` type
        unsafe { Gc::from_raw(ptr) }
    }

    /// Attempts to allocate memory managed by the GC and initialize it to the given value
    ///
    /// Returns a GC pointer to the value or an error if the allocation failed
    pub fn try_alloc<T: Trace>(&self, value: T) -> Result<Gc<T>, AllocError> {
        // Allocate the value as an array of one value
        let ptr = self.try_alloc_array_ptr(iter::once(value))?.cast();
        // Safety: Pointer is coming from our internal allocation function, so it is definitely
        // valid for the `Gc` type
        Ok(unsafe { Gc::from_raw(ptr) })
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

    pub fn alloc_array_ptr<T, I>(&self, values: I) -> NonNull<[T]>
        where T: Trace,
              I: ExactSizeIterator<Item=T>,
    {
        self.try_alloc_array_ptr(values)
            .unwrap_or_else(|err| handle_alloc_error(err.into_inner()))
    }

    pub fn try_alloc_array_ptr<T, I>(&self, values: I) -> Result<NonNull<[T]>, AllocError>
        where T: Trace,
              I: ExactSizeIterator<Item=T>,
    {
        todo!()
    }

    pub unsafe fn sweep(&self) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::{Arc, atomic::{AtomicU8, Ordering}};

    /// This is used to allow GC tests to pretend they are the only thing using the GC at any given time
    static GC_TEST_LOCK: parking_lot::Mutex<()> = parking_lot::const_mutex(());

    #[test]
    fn gc_alloc() {
        let _lock = GC_TEST_LOCK.lock();

        let value1 = Gc::new(2i8);
        let value2 = Gc::new(42i16);
        let value3 = Gc::new(-33i32);
        let value4 = Gc::new(54i64);
        let value5 = Gc::new(-12931i128);

        // Check that all the values are as we expect
        assert_eq!(*value1, 2);
        assert_eq!(*value2, 42);
        assert_eq!(*value3, -33);
        assert_eq!(*value4, 54);
        assert_eq!(*value5, -12931);

        // Make sure we don't free mgc::marked pointers
        mark(&value2);
        mark(&value3);

        sweep();

        assert_eq!(*value2, 42);
        assert_eq!(*value3, -33);

        // Should clean up all memory at the end
        sweep();
    }

    #[test]
    fn gc_str() {
        let _lock = GC_TEST_LOCK.lock();

        let value = Gc::from("abc123 woooo");
        assert_eq!(&*value, "abc123 woooo");

        // Should not clean up anything because we've traced
        value.trace();
        sweep();

        // Value should still be the same
        assert_eq!(&*value, "abc123 woooo");

        // Should clean up all memory at the end
        sweep();
    }

    #[test]
    fn gc_array() {
        let _lock = GC_TEST_LOCK.lock();

        let values1: &[Gc<u16>] = &[
            Gc::new(2),
            Gc::new(3),
            Gc::new(123),
            Gc::new(70),
            Gc::new(42),
        ];

        let values2: &[u16] = &[
            2,
            3,
            123,
            70,
            42,
        ];

        // These type annotations are unnecessary, but good for testing
        let array1: Gc<[Gc<u16>]> = Gc::from(values1);
        let array2: Gc<[u16]> = Gc::from(values2);

        // Check all values are as we expect
        assert_eq!(array1.len(), array2.len());
        for (a, b) in array1.iter().zip(array2.iter()) {
            assert_eq!(**a, *b);
        }

        array1.trace();
        array2.trace();

        // Should not clean up anything
        sweep();

        // Check all values are still as we expect
        assert_eq!(array1.len(), array2.len());
        for (a, b) in array1.iter().zip(array2.iter()) {
            assert_eq!(**a, *b);
        }

        // Should clean up all memory at the end
        sweep();
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
        let _lock = GC_TEST_LOCK.lock();

        let counter = Arc::new(AtomicU8::new(0));

        let values1: &[NeedsDrop] = &[
            NeedsDrop {value: 1, counter: counter.clone()},
            NeedsDrop {value: 2, counter: counter.clone()},
            NeedsDrop {value: 3, counter: counter.clone()},
            NeedsDrop {value: 4, counter: counter.clone()},
            NeedsDrop {value: 5, counter: counter.clone()},
        ];

        let array1: Gc<[NeedsDrop]> = Gc::from(values1);

        assert_eq!(counter.load(Ordering::SeqCst), 0);
        assert_eq!(array1.len(), 5);
        for (a, b) in array1.iter().zip(1u8..) {
            assert_eq!(a.value, b);
        }

        // mark the value to prevent it from being collected
        mark(&array1);

        // Should not clean up anything
        sweep();
        assert_eq!(counter.load(Ordering::SeqCst), 0);

        // Should clean up all the memory at the end and call drop
        sweep();
        assert_eq!(counter.load(Ordering::SeqCst), values1.len() as u8);
    }

    #[test]
    fn gc_zero_sized_types() {
        let _lock = GC_TEST_LOCK.lock();

        let value1 = Gc::new(());
        let value2 = Gc::from(&[] as &[i32]);

        // Should be able to access the value as normal
        assert_eq!(*value1, ());
        println!("{:?}", *value1);
        assert_eq!(*value2, []);
        println!("{:?}", &*value2);

        // marking the value should work even though it is zero-sized
        mark(&value1);
        mark(&value2);

        // Should not clean up anything
        sweep();

        // Should be able to access the value as normal
        assert_eq!(*value1, ());
        println!("{:?}", *value1);
        assert_eq!(*value2, []);
        println!("{:?}", &*value2);

        // Should clean up all the memory at the end
        sweep();
    }

    #[test]
    fn gc_cycles() {
        let _lock = GC_TEST_LOCK.lock();

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

        let a = Gc::new(Cons(5, Mutex::new(Gc::new(Nil))));
        let b = Gc::new(Cons(10, Mutex::new(Gc::clone(&a))));
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
        sweep();

        // Values should still be the same
        assert_eq!(a.value(), Some(5));
        assert_eq!(b.value(), Some(10));

        // Should clean up all the memory at the end
        sweep();
    }
}
