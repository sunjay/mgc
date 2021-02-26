//! Allocation, deallocation, and heap traversal functions for memory managed by the GC.
//!
//! The garbage collector does not currently implement its own heap. We use the default allocator
//! provided by the standard library.
//!
//! NOTE: This implementation is crazy unsafe. It relies on the unstable layout of trait objects and
//! assumes that the data pointer of a trait object is the same as the pointer that would have been
//! returned from `Box::new`. This may completely break and explode in the future if those details
//! change.

use std::ptr::NonNull;
use std::alloc::Layout;
use std::fmt;
use std::error::Error;

mod private {
    pub trait Sealed {}
}

#[derive(Debug)]
pub struct AllocError(Layout);

impl AllocError {
    pub fn new(layout: Layout) -> Self {
        AllocError(layout)
    }

    pub fn into_inner(self) -> Layout {
        self.0
    }
}

impl fmt::Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Failed to allocate {} bytes with alignment {}", self.0.size(), self.0.align())
    }
}

impl Error for AllocError {}

/// The `Alloc` trait is an `unsafe` trait for a number of reasons, and implementors must ensure
/// that they adhere to these contracts:
///
/// * It's undefined behavior if allocators unwind. This restriction may be lifted in the future,
///   but currently a panic from any of these functions may lead to memory unsafety.
/// * Layout queries and calculations in general must be correct. Callers of this trait are allowed
///   to rely on the contracts defined on each method, and implementors must ensure such contracts
///   remain true.
pub unsafe trait Alloc: private::Sealed {
    /// Allocate memory as described by the given layout
    ///
    /// Returns a pointer to newly-allocated memory, or an error to indicate allocation failure.
    ///
    /// # Safety
    ///
    /// See: [`GlobalAlloc::alloc`](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html#tymethod.alloc)
    unsafe fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError>;

    /// Deallocate the block of memory at the given `ptr` pointer with the given layout
    ///
    /// # Safety
    ///
    /// See: [`GlobalAlloc::dealloc`](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html#tymethod.dealloc)
    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout);
}

#[derive(Default)]
pub struct GlobalAlloc {
    _private: (),
}

impl GlobalAlloc {
    pub(crate) const fn new() -> Self {
        Self {
            _private: (),
        }
    }
}

#[doc(hidden)]
impl private::Sealed for GlobalAlloc {}

unsafe impl Alloc for GlobalAlloc {
    unsafe fn alloc(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        NonNull::new(std::alloc::alloc(layout)).ok_or_else(|| AllocError(layout))
    }

    unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        std::alloc::dealloc(ptr.as_ptr(), layout)
    }
}
