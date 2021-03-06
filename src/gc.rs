use crate::trace::*;

use std::fmt;
#[cfg(feature = "global")]
use std::iter;
use std::ptr::NonNull;
use std::ops::Deref;

#[cfg(feature = "global")]
use super::{GLOBAL_GC, GcAlloc};

/// Mark the given GC allocated value as still reachable. This will result in the allocation NOT
/// being collected during the next sweep. Any allocation that is not marked will be freed.
///
/// Returns true if the value was already marked previously.
///
/// # Safety
///
/// This function should not be called concurrently with `sweep`.
fn mark<T: ?Sized>(value: &Gc<T>) -> bool {
    // Safety: All Gc<T> values are allocated by `alloc` so this pointer should be valid
    unsafe { super::mark(value.ptr) }
}

/// A cloneable pointer into memory managed by the GC
///
/// The value will be freed at some point after the pointer is no longer being used
///
/// # Safety
///
/// Note that this value is only safe to use as long as the GC has not collected it. It is
/// unfortunately not possible to statically guarantee that this has not occurred. The user of this
/// type needs to ensure that the GC is always aware that this value is still being used.
pub struct Gc<T: ?Sized> {
    ptr: NonNull<T>,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Gc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Gc<T> {}

#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl<T: Trace> Gc<T> {
    /// Allocates memory managed by the GC and initializes it with the given value
    #[inline]
    pub fn new(value: T) -> Self {
        GLOBAL_GC.alloc(value)
    }
}

impl<T: ?Sized> Gc<T> {
    /// Returns `true` if the two `Gc` values point to the same allocation
    /// (in a vein similar to [`ptr::eq`]).
    ///
    /// [`ptr::eq`]: core::ptr::eq
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr.as_ptr() == other.ptr.as_ptr()
    }

    /// Consumes the `Gc`, returning the wrapped pointer
    ///
    /// To avoid a memory leak, the pointer must be converted back into a `Gc` using `Gc::from_raw`.
    pub fn into_raw(this: Self) -> NonNull<T> {
        this.ptr
    }

    /// Constructs an `Gc` from a raw pointer
    ///
    /// # Safety
    ///
    /// The raw pointer must have been previously returned by a call to `Gc<U>::into_raw` where `U`
    /// must have the same size and alignment as `T`. This is trivially true if `U` is `T`. Note
    /// that if `U` is not `T` but has the same size and alignment, this is basically like
    /// transmuting references of different types. See `mem::transmute` for more information on what
    /// restrictions apply in this case.
    ///
    /// The user of `from_raw` has to make sure a specific value of `T` is only dropped once.
    ///
    /// This function is unsafe because improper use may lead to memory unsafety, even if the
    /// returned `Gc<T>` is never accessed.
    pub unsafe fn from_raw(ptr: NonNull<T>) -> Self {
        Self {ptr}
    }
}

#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl<T: Trace> iter::FromIterator<T> for Gc<[T]> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Self {
        let items: Vec<T> = Vec::from_iter(iter);
        items.into()
    }
}

#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl<T: Trace> From<T> for Gc<T> {
    fn from(value: T) -> Self {
        GLOBAL_GC.alloc(value)
    }
}

#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl<'a, T: Trace + Clone> From<&'a [T]> for Gc<[T]> {
    #[inline]
    fn from(slice: &'a [T]) -> Self {
        GLOBAL_GC.alloc(slice)
    }
}

#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl<T: Trace> From<Vec<T>> for Gc<[T]> {
    #[inline]
    fn from(items: Vec<T>) -> Self {
        GLOBAL_GC.alloc(items)
    }
}

// This code is pretty much the same as the impl for Arc<str>
#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl From<&str> for Gc<str> {
    #[inline]
    fn from(value: &str) -> Self {
        GLOBAL_GC.alloc(value)
    }
}

// This code is pretty much the same as the impl for Arc<str>
#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl From<String> for Gc<str> {
    #[inline]
    fn from(value: String) -> Self {
        GLOBAL_GC.alloc(value)
    }
}

#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl From<&std::sync::Arc<str>> for Gc<str> {
    #[inline]
    fn from(value: &std::sync::Arc<str>) -> Self {
        GLOBAL_GC.alloc(value)
    }
}

#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
impl From<std::sync::Arc<str>> for Gc<str> {
    #[inline]
    fn from(value: std::sync::Arc<str>) -> Self {
        GLOBAL_GC.alloc(value)
    }
}

impl<T: ?Sized + Trace> Trace for Gc<T> {
    fn trace(&self) {
        // Avoid reference cycles by only tracing values that weren't previously marked
        if !mark(self) {
            (**self).trace();
        }
    }
}

impl<T: ?Sized> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety: The garbage collector should not collect a pointer while it still exists
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: ?Sized> Clone for Gc<T> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
        }
    }
}

#[cfg(feature = "global")]
impl<T: Trace + Default> Default for Gc<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized> fmt::Pointer for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.ptr, f)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Gc<T> {
    fn eq(&self, other: &Self) -> bool {
        Self::ptr_eq(self, other) || (**self).eq(&**other)
    }
}

impl<T: ?Sized + Eq> Eq for Gc<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for Gc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + Ord> Ord for Gc<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + std::borrow::Borrow<T>> std::borrow::Borrow<T> for Gc<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> AsRef<T> for Gc<T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> Unpin for Gc<T> {}

impl<T: ?Sized + std::hash::Hash> std::hash::Hash for Gc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}
