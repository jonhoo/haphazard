use alloc::boxed::Box;

/// Trait for types that can be dropped (which is all of them).
///
/// This trait exists solely as a workaround for the fact that only types with an explicit `Drop`
/// implementation implement `Drop`, even though all types _can_ be dropped. We want to store
/// the equivalent of `Box<dyn Drop>` when objects are retired, but can't do that since not every
/// type is `Drop`. This trait is effectively the same as `Drop` (every trait implies `Drop`), and
/// has a blanket implementation for any type, so can be used instead of `dyn Drop`.
///
/// See also <https://github.com/rust-lang/rust/issues/86653> and
/// <https://github.com/rust-lang/rust/pull/86747>.
pub trait Reclaim {}
impl<T> Reclaim for T {}

/// A type that can be turned into, and converted from, a raw pointer whose referent is `T`.
///
/// # Safety
///
/// 1. the `*mut T` returned from `into_raw` must be valid as a `&mut T` when it is returned.
/// 2. the `*mut T` returned from `into_raw` must remain valid as a `&T` until it is passed to
///    `from_raw`.
/// 3. `from_raw` must not return a particular `*mut T` again until the provided `self` is dropped
///    after an eventual call to `from_raw`.
pub unsafe trait Pointer<T>
where
    Self: Sized + core::ops::Deref<Target = T>,
{
    /// Extract the raw pointer referenced by `self`.
    fn into_raw(self) -> *mut T;

    /// Reconstruct this pointer type from the given `ptr`.
    ///
    /// # Safety (for callers)
    ///
    /// 1. `ptr` must be a pointer returned by `Self::into_raw`
    /// 2. `ptr` must be valid to dereference to a `T`
    /// 3. `ptr` must not have been passed to `from_raw` since it was returned from `into_raw`
    /// 4. `ptr` must not be aliased
    #[allow(clippy::missing_safety_doc)]
    unsafe fn from_raw(ptr: *mut T) -> Self;
}

unsafe impl<T> Pointer<T> for Box<T> {
    fn into_raw(self) -> *mut T {
        Box::into_raw(self)
    }

    unsafe fn from_raw(ptr: *mut T) -> Self {
        // Safety: the safety requirements for Box::from_raw are the same as for Pointer::from_raw.
        unsafe { Box::from_raw(ptr) }
    }
}
