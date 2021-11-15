pub trait Reclaim {}
impl<T> Reclaim for T {}

pub trait Deleter {
    /// # Safety
    /// `ptr` must have been allocated by the corresponding allocation method.
    /// delete must be called at most once for each `ptr`.
    unsafe fn delete(&self, ptr: *mut dyn Reclaim);
}

impl Deleter for unsafe fn(*mut (dyn Reclaim + 'static)) {
    unsafe fn delete(&self, ptr: *mut dyn Reclaim) {
        unsafe { (*self)(ptr) }
    }
}

pub mod deleters {
    use super::Reclaim;
    use alloc::boxed::Box;

    unsafe fn _drop_in_place(ptr: *mut dyn Reclaim) {
        // Safe by the contract on HazPtrObject::retire.
        unsafe { core::ptr::drop_in_place(ptr) };
    }

    /// Always safe to use given requirements on HazPtrObject::retire,
    /// but may lead to memory leaks if the pointer type itself needs drop.
    #[allow(non_upper_case_globals)]
    pub const drop_in_place: unsafe fn(*mut dyn Reclaim) = _drop_in_place;

    unsafe fn _drop_box(ptr: *mut dyn Reclaim) {
        // Safety: Safe by the safety gurantees of retire and because it's only used when
        // retiring Box objects.
        let _ = unsafe { Box::from_raw(ptr) };
    }

    /// # Safety
    ///
    /// Can only be used on values that were originally derived from a Box.
    #[allow(non_upper_case_globals)]
    pub const drop_box: unsafe fn(*mut dyn Reclaim) = _drop_box;
}
