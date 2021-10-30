use std::sync::atomic::AtomicPtr;
use std::sync::atomic::Ordering;

pub(crate) struct HazPtrRecord {
    pub(crate) ptr: AtomicPtr<u8>,
    pub(crate) next: AtomicPtr<HazPtrRecord>,
    pub(crate) available_next: AtomicPtr<HazPtrRecord>,
}

impl HazPtrRecord {
    pub(crate) fn reset(&self) {
        self.ptr.store(std::ptr::null_mut(), Ordering::Release);
    }

    pub(crate) fn protect(&self, ptr: *mut u8) {
        self.ptr.store(ptr, Ordering::Release);
    }
}
