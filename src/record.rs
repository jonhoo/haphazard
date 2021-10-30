use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicBool, AtomicPtr};

pub(crate) struct HazPtrRecord {
    pub(crate) ptr: AtomicPtr<u8>,
    pub(crate) next: AtomicPtr<HazPtrRecord>,
    pub(crate) active: AtomicBool,
}

impl HazPtrRecord {
    pub(crate) fn reset(&self) {
        self.ptr.store(std::ptr::null_mut(), Ordering::Release);
    }

    pub(crate) fn protect(&self, ptr: *mut u8) {
        self.ptr.store(ptr, Ordering::Release);
    }

    pub(crate) fn release(&self) {
        self.active.store(false, Ordering::Release);
    }

    pub(crate) fn try_acquire(&self) -> bool {
        let active = self.active.load(Ordering::Acquire);
        !active
            && self
                .active
                .compare_exchange(active, true, Ordering::Release, Ordering::Relaxed)
                .is_ok()
    }
}
