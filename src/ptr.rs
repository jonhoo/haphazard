use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicBool, AtomicPtr};

pub struct HazPtr {
    pub(crate) ptr: AtomicPtr<u8>,
    pub(crate) next: AtomicPtr<HazPtr>,
    pub(crate) active: AtomicBool,
}

impl HazPtr {
    pub(crate) fn protect(&self, ptr: *mut u8) {
        self.ptr.store(ptr, Ordering::SeqCst);
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
