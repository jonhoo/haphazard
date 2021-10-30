use crate::{HazPtr, HazPtrDomain, HazPtrObject};
use std::sync::atomic::AtomicPtr;
use std::sync::atomic::Ordering;

pub struct HazPtrHolder<'domain, F> {
    hazard: &'domain HazPtr,
    domain: &'domain HazPtrDomain<F>,
}

impl HazPtrHolder<'static, crate::Global> {
    pub fn global() -> Self {
        HazPtrHolder::for_domain(HazPtrDomain::global())
    }
}

impl<'domain, F> HazPtrHolder<'domain, F> {
    pub fn for_domain(domain: &'domain HazPtrDomain<F>) -> Self {
        Self {
            hazard: domain.acquire(),
            domain,
        }
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in `AtomicPtr` is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the `AtomicPtr` will only be deallocated
    /// through calls to [`HazPtrObject::retire`] on the same [`HazPtrDomain`] as this holder is
    /// associated with.
    pub unsafe fn protect<'l, 'o, T>(&'l mut self, src: &'_ AtomicPtr<T>) -> Option<&'l T>
    where
        T: HazPtrObject<'o, F>,
        'o: 'l,
        F: 'static,
    {
        let mut ptr = src.load(Ordering::Relaxed);
        loop {
            // Safety: same safety requirements as try_protect.
            match unsafe { self.try_protect(ptr, src) } {
                Ok(None) => break None,
                // Safety:
                // This is needed to workaround a bug in the borrow checker. See:
                // - https://github.com/rust-lang/rust/issues/51545
                // - https://github.com/rust-lang/rust/issues/54663
                // - https://github.com/rust-lang/rust/issues/58910
                // - https://github.com/rust-lang/rust/issues/84361
                Ok(Some(r)) => break Some(unsafe { &*(r as *const _) }),
                Err(ptr2) => {
                    ptr = ptr2;
                }
            }
        }
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in `AtomicPtr` is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the `AtomicPtr` will only be deallocated
    /// through calls to [`HazPtrObject::retire`] on the same [`HazPtrDomain`] as this holder is
    /// associated with.
    pub unsafe fn try_protect<'l, 'o, T>(
        &'l mut self,
        ptr: *mut T,
        src: &'_ AtomicPtr<T>,
    ) -> Result<Option<&'l T>, *mut T>
    where
        T: HazPtrObject<'o, F>,
        'o: 'l,
        F: 'static,
    {
        self.hazard.protect(ptr as *mut u8);

        crate::asymmetric_light_barrier();

        let ptr2 = src.load(Ordering::Acquire);
        if ptr != ptr2 {
            self.hazard.reset();
            Err(ptr2)
        } else {
            // All good -- protected
            Ok(std::ptr::NonNull::new(ptr).map(|nn| {
                // Safety: this is safe because:
                //
                //  1. Target of ptr1 will not be deallocated for the returned lifetime since
                //     our hazard pointer is active and pointing at ptr1.
                //  2. Pointer address is valid by the safety contract of load.
                let r = unsafe { nn.as_ref() };
                debug_assert_eq!(
                    self.domain as *const HazPtrDomain<F>,
                    r.domain() as *const HazPtrDomain<F>,
                    "object guarded by different domain than holder used to access it"
                );
                r
            }))
        }
    }

    pub fn reset(&mut self) {
        self.hazard.reset();
    }
}

impl<F> Drop for HazPtrHolder<'_, F> {
    fn drop(&mut self) {
        self.hazard.reset();
        self.domain.release(self.hazard);
    }
}
