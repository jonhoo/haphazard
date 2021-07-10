use crate::{HazPtr, HazPtrDomain, HazPtrObject};
use std::sync::atomic::AtomicPtr;
use std::sync::atomic::Ordering;

pub struct HazPtrHolder<'domain, F> {
    hazard: Option<&'domain HazPtr>,
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
            hazard: None,
            domain,
        }
    }

    fn hazptr(&mut self) -> &'domain HazPtr {
        if let Some(hazptr) = self.hazard {
            hazptr
        } else {
            let hazptr = self.domain.acquire();
            self.hazard = Some(hazptr);
            hazptr
        }
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in `AtomicPtr` is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the `AtomicPtr` will only be deallocated
    /// through calls to [`HazPtrObject::retire`] on the same [`HazPtrDomain`] as this holder is
    /// associated with.
    pub unsafe fn load<'l, 'o, T>(&'l mut self, ptr: &'_ AtomicPtr<T>) -> Option<&'l T>
    where
        T: HazPtrObject<'o, F>,
        'o: 'l,
        F: 'static,
    {
        let hazptr = self.hazptr();
        let mut ptr1 = ptr.load(Ordering::SeqCst);
        loop {
            hazptr.protect(ptr1 as *mut u8);
            let ptr2 = ptr.load(Ordering::SeqCst);
            if ptr1 == ptr2 {
                // All good -- protected
                break std::ptr::NonNull::new(ptr1).map(|nn| {
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
                });
            } else {
                ptr1 = ptr2;
            }
        }
    }

    pub fn reset(&mut self) {
        if let Some(hazptr) = self.hazard {
            hazptr.ptr.store(std::ptr::null_mut(), Ordering::SeqCst);
        }
    }
}

impl<F> Drop for HazPtrHolder<'_, F> {
    fn drop(&mut self) {
        self.reset();

        // Return self.0 to domain if Some
        if let Some(hazptr) = self.hazard {
            hazptr.active.store(false, Ordering::SeqCst);
        }
    }
}
