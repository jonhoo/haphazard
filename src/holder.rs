use crate::sync::atomic::AtomicPtr;
use crate::{Domain, HazPtrObject, HazPtrRecord};
use std::sync::atomic::Ordering;

pub struct HazardPointerArray<'domain, F, const N: usize> {
    domain: &'domain Domain<F>,
    records: [&'domain HazPtrRecord; N],
}

impl<'domain, F, const N: usize> HazardPointerArray<'domain, F, N> {
    pub unsafe fn protect<'l, 'o, T>(
        &'l mut self,
        mut sources: [&'_ AtomicPtr<T>; N],
    ) -> [Option<&'l T>; N]
    where
        T: HazPtrObject<'o, F>,
        'o: 'l,
        F: 'static,
    {
        let mut out = [None; N];

        for (i, (hazptr, src)) in self.records.iter_mut().zip(&mut sources).enumerate() {
            out[i] = unsafe { protect(&self.domain, hazptr, src) };
        }

        out
    }

    pub fn reset_protection(&mut self) {
        for hazptr in self.records {
            hazptr.reset();
        }
    }
}

impl<F, const N: usize> Drop for HazardPointerArray<'_, F, N> {
    fn drop(&mut self) {
        self.reset_protection();
        self.domain.release_many(self.records);
    }
}

pub struct HazardPointer<'domain, F> {
    hazard: &'domain HazPtrRecord,
    domain: &'domain Domain<F>,
}

impl HazardPointer<'static, crate::Global> {
    pub fn make_global() -> Self {
        HazardPointer::make_in_domain(Domain::global())
    }

    pub fn make_many_global<const N: usize>() -> HazardPointerArray<'static, crate::Global, N> {
        HazardPointer::make_many_in_domain(Domain::global())
    }
}

impl<'domain, F> HazardPointer<'domain, F> {
    pub fn make_in_domain(domain: &'domain Domain<F>) -> Self {
        Self {
            hazard: domain.acquire(),
            domain,
        }
    }

    pub fn make_many_in_domain<const N: usize>(
        domain: &'domain Domain<F>,
    ) -> HazardPointerArray<'domain, F, N> {
        let records = domain.acquire_many::<N>();

        HazardPointerArray { domain, records }
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in `AtomicPtr` is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the `AtomicPtr` will only be deallocated
    /// through calls to [`HazPtrObject::retire`] on the same [`Domain`] as this holder is
    /// associated with.
    pub unsafe fn protect<'l, 'o, T>(&'l mut self, src: &'_ AtomicPtr<T>) -> Option<&'l T>
    where
        T: HazPtrObject<'o, F>,
        'o: 'l,
        F: 'static,
    {
        unsafe { protect(&self.domain, &self.hazard, src) }
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in `AtomicPtr` is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the `AtomicPtr` will only be deallocated
    /// through calls to [`HazPtrObject::retire`] on the same [`Domain`] as this holder is
    /// associated with.
    unsafe fn try_protect<'l, 'o, T>(
        &'l mut self,
        ptr: *mut T,
        src: &'_ AtomicPtr<T>,
    ) -> Result<Option<&'l T>, *mut T>
    where
        T: HazPtrObject<'o, F>,
        'o: 'l,
        F: 'static,
    {
        unsafe { try_protect(&self.domain, &self.hazard, ptr, src) }
    }

    pub fn reset_protection(&mut self) {
        self.hazard.reset();
    }
}

///
/// # Safety
///
/// Caller must guarantee that the address in `AtomicPtr` is valid as a reference, or null.
/// Caller must also guarantee that the value behind the `AtomicPtr` will only be deallocated
/// through calls to [`HazPtrObject::retire`] on the same [`Domain`] as this holder is
/// associated with.
unsafe fn protect<'domain, 'l, 'o, F, T>(
    domain: &'l &'domain Domain<F>,
    hazard: &'l &'domain HazPtrRecord,
    src: &'_ AtomicPtr<T>,
) -> Option<&'l T>
where
    T: HazPtrObject<'o, F>,
    'o: 'l,
    F: 'static,
{
    let mut ptr = src.load(Ordering::Relaxed);
    loop {
        // Safety: same safety requirements as try_protect.
        match unsafe { try_protect(domain, hazard, ptr, src) } {
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
/// through calls to [`HazPtrObject::retire`] on the same [`Domain`] as this holder is
/// associated with.
unsafe fn try_protect<'domain, 'l, 'o, F, T>(
    domain: &'l &'domain Domain<F>,
    hazard: &'l &'domain HazPtrRecord,
    ptr: *mut T,
    src: &'_ AtomicPtr<T>,
) -> Result<Option<&'l T>, *mut T>
where
    T: HazPtrObject<'o, F>,
    'o: 'l,
    F: 'static,
{
    hazard.protect(ptr as *mut u8);

    crate::asymmetric_light_barrier();

    let ptr2 = src.load(Ordering::Acquire);
    if ptr != ptr2 {
        hazard.reset();
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
                *domain as *const Domain<F>,
                r.domain() as *const Domain<F>,
                "object guarded by different domain than holder used to access it"
            );
            r
        }))
    }
}

impl<F> Drop for HazardPointer<'_, F> {
    fn drop(&mut self) {
        self.hazard.reset();
        self.domain.release(self.hazard);
    }
}
