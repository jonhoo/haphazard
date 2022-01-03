use crate::sync::atomic::AtomicPtr;
use crate::{Domain, HazPtrObject, HazPtrRecord};
use core::mem::{ManuallyDrop, MaybeUninit};
use core::sync::atomic::Ordering;

pub struct HazardPointerArray<'domain, F, const N: usize> {
    // ManuallyDrop is required to prevent the HazardPointer from reclaiming itself, since
    // HazardPointerArray has it's own drop implementation with an optimized reclaim for all hazard
    // pointers
    haz_ptrs: [ManuallyDrop<HazardPointer<'domain, F>>; N],
}

impl<'domain, F, const N: usize> HazardPointerArray<'domain, F, N> {
    pub fn hazard_pointers<'array>(&'array mut self) -> [&'array mut HazardPointer<'domain, F>; N] {
        // replace with `self.haz_ptrs.each_mut().map(|v| &mut **v)` when each_mut stabilizes

        let mut out: [MaybeUninit<&'array mut HazardPointer<'domain, F>>; N] =
            [(); N].map(|_| MaybeUninit::uninit());

        for (i, hazptr) in self.haz_ptrs.iter_mut().enumerate() {
            out[i].write(hazptr);
        }

        //
        // # Safety
        //
        // We have initialized every element of the array with our for loop above
        out.map(|maybe_uninit| unsafe { maybe_uninit.assume_init() })
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in `AtomicPtr` is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the `AtomicPtr` will only be deallocated
    /// through calls to [`HazPtrObject::retire`] on the same [`Domain`] as this holder is
    /// associated with.
    pub unsafe fn protect_all<'l, 'o, T>(
        &'l mut self,
        mut sources: [&'_ AtomicPtr<T>; N],
    ) -> [Option<&'l T>; N]
    where
        T: HazPtrObject<'o, F>,
        'o: 'l,
        F: 'static,
    {
        let mut out = [None; N];

        for (i, (hazptr, src)) in self.haz_ptrs.iter_mut().zip(&mut sources).enumerate() {
            out[i] = unsafe { hazptr.protect(src) };
        }

        out
    }

    pub fn reset_protection(&mut self) {
        for hazptr in self.haz_ptrs.iter_mut() {
            hazptr.reset_protection();
        }
    }
}

impl<'domain, F, const N: usize> Drop for HazardPointerArray<'domain, F, N> {
    fn drop(&mut self) {
        self.reset_protection();
        let domain = self.haz_ptrs[0].domain;
        // replace with `self.haz_ptrs.each_ref().map(|v| v.hazard)` when each_ref stabilizes
        let records = self.hazard_pointers().map(|hazptr| hazptr.hazard);
        domain.release_many(records);
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
        let haz_ptrs = domain
            .acquire_many::<N>()
            .map(|hazard| ManuallyDrop::new(HazardPointer { hazard, domain }));

        HazardPointerArray { haz_ptrs }
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
    /// through calls to [`HazPtrObject::retire`] on the same [`Domain`] as this holder is
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
            Ok(core::ptr::NonNull::new(ptr).map(|nn| {
                // Safety: this is safe because:
                //
                //  1. Target of ptr1 will not be deallocated for the returned lifetime since
                //     our hazard pointer is active and pointing at ptr1.
                //  2. Pointer address is valid by the safety contract of load.
                let r = unsafe { nn.as_ref() };
                debug_assert_eq!(
                    self.domain as *const Domain<F>,
                    r.domain() as *const Domain<F>,
                    "object guarded by different domain than holder used to access it"
                );
                r
            }))
        }
    }

    pub fn reset_protection(&mut self) {
        self.hazard.reset();
    }
}

impl<F> Drop for HazardPointer<'_, F> {
    fn drop(&mut self) {
        self.hazard.reset();
        self.domain.release(self.hazard);
    }
}
