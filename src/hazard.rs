use crate::sync::atomic::AtomicPtr;
use crate::{record::HazPtrRecord, Domain};
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::NonNull;
use core::sync::atomic::Ordering;

#[cfg(doc)]
use crate::*;

/// A type that can protect a referenced object from reclamation.
///
/// Protects up to a single address from concurrent reclamation in the referenced [`Domain`].
///
/// A hazard pointer does nothing when initially constructed. You need to load the pointer stored
/// by an [`std::sync::atomic::AtomicPtr`](AtomicPtr) through it with [`HazardPointer::protect`] in
/// order for it to protect an object. That protection is tied to the exclusive (`&mut`) borrow of
/// the `HazardPointer` that `protect` takes; the moment the exclusive borrow ends (such as when
/// the `HazardPointer` is dropped), the protection ends.
///
/// Note that a hazard pointer can only protect an object if any call to `retire` for said object
/// happens in the same domain as the one the hazard pointer was created in. The generic argument
/// `F` is a _domain family_, which helps enforce that statically. Families are discussed in the
/// documentation for [`Domain`]. `F` defaults to the [global domain](Global).
///
/// If you want a (slightly) higher-level interface, use [`AtomicPtr`].
///
/// If you need to protect multiple referenced objects at the same time, use
/// [`HazardPointerArray`].
pub struct HazardPointer<'domain, F = crate::Global> {
    hazard: &'domain HazPtrRecord,
    pub(crate) domain: &'domain Domain<F>,
}

impl Default for HazardPointer<'static, crate::Global> {
    fn default() -> Self {
        Self::new()
    }
}

impl HazardPointer<'static, crate::Global> {
    /// Create a new hazard pointer in the [global domain](Global).
    pub fn new() -> Self {
        HazardPointer::new_in_domain(Domain::global())
    }

    /// Create a new hazard pointer array in the [global domain](Global).
    pub fn many<const N: usize>() -> HazardPointerArray<'static, crate::Global, N> {
        HazardPointer::many_in_domain(Domain::global())
    }
}

impl<'domain, F> HazardPointer<'domain, F> {
    /// Create a new hazard pointer in the given domain.
    pub fn new_in_domain(domain: &'domain Domain<F>) -> Self {
        Self {
            hazard: domain.acquire(),
            domain,
        }
    }

    /// Create a new hazard pointer array in the given domain.
    pub fn many_in_domain<const N: usize>(
        domain: &'domain Domain<F>,
    ) -> HazardPointerArray<'domain, F, N> {
        let haz_ptrs = domain
            .acquire_many::<N>()
            .map(|hazard| ManuallyDrop::new(HazardPointer { hazard, domain }));

        HazardPointerArray { haz_ptrs }
    }

    /// Protect the value loaded from the given [`AtomicPtr`], and dereference it to `&T`.
    ///
    /// This operation will load the [`AtomicPtr`] multiple times:
    ///
    /// 1. load to get the currently stored pointer, `ptr`
    /// 2. store `ptr` into the hazard pointer to protect it from reclamation
    /// 3. load again to check that the pointer didn't change between 1 and 2.
    ///    if it did, set the loaded value to `ptr` and goto 2.
    ///
    /// Returns `None` if the loaded pointer is null.
    ///
    /// `T` must be `Sync` since we do not know which thread stored the pointer in the first place.
    ///
    /// # Safety
    ///
    /// 1. The value loaded from `AtomicPtr` is a valid `&T`, or null.
    /// 2. The loaded `&T` will only be deallocated through calls to `retire` functions on the same
    ///    [`Domain`] as this holder is associated with.
    pub unsafe fn protect<'l, T>(&'l mut self, src: &'_ AtomicPtr<T>) -> Option<&'l T>
    where
        T: Sync,
        F: 'static,
    {
        // NOTE: The type ascription here ensures that `protect_ptr` indeed returns a lifetime of
        // `'l` as we expect. It is a no-op, but will catch cases where `protect_ptr` changes in
        // the future.
        let (ptr, _proof): (_, PhantomData<&'l T>) = self.protect_ptr(src)?;
        Some(unsafe { ptr.as_ref() })
    }

    /// Protect the value loaded from the given [`AtomicPtr`], and return it as `NonNull<T>`.
    ///
    /// This operation will load the [`AtomicPtr`] multiple times:
    ///
    /// 1. load to get the currently stored pointer, `ptr`
    /// 2. store `ptr` into the hazard pointer to protect it from reclamation
    /// 3. load again to check that the pointer didn't change between 1 and 2.
    ///    if it did, set the loaded value to `ptr` and goto 2.
    ///
    /// Note that protecting a given pointer only has an effect if any thread that may drop the
    /// pointer does so through the same [`Domain`] as this hazard pointer is associated with.
    ///
    /// Returns `None` if the loaded pointer is null.
    pub fn protect_ptr<'l, T>(
        &'l mut self,
        src: &'_ AtomicPtr<T>,
    ) -> Option<(NonNull<T>, PhantomData<&'l T>)>
    where
        F: 'static,
    {
        let mut ptr = src.load(Ordering::Relaxed);
        loop {
            // Safety: same safety requirements as try_protect.
            match self.try_protect_ptr(ptr, src) {
                Ok(None) => break None,
                Ok(Some((ptr, _h))) => {
                    // XXX: We would _like_ to write
                    //
                    //     let _: PhantomData<&'l T> = _h;
                    //
                    // or better yet return _h in the tuple below rather than a fresh PhantomData,
                    // just as a sanity-check that we didn't mess up the lifetime bounds between
                    // try and non-try. Unfortunately, that runs us into a known bug in the borrow
                    // checker. See:
                    //
                    // - https://github.com/rust-lang/rust/issues/51545
                    // - https://github.com/rust-lang/rust/issues/54663
                    // - https://github.com/rust-lang/rust/issues/58910
                    // - https://github.com/rust-lang/rust/issues/84361
                    break Some((ptr, PhantomData));
                }
                Err(ptr2) => {
                    ptr = ptr2;
                }
            }
        }
    }

    /// Protect `ptr` and dereference it to `&T` if it's safe to do so.
    ///
    /// Unlike [`HazardPointer::protect`], this operation will _not_ load the [`AtomicPtr`]
    /// multiple times. It will only perform a single load to check that the stored pointer does
    /// not change before we have a chance to protect `ptr`.
    ///
    /// If the value has changed, the new pointer is returned wrapped in `Err`.
    ///
    /// `T` must be `Sync` since we do not know which thread stored the pointer in the first place.
    ///
    /// Returns `Ok(None)` if `ptr.is_null()`.
    ///
    /// # Safety
    ///
    /// 1. The value loaded from `AtomicPtr` is a valid `&T`, or null.
    /// 2. The loaded `&T` will only be deallocated through calls to `retire` functions on the same
    ///    [`Domain`] as this holder is associated with.
    pub unsafe fn try_protect<'l, T>(
        &'l mut self,
        ptr: *mut T,
        src: &'_ AtomicPtr<T>,
    ) -> Result<Option<&'l T>, *mut T>
    where
        T: Sync,
        F: 'static,
    {
        if ptr.is_null() {
            return Ok(None);
        }
        let ptr: Option<(_, PhantomData<&'l T>)> = self.try_protect_ptr(ptr, src)?;
        let (ptr, _) = ptr.expect("ptr was not null, but try_protect_ptr returned null");
        // Safety:
        //
        //  1. Target of ptr1 will not be deallocated for the returned lifetime since
        //     our hazard pointer is active and pointing at ptr1, and by safety requirement #2
        //     `ptr1` will only ever be reclaimed through `retire` of the appropriate domain.
        //  2. Pointer address is valid by the safety contract of try_protect.
        Ok(Some(unsafe { ptr.as_ref() }))
    }

    /// Protect `ptr` and dereference it to `NonNull<T>` if it's safe to do so.
    ///
    /// Unlike [`HazardPointer::protect_ptr`], this operation will _not_ load the [`AtomicPtr`]
    /// multiple times. It will only perform a single load to check that the stored pointer does
    /// not change before we have a chance to protect `ptr`.
    ///
    /// Note that protecting a given pointer only has an effect if any thread that may drop the
    /// pointer does so through the same [`Domain`] as this hazard pointer is associated with.
    ///
    /// If the value has changed, the new pointer is returned wrapped in `Err`.
    ///
    /// Returns `Ok(None)` if `ptr.is_null()`.
    #[allow(clippy::type_complexity)]
    pub fn try_protect_ptr<'l, T>(
        &'l mut self,
        ptr: *mut T,
        src: &'_ AtomicPtr<T>,
    ) -> Result<Option<(NonNull<T>, PhantomData<&'l T>)>, *mut T>
    where
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
            Ok(core::ptr::NonNull::new(ptr).map(|ptr| (ptr, PhantomData)))
        }
    }

    /// Release the protection awarded by this hazard pointer, if any.
    ///
    /// If the hazard pointer was protecting an object, that object may now be reclaimed when
    /// retired (assuming it isn't protected by any _other_ hazard pointers).
    pub fn reset_protection(&mut self) {
        self.hazard.reset();
    }

    /// Protect the given address.
    ///
    /// You will very rarely want to use this method, and should prefer the other protection
    /// methods instead, as they guard against races between when the value of a shared pointer was
    /// read and any changes to the shared pointer address.
    ///
    /// Note that protecting a given pointer only has an effect if any thread that may drop the
    /// pointer does so through the same [`Domain`] as this hazard pointer is associated with.
    ///
    /// It's important to note that this function solely writes the pointer value to the hazard
    /// pointer slot. However, this protection alone does not guarantee safety during dereferencing
    /// due to two key reasons:
    ///
    /// 1. The announcement made by the hazard pointer might not be immediately visible to
    ///    reclaiming threads, especially in a weak memory model.
    /// 2. Concurrent threads could already have retired the pointer before the protection.
    ///
    /// To ensure safety, users need to appropriately synchronize the write operation on a hazard
    /// slot and validate that the pointer hasn't already been retired. For synchronization, the
    /// library offers an [`asymmetric_light_barrier`] function. It enables reclaiming threads
    /// to acknowledge the preceding protection.
    /// 
    /// Manual pointer protection and validation involve the following steps:
    ///
    /// 1. Acquire a pointer `p`, and manually protect it with a [`HazardPointer`] by calling
    ///    [`HazardPointer::protect_raw`].
    /// 2. Issue a memory barrier with [`asymmetric_light_barrier`] to enable reclaiming threads
    ///    to recognize the preceding protection.
    /// 3. Validate whether `p` is retired. If `p` remains guaranteed as not retired, it is safe
    ///    for dereferencing. Otherwise, revisit step 1 and retry.
    ///
    /// The strategy to validate whether `p` is retired would depend on the semantics of
    /// the data structures or algorithms. For example, in Harris-Michael linked lists, validation
    /// can be done by reloading the pointer from the [`AtomicPtr`] and ensuring that the its
    /// value has not change. This stratege works because unlinking the node from its predecessor
    /// strictly *happens before* the retirement of that node under the data structure's semantics.
    ///
    /// # Example
    ///
    /// ```
    /// use haphazard::{AtomicPtr, HazardPointer, asymmetric_light_barrier};
    ///
    /// struct Node {
    ///     value: usize,
    ///     next: AtomicPtr<Self>,
    /// }
    ///
    /// // Let's imagine a data structure which has the following properties.
    /// //
    /// // 1. It always has exactly two nodes.
    /// // 2. A thread may change its contents by exchanging the `head` pointer with an another
    /// //    chain consisted of two nodes.
    /// // 3. After a successful `compare_exchange`, the thread retires popped nodes without
    /// //    unlinking the first and the second node.
    /// //
    /// // Note that the link between the first and the second node won't be changed
    /// // before the retirement! For this reason, to validate the protection of the second node,
    /// // one must reload the head pointer and confirm that it has not changed.
    /// let head =
    ///     AtomicPtr::from(Box::new(Node {
    ///         value: 0,
    ///         next: AtomicPtr::from(Box::new(Node {
    ///             value: 1,
    ///             next: unsafe { AtomicPtr::new(std::ptr::null_mut()) },
    ///         })),
    ///     }));
    ///
    /// let mut hp1 = HazardPointer::default();
    /// let mut hp2 = HazardPointer::default();
    /// 
    /// let (n1, n2) = loop {
    ///     // The first node can be loaded in a conventional way.
    ///     let n1 = head.safe_load(&mut hp1).expect("The first node must exist");
    ///
    ///     // However, the second one cannot, because of the aforementioned reasons.
    ///     let ptr = n1.next.load_ptr();
    ///     // 1. Announce a hazard pointer manually.
    ///     hp2.protect_raw(ptr);
    ///
    ///     // 2. Synchronize with reclaimers.
    ///     asymmetric_light_barrier();
    ///
    ///     // 3. Validate the second protection by reloading the head pointer.
    ///     if n1 as *const _ == head.load_ptr().cast_const() {
    ///         // If the link to the head node has not changed,
    ///         // it is guaranteed that the second node is not retired yet.
    ///
    ///         // Safety: `ptr` is properly protected by `hp2`.
    ///         let n2 = unsafe { &*ptr };
    ///         break (n1, n2);
    ///     }
    ///
    /// };
    ///
    /// // Here, `n1` and `n2` is safe for dereferencing.
    /// ```
    pub fn protect_raw<T>(&mut self, ptr: *mut T)
    where
        F: 'static,
    {
        self.hazard.protect(ptr as *mut u8);
    }
}

impl<F> Drop for HazardPointer<'_, F> {
    fn drop(&mut self) {
        self.hazard.reset();
        self.domain.release(self.hazard);
    }
}

/// An efficient way to obtain and hold `N` [`HazardPointer`]s.
///
/// Construct one either with
///
/// ```
/// # use haphazard::HazardPointerArray;
/// let _: HazardPointerArray<haphazard::Global, 4> = HazardPointerArray::default();
/// ```
///
/// or using [`HazardPointer::many`]/[`HazardPointer::many_in_domain`]:
///
/// ```
/// # use haphazard::{HazardPointer, HazardPointerArray};
/// let _ = HazardPointer::many::<4>();
/// let _ = HazardPointer::many_in_domain::<4>(haphazard::Domain::global());
/// ```
///
/// To use the individual hazard pointers, use [`HazardPointerArray::as_refs`], or protect multiple
/// [`AtomicPtr`]s using [`HazardPointerArray::protect_all`].
pub struct HazardPointerArray<'domain, F, const N: usize> {
    // ManuallyDrop is required to prevent the HazardPointer from reclaiming itself, since
    // HazardPointerArray has it's own drop implementation with an optimized reclaim for all hazard
    // pointers
    haz_ptrs: [ManuallyDrop<HazardPointer<'domain, F>>; N],
}

impl<const N: usize> Default for HazardPointerArray<'static, crate::Global, N> {
    fn default() -> Self {
        HazardPointer::many::<N>()
    }
}

impl<'domain, F, const N: usize> HazardPointerArray<'domain, F, N> {
    /// Reference the `N` allocated [`HazardPointer`]s.
    ///
    /// If you're curious why you can't just slice directly into `HazardPointerArray`, it's because
    /// doing so would mutable borrow the _entire_ array, which would make the _other_ pointers
    /// unusable. The borrow checker knows that individual elements in a `[_; N]` are distinct, and
    /// can be borrowed individually, but does not know that that is the case for `SomeType[i]`.
    pub fn as_refs<'array>(&'array mut self) -> [&'array mut HazardPointer<'domain, F>; N] {
        // TODO: replace with `self.haz_ptrs.each_mut().map(|v| &mut **v)` when each_mut stabilizes

        let mut out: [MaybeUninit<&'array mut HazardPointer<'domain, F>>; N] =
            [(); N].map(|_| MaybeUninit::uninit());

        for (i, hazptr) in self.haz_ptrs.iter_mut().enumerate() {
            out[i].write(hazptr);
        }

        // Safety: we have initialized every element of the array with our for loop above
        out.map(|maybe_uninit| unsafe { maybe_uninit.assume_init() })
    }

    /// Protect the value loaded from each [`AtomicPtr`], and dereference each one to `&T`.
    ///
    /// The order of the returned references matches the order of `sources`.
    ///
    /// This operation will load each [`AtomicPtr`] multiple times:
    ///
    /// 1. load to get the currently stored pointer, `ptr`
    /// 2. store `ptr` into the hazard pointer to protect it from reclamation
    /// 3. load again to check that the pointer didn't change between 1 and 2.
    ///    if it did, set the loaded value to `ptr` and goto 2.
    ///
    /// Produces `None` at a given index if the loaded pointer for that `AtomicPtr` was null.
    ///
    /// # Safety
    ///
    /// 1. The values loaded each `AtomicPtr` are all valid `&T`, or null.
    /// 2. The loaded `&T` will only be deallocated through calls to `retire` functions on the same
    ///    [`Domain`] as this holder is associated with.
    pub unsafe fn protect_all<'l, T>(
        &'l mut self,
        mut sources: [&'_ AtomicPtr<T>; N],
    ) -> [Option<&'l T>; N]
    where
        T: Sync,
        F: 'static,
    {
        let mut out = [None; N];

        for (i, (hazptr, src)) in self.haz_ptrs.iter_mut().zip(&mut sources).enumerate() {
            // Safety: our safety requirements imply the safety requirements for protect for each
            // index.
            out[i] = unsafe { hazptr.protect(src) };
        }

        out
    }

    /// Release the protection awarded by the contained hazard pointers, if any.
    ///
    /// If the hazard pointer array was protecting any objects, those objects may now be reclaimed
    /// when retired (assuming they aren't protected by any _other_ hazard pointers).
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
        let records = self.as_refs().map(|hazptr| hazptr.hazard);
        domain.release_many(records);
    }
}
