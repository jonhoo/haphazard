use crate::raw::{Pointer, Reclaim};
use crate::record::HazPtrRecord;
use crate::sync::atomic::{AtomicIsize, AtomicPtr, AtomicUsize};
use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use core::marker::PhantomData;
use core::sync::atomic::Ordering;

// Like folly's implementation, we use a time a based check to run reclamation about every
// `SYNC_TIME_PERIOD` nanoseconds. The next time we should run reclamation is stored in
// `due_time` inside `Domain`. On `no_std` we don't (yet) have access to time so this feature is
// disabled. Also on platforms with < 64 bits, we can only store 2^32 nanoseconds -> ~4 seconds or
// less, so this feature is also disabled. Additionally, loom can't support time for reasons of
// determinism.

#[cfg(all(feature = "std", target_pointer_width = "64", not(loom)))]
const SYNC_TIME_PERIOD: u64 = std::time::Duration::from_nanos(2000000000).as_nanos() as u64;
#[cfg(all(feature = "std", target_pointer_width = "64", not(loom)))]
use crate::sync::atomic::AtomicU64;

#[cfg(loom)]
const RCOUNT_THRESHOLD: isize = 5;
#[cfg(not(loom))]
const RCOUNT_THRESHOLD: isize = 1000;
const HCOUNT_MULTIPLIER: isize = 2;
#[cfg(loom)]
const NUM_SHARDS: usize = 2;
#[cfg(not(loom))]
const NUM_SHARDS: usize = 8;
const IGNORED_LOW_BITS: u8 = 8;
const SHARD_MASK: usize = NUM_SHARDS - 1;
const LOCK_BIT: usize = 1;

/// The singleton [domain family](Domain) for the global domain.
///
/// The global domain is a convenient way to amortize the overhead of memory reclamation across
/// an entire program. Rather than being tied to any given [`Domain`] instance, all users of the
/// global domain share a responsibility to reclaim retired objects, and are able to re-use each
/// others' hazard pointers.
///
/// You can get a handle to the single global domain using [`Domain::global`].
#[non_exhaustive]
pub struct Global;
impl Global {
    const fn new() -> Self {
        Global
    }
}

/// Mark a [domain family](Domain) that unique caracterize a [domain instance](Domain)
///
/// See [`Global`] and [`unique_domain`]
///
/// # Safety
///
/// Implementors of this trait must guarantee only one Domain of that family can be contructed.
pub unsafe trait Singleton {}

// Safety: we can guarantee that there's only ever one Domain<Global> because Global itself is not
// possible to construct outside of this crate (due to #[non_exhaustive] + no public constructor),
// and we only ever construct one Domain from it internally in the form of a single static.
unsafe impl Singleton for Global {}

#[cfg(not(loom))]
static SHARED_DOMAIN: Domain<Global> = Domain::new(&Global::new());

#[cfg(loom)]
loom::lazy_static! {
    static ref SHARED_DOMAIN: Domain<Global> = Domain::new(&Global::new());
    static ref SHARD: loom::sync::atomic::AtomicUsize = loom::sync::atomic::AtomicUsize::new(0);
}

// Make AtomicPtr usable with loom API.
trait WithMut<T> {
    fn with_mut<R>(&mut self, f: impl FnOnce(&mut *mut T) -> R) -> R;
}
impl<T> WithMut<T> for core::sync::atomic::AtomicPtr<T> {
    fn with_mut<R>(&mut self, f: impl FnOnce(&mut *mut T) -> R) -> R {
        f(self.get_mut())
    }
}

/// Synchronization point between hazard pointers and the writers they guard against.
///
/// Every [hazard pointer](crate::HazardPointer) is associated with a domain, and can only guard
/// against reclamation of objects that are retired through that same domain. In other words, you
/// should always ensure that your code uses the same domain to retire objects as it uses to make
/// hazard pointers to read those objects. If it does not, the hazard pointers will provide no
/// meaningful protection. This connection is part of the safety contract for
/// [`HazardPointer::load`](HazardPointer::load).
///
/// ## Domain families
///
/// To help aid in determining that the same domain is used for loads and stores, every domain has
/// an associated _domain family_ (`F`). The family serves no purpose beyond adding a statically
/// checked guide so that obviously-incompatible domains aren't used. To take advantage of it, your
/// code should define a new zero-sized type that you use every `F` appears, like so:
///
/// ```rust
/// #[non_exhaustive]
/// struct Family;
///
/// type Domain = haphazard::Domain<Family>;
/// type HazardPointer<'domain> = haphazard::HazardPointer<'domain, Family>;
/// type AtomicPtr<T> = haphazard::AtomicPtr<T, Family>;
/// ```
///
/// This ensures at compile-time that you don't, for example, use a
/// [`HazardPointer`](crate::HazardPointer) from the [global domain](Global) to guard loads from an
/// [`AtomicPtr`](crate::AtomicPtr) that is tied to a custom domain.
///
/// This isn't bullet-proof though! Nothing prevents you from using hazard pointers allocated from
/// one instance of `Domain<Family>` with an atomic pointer whose writers use a different
/// _instance_ of `Domin<Family>`. So be careful!
///
/// The [`unique_domain`] macro provides a mechanism for constructing a domain with a unique
/// domain family that cannot be confused with any other. If you can use it, you should do so, as
/// it gives stronger static guarantees. However, it has the downside that you cannot name the
/// return type (at least without [impl Trait in type
/// aliases](https://github.com/rust-lang/rust/issues/63063)), which makes it difficult to store in
/// other types.
///
/// ## Reclamation
///
/// Domains are the coordination mechanism used for reclamation. When an object is retired into a
/// domain, the retiring thread will (sometimes) scan the domain for objects that are now safe to
/// reclaim (i.e., drop). Objects that cannot yet be reclaimed because there are active readers are
/// left in the domain for a later retire to check again. This means that there is generally a
/// delay between when an object is retired (i.e., marked as deleted) and when it is actually
/// reclaimed (i.e., [`drop`](core::mem::drop) is called). And if there are no more retires, the
/// objects may not be reclaimed until the owning domain is itself dropped.
///
/// When using the [global domain](Global) to guard data access in your data structure, keep in
/// mind that there is no guarantee that retired objects will be cleaned up by the time your data
/// structure is dropped. As a result, you may need to require that the data you store in said data
/// structure be `'static`. If you wish to avoid that bound, you'll need to construct your own
/// `Domain` for each instance of your data structure so that all the guarded data is reclaimed
/// when your data structure is dropped.
#[non_exhaustive]
pub struct Domain<F> {
    hazptrs: HazPtrRecords,
    untagged: [RetiredList; NUM_SHARDS],
    family: PhantomData<F>,
    #[cfg(all(feature = "std", target_pointer_width = "64", not(loom)))]
    due_time: AtomicU64,
    nbulk_reclaims: AtomicUsize,
    count: AtomicIsize,
    shutdown: bool,
}

#[cfg(miri)]
extern "Rust" {
    fn miri_static_root(ptr: *const u8);
}

impl Domain<Global> {
    /// Get a handle to the singleton [global domain](Global).
    pub fn global() -> &'static Self {
        #[cfg(miri)]
        unsafe {
            miri_static_root(&SHARED_DOMAIN as *const _ as *const u8);
        };

        &SHARED_DOMAIN
    }
}

/// Generate a [`Domain`] with an entirely unique domain family.
/// The generated family implements [`Singleton`],
#[macro_export]
macro_rules! unique_domain {
    () => {{
        struct UniqueFamily;
        // Safety: nowhere else can construct an instance of UniqueFamily to pass to Domain::new.
        unsafe impl Singleton for UniqueFamily {}
        Domain::new(&UniqueFamily)
    }};
}

// Macro to make new const only when not in loom.
macro_rules! new {
    ($($decl:tt)*) => {
        /// Construct a new domain with the given family type.
        ///
        /// The type checker protects you from accidentally using a `HazardPointer` from one domain
        /// _family_ (the type `F`) with an object protected by a domain in a different family.
        /// However, it does _not_ protect you from mixing up domains with the same family type.
        /// Therefore, prefer creating domains with [`unique_domain`] where possible, since it
        /// guarantees a unique `F` for every domain.
        ///
        /// See the [`Domain`] documentation for more details.
        pub $($decl)*(_: &'_ F) -> Self {
            // https://blog.rust-lang.org/2021/02/11/Rust-1.50.0.html#const-value-repetition-for-arrays
            #[cfg(not(loom))]
            let untagged = {
                // https://github.com/rust-lang/rust-clippy/issues/7665
                #[allow(clippy::declare_interior_mutable_const)]
                const RETIRED_LIST: RetiredList = RetiredList::new();
                [RETIRED_LIST; NUM_SHARDS]
            };
            #[cfg(loom)]
            let untagged = {
                [(); NUM_SHARDS].map(|_| RetiredList::new())
            };
            Self {
                hazptrs: HazPtrRecords {
                    head: AtomicPtr::new(core::ptr::null_mut()),
                    head_available: AtomicUsize::new(0),
                    count: AtomicIsize::new(0),
                },
                untagged,
                count: AtomicIsize::new(0),
                #[cfg(all(feature = "std", target_pointer_width = "64", not(loom)))]
                due_time: AtomicU64::new(0),
                nbulk_reclaims: AtomicUsize::new(0),
                family: PhantomData,
                shutdown: false,
            }
        }
    };
}

impl<F> Domain<F> {
    #[cfg(not(loom))]
    new!(const fn new);
    #[cfg(loom)]
    new!(fn new);

    pub(crate) fn acquire(&self) -> &HazPtrRecord {
        self.acquire_many::<1>()[0]
    }

    pub(crate) fn acquire_many<const N: usize>(&self) -> [&HazPtrRecord; N] {
        debug_assert!(N >= 1);

        let (mut head, n) = self.try_acquire_available::<N>();
        assert!(n <= N);

        let mut tail = core::ptr::null();
        [(); N].map(|_| {
            if !head.is_null() {
                tail = head;
                // Safety: HazPtrRecords are never deallocated.
                let rec = unsafe { &*head };
                head = rec.available_next.load(Ordering::Relaxed);
                rec
            } else {
                let rec = self.acquire_new();
                // Make sure we also link in the newly allocated nodes.
                if !tail.is_null() {
                    unsafe { &*tail }
                        .available_next
                        .store(rec as *const _ as *mut _, Ordering::Relaxed);
                }
                tail = rec as *const _;
                rec
            }
        })
    }

    pub(crate) fn release(&self, rec: &HazPtrRecord) {
        assert!(rec.available_next.load(Ordering::Relaxed).is_null());
        self.push_available(rec, rec);
    }

    pub(crate) fn release_many<const N: usize>(&self, recs: [&HazPtrRecord; N]) {
        let head = recs[0];
        let tail = recs.last().expect("we only give out with N > 0");
        assert!(tail.available_next.load(Ordering::Relaxed).is_null());
        self.push_available(head, tail);
    }

    fn try_acquire_available<const N: usize>(&self) -> (*const HazPtrRecord, usize) {
        debug_assert!(N >= 1);
        debug_assert_eq!(core::ptr::null::<HazPtrRecord>() as usize, 0);

        loop {
            let avail = self.hazptrs.head_available.load(Ordering::Acquire);
            if avail == core::ptr::null::<HazPtrRecord>() as usize {
                return (core::ptr::null_mut(), 0);
            }
            debug_assert_ne!(avail, core::ptr::null::<HazPtrRecord>() as usize | LOCK_BIT);
            if (avail as usize & LOCK_BIT) == 0 {
                // Definitely a valid pointer now.
                let avail: *const HazPtrRecord = avail as _;

                // The available list is not currently locked.
                //
                // XXX: This could be a fetch_or and allow progress even if there's a new (but
                // unlocked) head.
                if self
                    .hazptrs
                    .head_available
                    .compare_exchange_weak(
                        avail as usize,
                        avail as usize | LOCK_BIT,
                        Ordering::AcqRel,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    // Safety: We hold the lock on the available list.
                    let (rec, n) = unsafe { self.try_acquire_available_locked::<N>(avail) };
                    debug_assert!(n >= 1, "head_available was not null");
                    debug_assert!(n <= N);
                    return (rec, n);
                } else {
                    #[cfg(not(any(loom, feature = "std")))]
                    core::hint::spin_loop();
                    #[cfg(any(loom, feature = "std"))]
                    crate::sync::yield_now();
                }
            }
        }
    }

    /// # Safety
    ///
    /// Must already hold the lock on the available list
    unsafe fn try_acquire_available_locked<const N: usize>(
        &self,
        head: *const HazPtrRecord,
    ) -> (*const HazPtrRecord, usize) {
        debug_assert!(N >= 1);
        debug_assert!(!head.is_null());

        let mut tail = head;
        let mut n = 1;
        let mut next = unsafe { &*tail }.available_next.load(Ordering::Relaxed);

        while !next.is_null() && n < N {
            debug_assert_eq!((next as usize) & LOCK_BIT, 0);
            tail = next;
            next = unsafe { &*tail }.available_next.load(Ordering::Relaxed);
            n += 1;
        }

        // NOTE: This releases the lock
        self.hazptrs
            .head_available
            .store(next as usize, Ordering::Release);
        unsafe { &*tail }
            .available_next
            .store(core::ptr::null_mut(), Ordering::Relaxed);

        (head, n)
    }

    fn push_available(&self, head: &HazPtrRecord, tail: &HazPtrRecord) {
        debug_assert!(tail.available_next.load(Ordering::Relaxed).is_null());
        if cfg!(debug_assertions) {
            // XXX: check that head and tail are connected
        }
        debug_assert_eq!(head as *const _ as usize & LOCK_BIT, 0);
        loop {
            let avail = self.hazptrs.head_available.load(Ordering::Acquire);
            if (avail & LOCK_BIT) == 0 {
                tail.available_next
                    .store(avail as *mut _, Ordering::Relaxed);
                if self
                    .hazptrs
                    .head_available
                    .compare_exchange_weak(
                        avail,
                        head as *const _ as usize,
                        Ordering::AcqRel,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    break;
                }
            } else {
                #[cfg(not(any(loom, feature = "std")))]
                core::hint::spin_loop();
                #[cfg(any(loom, feature = "std"))]
                crate::sync::yield_now();
            }
        }
    }

    pub(crate) fn acquire_new(&self) -> &HazPtrRecord {
        // No free HazPtrRecords -- need to allocate a new one
        let hazptr = Box::into_raw(Box::new(HazPtrRecord {
            ptr: AtomicPtr::new(core::ptr::null_mut()),
            next: AtomicPtr::new(core::ptr::null_mut()),
            available_next: AtomicPtr::new(core::ptr::null_mut()),
        }));
        // And stick it at the head of the linked list
        let mut head = self.hazptrs.head.load(Ordering::Acquire);
        loop {
            // Safety: hazptr was never shared, so &mut is ok.
            unsafe { &mut *hazptr }.next.with_mut(|p| *p = head);
            match self.hazptrs.head.compare_exchange_weak(
                head,
                hazptr,
                // NOTE: Folly uses Release, but needs to be both for the load on success.
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // NOTE: Folly uses SeqCst because it's the default, not clear if
                    // necessary.
                    self.hazptrs.count.fetch_add(1, Ordering::SeqCst);
                    // Safety: HazPtrRecords are never de-allocated while the domain lives.
                    break unsafe { &*hazptr };
                }
                Err(head_now) => {
                    // Head has changed, try again with that as our next ptr.
                    head = head_now
                }
            }
        }
    }

    /// Retire `ptr`, and reclaim it once it is safe to do so.
    ///
    /// # Safety
    ///
    /// 1. no [`HazardPointer`] will guard `ptr` from this point forward.
    /// 2. `ptr` has not already been retired unless it has been reclaimed since then.
    /// 3. `ptr` is valid as `&T` until `self` is dropped.
    pub unsafe fn retire_ptr<T, P>(&self, ptr: *mut T) -> usize
    where
        P: Pointer<T>,
    {
        // First, stick ptr onto the list of retired objects.
        //
        // Safety: ptr will not be accessed after Domain is dropped, which is when 'domain ends.
        let retired = Box::new(unsafe {
            Retired::new(self, ptr, |ptr: *mut dyn Reclaim| {
                // Safety: the safety requirements of `from_raw` are the same as the ones to call
                // the deleter.
                let _ = P::from_raw(ptr as *mut T);
            })
        });

        self.push_list(retired)
    }

    /// Reclaim as many retired objects as possible.
    ///
    /// Returns the number of retired objects that were reclaimed.
    pub fn eager_reclaim(&self) -> usize {
        self.nbulk_reclaims.fetch_add(1, Ordering::Acquire);
        self.do_reclamation(0)
    }

    // Only used for tests -- waits for no outstanding reclaims.
    #[doc(hidden)]
    pub fn cleanup(&self) {
        self.eager_reclaim();
        self.wait_for_zero_bulk_reclaims(); // wait for concurrent bulk_reclaim-s
    }

    fn push_list(&self, mut retired: Box<Retired>) -> usize {
        assert!(
            retired.next.with_mut(|p| p.is_null()),
            "only single item retiring is supported atm"
        );

        crate::asymmetric_light_barrier();

        let retired = Box::into_raw(retired);
        unsafe { self.untagged[Self::calc_shard(retired)].push(retired, retired) };
        self.count.fetch_add(1, Ordering::Release);

        self.check_threshold_and_reclaim()
    }

    fn threshold(&self) -> isize {
        RCOUNT_THRESHOLD.max(HCOUNT_MULTIPLIER * self.hazptrs.count.load(Ordering::Acquire))
    }

    fn check_count_threshold(&self) -> isize {
        let mut rcount = self.count.load(Ordering::Acquire);
        while rcount > self.threshold() {
            match self
                .count
                .compare_exchange_weak(rcount, 0, Ordering::AcqRel, Ordering::Relaxed)
            {
                Ok(_) => {
                    #[cfg(all(feature = "std", target_pointer_width = "64", not(loom)))]
                    {
                        self.due_time
                            .store(Self::now() + SYNC_TIME_PERIOD, Ordering::Release);
                    }
                    return rcount;
                }
                Err(rcount_now) => rcount = rcount_now,
            }
        }
        0
    }

    #[cfg(all(feature = "std", target_pointer_width = "64", not(loom)))]
    fn check_due_time(&self) -> isize {
        let time = Self::now();
        let due = self.due_time.load(Ordering::Acquire);
        if time < due
            || self
                .due_time
                .compare_exchange(
                    due,
                    time + SYNC_TIME_PERIOD,
                    Ordering::AcqRel,
                    Ordering::Relaxed,
                )
                .is_err()
        {
            // Not yet due, or someone else noticed we were due already.
            return 0;
        }
        self.count.swap(0, Ordering::AcqRel)
    }

    fn check_threshold_and_reclaim(&self) -> usize {
        #[allow(unused_mut)]
        let mut rcount = self.check_count_threshold();
        if rcount == 0 {
            // TODO: Implement some kind of mock time for no_std.
            // Currently we reclaim only based on rcount on no_std
            // (also the reason for allow unused_mut)
            #[cfg(all(feature = "std", target_pointer_width = "64", not(loom)))]
            {
                rcount = self.check_due_time();
            }
            if rcount == 0 {
                return 0;
            }
        }

        self.nbulk_reclaims.fetch_add(1, Ordering::Acquire);
        self.do_reclamation(rcount)
    }

    fn do_reclamation(&self, mut rcount: isize) -> usize {
        let mut total_reclaimed = 0;
        loop {
            let mut done = true;
            let mut stolen_heads = [core::ptr::null_mut(); NUM_SHARDS];
            let mut empty = true;
            for (stolen_head, untagged) in stolen_heads.iter_mut().zip(&self.untagged) {
                *stolen_head = untagged.pop_all();
                if !stolen_head.is_null() {
                    empty = false;
                }
            }

            if !empty {
                crate::asymmetric_heavy_barrier(crate::HeavyBarrierKind::Expedited);

                // Find all guarded addresses.
                #[allow(clippy::mutable_key_type)]
                //XXX: Maybe use a sorted vec to reduce heap allocations, and have O(log(n)) lookups
                let mut guarded_ptrs = BTreeSet::new();
                let mut node = self.hazptrs.head.load(Ordering::Acquire);
                while !node.is_null() {
                    // Safety: HazPtrRecords are never de-allocated while the domain lives.
                    let n = unsafe { &*node };
                    guarded_ptrs.insert(n.ptr.load(Ordering::Acquire));
                    node = n.next.load(Ordering::Relaxed);
                }

                let (nreclaimed, is_done) =
                    self.match_reclaim_untagged(stolen_heads, &guarded_ptrs);
                done = is_done;

                rcount -= nreclaimed as isize;
                total_reclaimed += nreclaimed;
            }

            if rcount != 0 {
                self.count.fetch_add(rcount, Ordering::Release);
            }
            rcount = self.check_count_threshold();
            if rcount == 0 && done {
                break;
            }
        }
        self.nbulk_reclaims.fetch_sub(1, Ordering::Acquire);
        total_reclaimed
    }

    fn match_reclaim_untagged(
        &self,
        stolen_heads: [*mut Retired; NUM_SHARDS],
        guarded_ptrs: &BTreeSet<*mut u8>,
    ) -> (usize, bool) {
        let mut unreclaimed = core::ptr::null_mut();
        let mut unreclaimed_tail = unreclaimed;
        let mut nreclaimed = 0;

        // Sort nodes into those that can be reclaimed,
        // and those that are still guarded
        for mut node in stolen_heads {
            // XXX: This can probably also be hoisted out of the loop, and we can do a _single_
            // reclaim_unprotected call as well.
            let mut reclaimable = core::ptr::null_mut();

            while !node.is_null() {
                // Safety: All accessors only access the head, and the head is no longer pointing here.
                let n = unsafe { &*node };
                let next = n.next.load(Ordering::Relaxed);
                debug_assert_ne!(node, next);

                if !guarded_ptrs.contains(&(n.ptr as *mut u8)) {
                    // No longer guarded -- safe to reclaim.
                    n.next.store(reclaimable, Ordering::Relaxed);
                    reclaimable = node;
                    nreclaimed += 1;
                } else {
                    // Not safe to reclaim -- still guarded.
                    n.next.store(unreclaimed, Ordering::Relaxed);
                    unreclaimed = node;
                    if unreclaimed_tail.is_null() {
                        unreclaimed_tail = unreclaimed;
                    }
                }

                node = next;
            }

            // Safety:
            //
            // 1. No item in `reclaimable` has a hazard pointer guarding it, so we have the
            //    only remaining pointer to each item.
            // 2. Every Retired was originally constructed from a Box, and is thus valid.
            // 3. None of these Retired have been dropped previously, because we atomically
            //    stole the entire sublist from self.untagged.
            unsafe { self.reclaim_unprotected(reclaimable) };
        }

        let done = self.untagged.iter().all(|u| u.is_empty());
        // NOTE: We're _not_ respecting sharding here, presumably to avoid multiple push CASes.
        unsafe { self.untagged[0].push(unreclaimed, unreclaimed_tail) };

        (nreclaimed, done)
    }

    // # Safety
    //
    // All `Retired` nodes in `retired` are valid, unaliased, and can be taken ownership of.
    unsafe fn reclaim_unprotected(&self, mut retired: *mut Retired) {
        while !retired.is_null() {
            let next = unsafe { &*retired }.next.load(Ordering::Relaxed);
            let n = unsafe { Box::from_raw(retired) };

            // We uphold the Pointer::from_raw guarantees since:
            //
            //  - `n.ptr` has not yet been dropped because it was still on `retired`.
            //  - it will not be dropped again because we have removed it from `retired`.
            //  - `n.ptr` was allocated by the corresponding allocation method as per the
            //    safety guarantees of calling `retire`.
            unsafe { (n.deleter)(n.ptr) };

            // TODO: Support linked nodes for more efficient deallocation (`children`).

            retired = next;
        }
    }

    #[cfg(any(loom, miri))]
    fn now() -> u64 {
        0
    }

    #[cfg(all(feature = "std", target_pointer_width = "64", not(loom), not(miri)))]
    fn now() -> u64 {
        u64::try_from(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system time is set to before the epoch")
                .as_nanos(),
        )
        .expect("system time is too far into the future")
    }

    fn reclaim_all_objects(&mut self) {
        for i in 0..NUM_SHARDS {
            let head = self.untagged[i].pop_all();
            // Safety: &mut self implies that there are no active Hazard Pointers.
            // So, all objects are safe to reclaim.
            unsafe { self.reclaim_list_transitive(head) };
        }
    }

    unsafe fn reclaim_list_transitive(&self, head: *mut Retired) {
        // TODO: handle children
        unsafe { self.reclaim_unconditional(head) };
    }

    /// Equivalent to reclaim_unprotected, but differs in name to clarify that it will remove
    /// indiscriminately.
    unsafe fn reclaim_unconditional(&self, head: *mut Retired) {
        unsafe { self.reclaim_unprotected(head) };
    }

    fn wait_for_zero_bulk_reclaims(&self) {
        while self.nbulk_reclaims.load(Ordering::Acquire) > 0 {
            #[cfg(not(any(loom, feature = "std")))]
            core::hint::spin_loop();
            #[cfg(any(loom, feature = "std"))]
            crate::sync::yield_now();
        }
    }

    fn free_hazptr_recs(&mut self) {
        // NOTE: folly skips this step for the global domain, but the global domain is never
        // dropped in the first place, as it is a static. See
        //
        //   https://doc.rust-lang.org/reference/items/static-items.html

        let mut node: *mut HazPtrRecord = self.hazptrs.head.with_mut(|p| *p);
        while !node.is_null() {
            // Safety: we have &mut self, so no-one holds any of our hazard pointers any more,
            // as all holders are tied to 'domain (which must have expired to create the &mut).
            let mut n: Box<HazPtrRecord> = unsafe { Box::from_raw(node) };
            node = n.next.with_mut(|p| *p);
            drop(n);
        }
    }

    #[cfg(not(loom))]
    fn calc_shard(input: *mut Retired) -> usize {
        (input as usize >> IGNORED_LOW_BITS) & SHARD_MASK
    }

    #[cfg(loom)]
    fn calc_shard(_input: *mut Retired) -> usize {
        SHARD.fetch_add(1, Ordering::Relaxed) & SHARD_MASK
    }
}

impl<F> Drop for Domain<F> {
    fn drop(&mut self) {
        self.shutdown = true;

        self.reclaim_all_objects();
        self.free_hazptr_recs();
    }
}

struct HazPtrRecords {
    head: AtomicPtr<HazPtrRecord>,
    head_available: AtomicUsize, // really *mut HazPtrRecord
    count: AtomicIsize,
}

struct Retired {
    // This is + 'domain, which is enforced for anything that constructs a Retired
    ptr: *mut dyn Reclaim,
    /// # Safety
    ///
    /// Safe to call when it would be safe to call `from_raw(ptr)` on the originating `Pointer`
    /// type.
    deleter: unsafe fn(ptr: *mut dyn Reclaim),
    next: AtomicPtr<Retired>,
}

impl Retired {
    /// # Safety
    ///
    /// `ptr` will not be accessed after `'domain` ends.
    unsafe fn new<'domain, F>(
        _: &'domain Domain<F>,
        ptr: *mut (dyn Reclaim + 'domain),
        deleter: unsafe fn(ptr: *mut dyn Reclaim),
    ) -> Self {
        Retired {
            ptr: unsafe { core::mem::transmute::<_, *mut (dyn Reclaim + 'static)>(ptr) },
            deleter,
            next: AtomicPtr::new(core::ptr::null_mut()),
        }
    }
}

struct RetiredList {
    head: AtomicPtr<Retired>,
}

impl RetiredList {
    // Macro to make new const only when not in loom.
    #[cfg(not(loom))]
    const fn new() -> Self {
        Self {
            head: AtomicPtr::new(core::ptr::null_mut()),
        }
    }
    #[cfg(loom)]
    fn new() -> Self {
        Self {
            head: AtomicPtr::new(core::ptr::null_mut()),
        }
    }

    unsafe fn push(&self, sublist_head: *mut Retired, sublist_tail: *mut Retired) {
        if sublist_head.is_null() {
            // Pushing an empty list is easy.
            return;
        }

        // Stick it at the head of the linked list
        let head_ptr = &self.head;
        let mut head = head_ptr.load(Ordering::Acquire);
        loop {
            // Safety: we haven't moved anything in Retire, and we own the head, so last_next is
            // still valid.
            unsafe { &*sublist_tail }
                .next
                .store(head, Ordering::Release);
            match head_ptr.compare_exchange_weak(
                head,
                sublist_head,
                // NOTE: Folly uses Release, but needs to be both for the load on success.
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => break,
                Err(head_now) => {
                    // Head has changed, try again with that as our next ptr.
                    head = head_now
                }
            }
        }
    }

    fn pop_all(&self) -> *mut Retired {
        self.head.swap(core::ptr::null_mut(), Ordering::Acquire)
    }

    fn is_empty(&self) -> bool {
        self.head.load(Ordering::Relaxed).is_null()
    }
}

/*
fn foo() {
    let domain = Domain::new();
    'a: {
        let d: &'a Domain = &domain;
        let t = String::new();
        let z: Box<PrintOnDrop<&'a String>> = Box::new(PrintOnDrop(&t));
        d.retire(z); // z goes on .retired, but is _not_ dropped
        // drop(t), so z is no longer valid
    }
    // walk .retired, find that z can be reclaimed, call drop(z);
    drop(domain);
}
*/

/// ```compile_fail
/// use haphazard::*;
/// let dw = Domain::global();
/// let dr = Domain::new(&());
///
/// let x: AtomicPtr<i32, Global> = AtomicPtr::from(Box::new(42));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazardPointer::new_in_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { x.load(&mut h).expect("not null") };
/// ```
#[cfg(doctest)]
struct CannotConfuseGlobalWriter;

/// ```compile_fail
/// use haphazard::*;
/// let dw = Domain::new(&());
/// let dr = Domain::global();
///
/// let x: AtomicPtr<i32, ()> = AtomicPtr::from(Box::new(42));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazardPointer::new_in_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { x.load(&mut h).expect("not null") };
/// ```
#[cfg(doctest)]
struct CannotConfuseGlobalReader;

/// ```compile_fail
/// use haphazard::*;
/// let dw = unique_domain!();
/// let dr = unique_domain!();
///
/// fn build_ptr_in_domain<T, F, P, B>(_: &Domain<F>, builder: B) -> AtomicPtr<T, F, P>
/// where
///     B: Fn() -> AtomicPtr<T, F, P>,
/// {
///     builder()
/// }
/// let x = build_ptr_in_domain(&dw, || AtomicPtr::from(Box::new(42)));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazardPointer::new_in_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = x.safe_load(&mut h).expect("not null");
/// ```
#[cfg(doctest)]
struct CannotConfuseAcrossFamilies;

#[cfg(test)]
mod tests {
    use super::Domain;
    use core::{ptr::null_mut, sync::atomic::Ordering};

    #[test]
    fn acquire_many_skips_used_nodes() {
        let domain = Domain::new(&());
        let rec1 = domain.acquire();
        let rec2 = domain.acquire();
        let rec3 = domain.acquire();

        assert_eq!(
            rec3.next.load(Ordering::Relaxed),
            rec2 as *const _ as *mut _
        );
        assert_eq!(
            rec2.next.load(Ordering::Relaxed),
            rec1 as *const _ as *mut _
        );
        assert_eq!(rec1.next.load(Ordering::Relaxed), core::ptr::null_mut());
        domain.release(rec1);
        domain.release(rec3);
        drop(rec1);
        drop(rec3);

        let [one, two, three] = domain.acquire_many();

        assert_eq!(
            one.available_next.load(Ordering::Relaxed),
            two as *const _ as *mut _
        );
        assert_eq!(
            two.available_next.load(Ordering::Relaxed),
            three as *const _ as *mut _
        );
        assert_eq!(
            three.available_next.load(Ordering::Relaxed),
            core::ptr::null_mut(),
        );

        // one was previously rec3
        // two was previously rec1
        // so proper ordering for next is three -> rec3/one -> rec2 -> rec1/two
        assert_eq!(
            three.next.load(Ordering::Relaxed),
            one as *const _ as *mut _
        );
        assert_eq!(one.next.load(Ordering::Relaxed), rec2 as *const _ as *mut _);
        assert_eq!(rec2.next.load(Ordering::Relaxed), two as *const _ as *mut _);
    }

    #[test]
    fn acquire_many_orders_nodes_between_acquires() {
        let domain = Domain::new(&());
        let rec1 = domain.acquire();
        let rec2 = domain.acquire();

        assert_eq!(
            rec2.next.load(Ordering::Relaxed),
            rec1 as *const _ as *mut _
        );
        domain.release(rec2);
        drop(rec2);

        // one was previously rec2
        // two is a new node
        let [one, two] = domain.acquire_many();

        assert_eq!(
            one.available_next.load(Ordering::Relaxed),
            two as *const _ as *mut _
        );
        assert_eq!(
            two.available_next.load(Ordering::Relaxed),
            core::ptr::null_mut(),
        );

        assert_eq!(two.next.load(Ordering::Relaxed), one as *const _ as *mut _);
        assert_eq!(one.next.load(Ordering::Relaxed), rec1 as *const _ as *mut _);
    }

    #[test]
    fn acquire_many_properly_orders_reused_nodes() {
        let domain = Domain::new(&());
        let rec1 = domain.acquire();
        let rec2 = domain.acquire();
        let rec3 = domain.acquire();

        // rec3 -> rec2 -> rec1
        assert_eq!(rec1.next.load(Ordering::Relaxed), core::ptr::null_mut(),);
        assert_eq!(
            rec2.next.load(Ordering::Relaxed),
            rec1 as *const _ as *mut _
        );
        assert_eq!(
            rec3.next.load(Ordering::Relaxed),
            rec2 as *const _ as *mut _
        );

        // rec1 available_next -> null
        domain.release(rec1);
        // rec2 available_next -> rec1
        domain.release(rec2);
        // rec3 available_next -> rec2
        domain.release(rec3);
        drop(rec1);
        drop(rec2);
        drop(rec3);

        // one is rec3
        // two is rec2
        // three is rec1
        let [one, two, three, four, five] = domain.acquire_many();

        assert_eq!(
            one.available_next.load(Ordering::Relaxed),
            two as *const _ as *mut _
        );
        assert_eq!(
            two.available_next.load(Ordering::Relaxed),
            three as *const _ as *mut _
        );
        assert_eq!(
            three.available_next.load(Ordering::Relaxed),
            four as *const _ as *mut _
        );
        assert_eq!(
            four.available_next.load(Ordering::Relaxed),
            five as *const _ as *mut _
        );
        assert_eq!(
            five.available_next.load(Ordering::Relaxed),
            core::ptr::null_mut(),
        );

        assert_eq!(
            five.next.load(Ordering::Relaxed),
            four as *const _ as *mut _
        );
        assert_eq!(four.next.load(Ordering::Relaxed), one as *const _ as *mut _);
        assert_eq!(one.next.load(Ordering::Relaxed), two as *const _ as *mut _);
        assert_eq!(
            two.next.load(Ordering::Relaxed),
            three as *const _ as *mut _
        );
        assert_eq!(three.next.load(Ordering::Relaxed), null_mut());
    }
}
