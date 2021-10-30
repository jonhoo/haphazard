use crate::{Deleter, HazPtrRecord, Reclaim};
use std::collections::HashSet;
use std::marker::PhantomData;
use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};

const SYNC_TIME_PERIOD: u64 = std::time::Duration::from_nanos(2000000000).as_nanos() as u64;
const RCOUNT_THRESHOLD: isize = 1000;
const HCOUNT_MULTIPLIER: isize = 2;

#[non_exhaustive]
pub struct Global;
impl Global {
    const fn new() -> Self {
        Global
    }
}

static SHARED_DOMAIN: Domain<Global> = Domain::new(&Global::new());

// Holds linked list of HazPtrRecords
pub struct Domain<F> {
    hazptrs: HazPtrRecords,
    untagged: RetiredList,
    family: PhantomData<F>,
    due_time: AtomicU64,
    nbulk_reclaims: AtomicUsize,
    count: AtomicIsize,
    shutdown: bool,
}

impl Domain<Global> {
    pub fn global() -> &'static Self {
        &SHARED_DOMAIN
    }
}

#[macro_export]
macro_rules! unique_domain {
    () => {
        Domain::new(&|| {})
    };
}

impl<F> Domain<F> {
    pub const fn new(_: &F) -> Self {
        Self {
            hazptrs: HazPtrRecords {
                head: AtomicPtr::new(std::ptr::null_mut()),
                count: AtomicIsize::new(0),
            },
            untagged: RetiredList {
                head: AtomicPtr::new(std::ptr::null_mut()),
            },
            count: AtomicIsize::new(0),
            due_time: AtomicU64::new(0),
            nbulk_reclaims: AtomicUsize::new(0),
            family: PhantomData,
            shutdown: false,
        }
    }

    pub(crate) fn acquire(&self) -> &HazPtrRecord {
        if let Some(hazptr) = self.try_acquire_existing() {
            hazptr
        } else {
            self.acquire_new()
        }
    }

    fn try_acquire_existing(&self) -> Option<&HazPtrRecord> {
        let head_ptr = &self.hazptrs.head;
        let mut node = head_ptr.load(Ordering::Acquire);
        while !node.is_null() {
            // Safety: HazPtrRecords are never de-allocated while the domain lives.
            let n = unsafe { &*node };
            if n.try_acquire() {
                return Some(n);
            }
            node = n.next.load(Ordering::Relaxed);
        }
        None
    }

    pub(crate) fn acquire_new(&self) -> &HazPtrRecord {
        // No free HazPtrRecords -- need to allocate a new one
        let hazptr = Box::into_raw(Box::new(HazPtrRecord {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
            next: AtomicPtr::new(std::ptr::null_mut()),
            active: AtomicBool::new(true),
        }));
        // And stick it at the head of the linked list
        let mut head = self.hazptrs.head.load(Ordering::Acquire);
        loop {
            // Safety: hazptr was never shared, so &mut is ok.
            *unsafe { &mut *hazptr }.next.get_mut() = head;
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

    /// # Safety
    ///
    /// ptr remains valid until `self` is dropped.
    pub(crate) unsafe fn retire<'domain>(
        &'domain self,
        ptr: *mut (dyn Reclaim + 'domain),
        deleter: &'static dyn Deleter,
    ) {
        // First, stick ptr onto the list of retired objects.
        //
        // Safety: ptr will not be accessed after Domain is dropped, which is when 'domain ends.
        let retired = Box::new(unsafe { Retired::new(self, ptr, deleter) });

        self.push_list(retired);
    }

    fn push_list(&self, mut retired: Box<Retired>) {
        assert!(
            retired.next.get_mut().is_null(),
            "only single item retiring is supported atm"
        );

        crate::asymmetric_light_barrier();

        let retired = Box::into_raw(retired);
        unsafe { self.untagged.push(retired, retired) };
        self.count.fetch_add(1, Ordering::Release);

        self.check_threshold_and_reclaim();
    }

    fn threshold(&self) -> isize {
        RCOUNT_THRESHOLD.max(HCOUNT_MULTIPLIER * self.hazptrs.count.load(Ordering::Acquire))
    }

    fn check_count_threshold(&self) -> isize {
        let rcount = self.count.load(Ordering::Acquire);
        while rcount > self.threshold() {
            if self
                .count
                .compare_exchange_weak(rcount, 0, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                self.due_time
                    .store(Self::now() + SYNC_TIME_PERIOD, Ordering::Release);
                return rcount;
            }
        }
        0
    }

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

    fn check_threshold_and_reclaim(&self) {
        let mut rcount = self.check_count_threshold();
        if rcount == 0 {
            rcount = self.check_due_time();
            if rcount == 0 {
                return;
            }
        }

        self.nbulk_reclaims.fetch_add(1, Ordering::Acquire);
        self.do_reclamation(rcount);
    }

    fn do_reclamation(&self, mut rcount: isize) -> usize {
        let mut total_reclaimed = 0;
        loop {
            let mut done = true;
            let stolen_head = self.untagged.pop_all();

            if !stolen_head.is_null() {
                crate::asymmetric_heavy_barrier(crate::HeavyBarrierKind::Expedited);

                // Find all guarded addresses.
                #[allow(clippy::mutable_key_type)]
                let mut guarded_ptrs = HashSet::new();
                let mut node = self.hazptrs.head.load(Ordering::Acquire);
                while !node.is_null() {
                    // Safety: HazPtrRecords are never de-allocated while the domain lives.
                    let n = unsafe { &*node };
                    // NOTE: Folly doesn't skip active here, but that seems wrong?
                    if n.active.load(Ordering::SeqCst) {
                        guarded_ptrs.insert(n.ptr.load(Ordering::Acquire));
                    }
                    node = n.next.load(Ordering::Relaxed);
                }

                // Sort nodes into those that can be reclaimed,
                // and those that are still guarded
                let mut node = stolen_head;
                let mut reclaimable = std::ptr::null_mut();
                let mut unreclaimed = std::ptr::null_mut();
                let mut unreclaimed_tail = unreclaimed;
                let mut nreclaimable: isize = 0;

                while !node.is_null() {
                    // Safety: All accessors only access the head, and the head is no longer pointing here.
                    let n = unsafe { &*node };
                    let next = n.next.load(Ordering::Relaxed);
                    debug_assert_ne!(node, next);

                    if !guarded_ptrs.contains(&(n.ptr as *mut u8)) {
                        // No longer guarded -- safe to reclaim.
                        n.next.store(reclaimable, Ordering::Relaxed);
                        reclaimable = node;
                        nreclaimable += 1;
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
                done = self.untagged.is_empty();
                unsafe { self.untagged.push(unreclaimed, unreclaimed_tail) };

                rcount -= nreclaimable;
                total_reclaimed += nreclaimable as usize;
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

    // # Safety
    //
    // All `Retired` nodes in `retired` are valid, unaliased, and can be taken ownership of.
    unsafe fn reclaim_unprotected(&self, mut retired: *mut Retired) {
        while !retired.is_null() {
            let next = unsafe { &*retired }.next.load(Ordering::Relaxed);
            let n = unsafe { Box::from_raw(retired) };

            // Safety:
            //  - `n.ptr` has not yet been dropped because it was still on `retired`.
            //  - it will not be dropped again because we have removed it from `retired`.
            //  - `n.ptr` was allocated by the corresponding allocation method as per the
            //    safety guarantees of calling `retire`.
            unsafe { n.deleter.delete(n.ptr) };

            // TODO: Support linked nodes for more efficient deallocation (`children`).

            retired = next;
        }
    }

    fn now() -> u64 {
        use std::convert::TryFrom;
        u64::try_from(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system time is set to before the epoch")
                .as_nanos(),
        )
        .expect("system time is too far into the future")
    }

    pub fn eager_reclaim(&self) -> usize {
        let rcount = self.count.swap(0, Ordering::AcqRel);
        self.nbulk_reclaims.fetch_add(1, Ordering::Acquire);
        self.do_reclamation(rcount)
    }

    pub(crate) fn release(&self, hazard: &HazPtrRecord) {
        hazard.release();
    }

    fn reclaim_all_objects(&mut self) {
        let head = self.untagged.pop_all();
        // Safety: &mut self implies that there are no active Hazard Pointers.
        // So, all objects are safe to reclaim.
        unsafe { self.reclaim_list_transitive(head) };
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

    fn free_hazptr_recs(&mut self) {
        // NOTE: folly skips this step for the global domain, but the global domain is never
        // dropped in the first place, as it is a static. See
        //
        //   https://doc.rust-lang.org/reference/items/static-items.html

        let mut node: *mut HazPtrRecord = *self.hazptrs.head.get_mut();
        while !node.is_null() {
            // Safety: we have &mut self, so no-one holds any of our hazard pointers any more,
            // as all holders are tied to 'domain (which must have expired to create the &mut).
            let mut n: Box<HazPtrRecord> = unsafe { Box::from_raw(node) };
            debug_assert!(!*n.active.get_mut());
            node = *n.next.get_mut();
            drop(n);
        }
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
    count: AtomicIsize,
}

struct Retired {
    // This is + 'domain, which is enforced for anything that constructs a Retired
    ptr: *mut dyn Reclaim,
    deleter: &'static dyn Deleter,
    next: AtomicPtr<Retired>,
}

impl Retired {
    /// # Safety
    ///
    /// `ptr` will not be accessed after `'domain` ends.
    unsafe fn new<'domain, F>(
        _: &'domain Domain<F>,
        ptr: *mut (dyn Reclaim + 'domain),
        deleter: &'static dyn Deleter,
    ) -> Self {
        Retired {
            ptr: unsafe { std::mem::transmute::<_, *mut (dyn Reclaim + 'static)>(ptr) },
            deleter,
            next: AtomicPtr::new(std::ptr::null_mut()),
        }
    }
}

struct RetiredList {
    head: AtomicPtr<Retired>,
}

impl RetiredList {
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
        self.head.swap(std::ptr::null_mut(), Ordering::Acquire)
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
/// use std::sync::atomic::AtomicPtr;
/// use haphazard::*;
/// let dw = Domain::global();
/// let dr = Domain::new(&());
///
/// let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&dw, 42))));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazardPointer::make_in_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { h.protect(&x) }.expect("not null");
/// ```
#[cfg(doctest)]
struct CannotConfuseGlobalWriter;

/// ```compile_fail
/// use std::sync::atomic::AtomicPtr;
/// use haphazard::*;
/// let dw = Domain::new(&());
/// let dr = Domain::global();
///
/// let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&dw, 42))));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazardPointer::make_in_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { h.protect(&x) }.expect("not null");
/// ```
#[cfg(doctest)]
struct CannotConfuseGlobalReader;

/// ```compile_fail
/// use std::sync::atomic::AtomicPtr;
/// use haphazard::*;
/// let dw = unique_domain!();
/// let dr = unique_domain!();
///
/// let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&dw, 42))));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazardPointer::make_in_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { h.protect(&x) }.expect("not null");
/// ```
#[cfg(doctest)]
struct CannotConfuseAcrossFamilies;
