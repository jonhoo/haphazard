use crate::{Deleter, HazPtr, Reclaim};
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

static SHARED_DOMAIN: HazPtrDomain<Global> = HazPtrDomain::new(&Global::new());

// Holds linked list of HazPtrs
pub struct HazPtrDomain<F> {
    hazptrs: HazPtrs,
    retired: RetiredList,
    family: PhantomData<F>,
    sync_time: AtomicU64,
    nbulk_reclaims: AtomicUsize,
}

impl HazPtrDomain<Global> {
    pub fn global() -> &'static Self {
        &SHARED_DOMAIN
    }
}

#[macro_export]
macro_rules! unique_domain {
    () => {
        HazPtrDomain::new(&|| {})
    };
}

impl<F> HazPtrDomain<F> {
    pub const fn new(_: &F) -> Self {
        Self {
            hazptrs: HazPtrs {
                head: AtomicPtr::new(std::ptr::null_mut()),
                count: AtomicIsize::new(0),
            },
            retired: RetiredList {
                head: AtomicPtr::new(std::ptr::null_mut()),
                count: AtomicIsize::new(0),
            },
            sync_time: AtomicU64::new(0),
            nbulk_reclaims: AtomicUsize::new(0),
            family: PhantomData,
        }
    }

    pub(crate) fn acquire(&self) -> &HazPtr {
        if let Some(hazptr) = self.try_acquire_existing() {
            hazptr
        } else {
            self.acquire_new()
        }
    }

    fn try_acquire_existing(&self) -> Option<&HazPtr> {
        let head_ptr = &self.hazptrs.head;
        let mut node = head_ptr.load(Ordering::Acquire);
        while !node.is_null() {
            // Safety: HazPtrs are never de-allocated while the domain lives.
            let n = unsafe { &*node };
            if n.try_acquire() {
                return Some(n);
            }
            node = n.next.load(Ordering::Relaxed);
        }
        None
    }

    pub(crate) fn acquire_new(&self) -> &HazPtr {
        // No free HazPtrs -- need to allocate a new one
        let hazptr = Box::into_raw(Box::new(HazPtr {
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
                    // Safety: HazPtrs are never de-allocated while the domain lives.
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
        let retired = Box::into_raw(Box::new(unsafe { Retired::new(self, ptr, deleter) }));

        crate::asymmetric_light_barrier();

        // Stick it at the head of the linked list
        let head_ptr = &self.retired.head;
        let mut head = head_ptr.load(Ordering::Acquire);
        loop {
            // Safety: retired was never shared, so &mut is ok.
            *unsafe { &mut *retired }.next.get_mut() = head;
            match head_ptr.compare_exchange_weak(
                head,
                retired,
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

        self.retired.count.fetch_add(1, Ordering::Release);

        // TODO: Folly has if check here, but only for recursion from bulk_lookup_and_reclaim,
        // which we don't do, so check isn't necessary.
        self.check_cleanup_and_reclaim();
    }

    fn check_cleanup_and_reclaim(&self) {
        if self.try_timed_cleanup() {
            return;
        }
        if Self::reached_threshold(
            self.retired.count.load(Ordering::Acquire),
            self.hazptrs.count.load(Ordering::Acquire),
        ) {
            self.try_bulk_reclaim();
        }
    }

    fn try_timed_cleanup(&self) -> bool {
        if !self.check_sync_time() {
            return false;
        }
        self.relaxed_cleanup();
        true
    }

    fn check_sync_time(&self) -> bool {
        use std::convert::TryFrom;
        let time = u64::try_from(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system time is set to before the epoch")
                .as_nanos(),
        )
        .expect("system time is too far into the future");
        let sync_time = self.sync_time.load(Ordering::Relaxed);

        // If it's not time to clean yet, or someone else just started cleaning, don't clean.
        time > sync_time
            && self
                .sync_time
                .compare_exchange(
                    sync_time,
                    time + SYNC_TIME_PERIOD,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                )
                .is_ok()
    }

    fn relaxed_cleanup(&self) {
        self.retired.count.store(0, Ordering::Release);
        self.bulk_reclaim(true);
    }

    const fn reached_threshold(rc: isize, hc: isize) -> bool {
        rc >= RCOUNT_THRESHOLD && rc >= HCOUNT_MULTIPLIER * hc
    }

    fn try_bulk_reclaim(&self) {
        let hc = self.hazptrs.count.load(Ordering::Acquire);
        let rc = self.retired.count.load(Ordering::Acquire);
        if !Self::reached_threshold(rc, hc) {
            return;
        }

        let rc = self.retired.count.swap(0, Ordering::Release);
        if !Self::reached_threshold(rc, hc) {
            // No need to add `rc` back to `self.retired.count`.
            // At least one concurrent `try_bulk_reclaim` will proceed to `bulk_reclaim`.
            return;
        }

        self.bulk_reclaim(false);
    }

    fn bulk_reclaim(&self, transitive: bool) -> usize {
        self.nbulk_reclaims.fetch_add(1, Ordering::Acquire);

        let mut reclaimed = 0;

        loop {
            let steal = self
                .retired
                .head
                .swap(std::ptr::null_mut(), Ordering::Acquire);

            crate::asymmetric_heavy_barrier(crate::HeavyBarrierKind::Expedited);

            if steal.is_null() {
                // Nothing to reclaim!
                return reclaimed;
            }

            // Find all guarded addresses.
            #[allow(clippy::mutable_key_type)]
            let mut guarded_ptrs = HashSet::new();
            let mut node = self.hazptrs.head.load(Ordering::Acquire);
            while !node.is_null() {
                // Safety: HazPtrs are never de-allocated while the domain lives.
                let n = unsafe { &*node };
                // NOTE: Folly doesn't skip active here, but that seems wrong?
                if n.active.load(Ordering::SeqCst) {
                    guarded_ptrs.insert(n.ptr.load(Ordering::Acquire));
                }
                node = n.next.load(Ordering::Relaxed);
            }

            let (reclaimed_now, done) = self.bulk_lookup_and_reclaim(steal, guarded_ptrs);
            reclaimed += reclaimed_now;
            if done || !transitive {
                break;
            }
        }
        self.nbulk_reclaims.fetch_sub(1, Ordering::Release);
        reclaimed
    }

    fn bulk_lookup_and_reclaim(
        &self,
        stolen_retired_head: *mut Retired,
        guarded_ptrs: HashSet<*mut u8>,
    ) -> (usize, bool) {
        // Reclaim any retired objects that aren't guarded
        let mut node = stolen_retired_head;
        let mut remaining = std::ptr::null_mut();
        let mut tail = None;
        let mut reclaimed: usize = 0;
        let mut still_retired: isize = 0;

        while !node.is_null() {
            // Safety: All accessors only access the head, and the head is no longer pointing here.
            let n = unsafe { &*node };
            let next = n.next.load(Ordering::Relaxed);
            debug_assert_ne!(node, next);

            if !guarded_ptrs.contains(&(n.ptr as *mut u8)) {
                // No longer guarded -- reclaim using deleter.

                // Safety: `current` has no hazard pointers guarding it, so we have the only
                // remaining pointer.
                let n = unsafe { Box::from_raw(node) };

                // Safety:
                //  - `n.ptr` has not yet been dropped because it was still on `retired`.
                //  - it will not be dropped again because we have removed it from `retired`.
                //  - `n.ptr` was allocated by the corresponding allocation method as per the
                //    safety guarantees of calling `retire`.
                unsafe { n.deleter.delete(n.ptr) };

                // TODO: Support linked nodes for more efficient deallocation (`children`).

                reclaimed += 1;
            } else {
                // Not safe to reclaim -- still guarded.
                n.next.store(remaining, Ordering::Relaxed);
                remaining = node;
                if tail.is_none() {
                    tail = Some(remaining);
                }
                still_retired += 1;
            }

            node = next;
        }

        let done = self.retired.head.load(Ordering::Acquire).is_null();

        let tail = if let Some(tail) = tail {
            assert!(!remaining.is_null());
            assert_ne!(still_retired, 0);
            // NOTE: Folly here calls push_retired, we do the push inline below.
            tail
        } else {
            assert!(remaining.is_null());
            assert_eq!(still_retired, 0);
            return (reclaimed, done);
        };

        crate::asymmetric_light_barrier();

        let head_ptr = &self.retired.head;
        let mut head = head_ptr.load(Ordering::Acquire);
        loop {
            // Safety: we still have exclusive access to remaining, which includes tail.
            *unsafe { &mut *tail }.next.get_mut() = head;
            match head_ptr.compare_exchange_weak(
                head,
                remaining,
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

        self.retired
            .count
            .fetch_add(still_retired, Ordering::Release);
        (reclaimed, done)
    }

    pub fn eager_reclaim(&self) -> usize {
        self.bulk_reclaim(true)
    }
}

impl<F> Drop for HazPtrDomain<F> {
    fn drop(&mut self) {
        // There should be no hazard pointers active, so all retired objects can be reclaimed.
        let nretired = *self.retired.count.get_mut();
        let nreclaimed = self.bulk_reclaim(true);
        assert_eq!(nretired, nreclaimed as isize);
        assert!(self.retired.head.get_mut().is_null());

        // Also drop all hazard pointers, as no-one should be holding them any more.
        let mut node: *mut HazPtr = *self.hazptrs.head.get_mut();
        while !node.is_null() {
            // Safety: we're in Drop, so no-one holds any of our hazard pointers any more,
            // as all holders are tied to 'domain (which must have expired on drop).
            let mut n: Box<HazPtr> = unsafe { Box::from_raw(node) };
            assert!(!*n.active.get_mut());
            node = *n.next.get_mut();
            drop(n);
        }
    }
}

struct HazPtrs {
    head: AtomicPtr<HazPtr>,
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
        _: &'domain HazPtrDomain<F>,
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
    count: AtomicIsize,
}

/*
fn foo() {
    let domain = HazPtrDomain::new();
    'a: {
        let d: &'a HazPtrDomain = &domain;
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
/// let dw = HazPtrDomain::global();
/// let dr = HazPtrDomain::new(&());
///
/// let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&dw, 42))));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazPtrHolder::for_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { h.load(&x) }.expect("not null");
/// ```
#[cfg(doctest)]
struct CannotConfuseGlobalWriter;

/// ```compile_fail
/// use std::sync::atomic::AtomicPtr;
/// use haphazard::*;
/// let dw = HazPtrDomain::new(&());
/// let dr = HazPtrDomain::global();
///
/// let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&dw, 42))));
///
/// // Reader uses a different domain thant the writer!
/// let mut h = HazPtrHolder::for_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { h.load(&x) }.expect("not null");
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
/// let mut h = HazPtrHolder::for_domain(&dr);
///
/// // This shouldn't compile because families differ.
/// let _ = unsafe { h.load(&x) }.expect("not null");
/// ```
#[cfg(doctest)]
struct CannotConfuseAcrossFamilies;
