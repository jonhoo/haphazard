use crate::{Deleter, HazPtr, Reclaim};
use std::collections::HashSet;
use std::marker::PhantomData;
use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize};

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
            },
            retired: RetiredList {
                head: AtomicPtr::new(std::ptr::null_mut()),
                count: AtomicUsize::new(0),
            },
            family: PhantomData,
        }
    }

    pub(crate) fn acquire(&self) -> &HazPtr {
        let head_ptr = &self.hazptrs.head;
        let mut node = head_ptr.load(Ordering::SeqCst);
        loop {
            // Safety: HazPtrs are never de-allocated.
            while !node.is_null() && unsafe { &*node }.active.load(Ordering::SeqCst) {
                // Safety: HazPtrs are never de-allocated.
                node = unsafe { &*node }.next.load(Ordering::SeqCst);
            }
            if node.is_null() {
                // No free HazPtrs -- need to allocate a new one
                let hazptr = Box::into_raw(Box::new(HazPtr {
                    ptr: AtomicPtr::new(std::ptr::null_mut()),
                    next: AtomicPtr::new(std::ptr::null_mut()),
                    active: AtomicBool::new(true),
                }));
                // And stick it at the head of the linked list
                let mut head = head_ptr.load(Ordering::SeqCst);
                break loop {
                    // Safety: hazptr was never shared, so &mut is ok.
                    *unsafe { &mut *hazptr }.next.get_mut() = head;
                    match head_ptr.compare_exchange_weak(
                        head,
                        hazptr,
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                    ) {
                        Ok(_) => {
                            // Safety: HazPtrs are never de-allocated.
                            break unsafe { &*hazptr };
                        }
                        Err(head_now) => {
                            // Head has changed, try again with that as our next ptr.
                            head = head_now
                        }
                    }
                };
            } else {
                // Safety: HazPtrs are never de-allocated.
                let node = unsafe { &*node };
                if node
                    .active
                    .compare_exchange_weak(false, true, Ordering::SeqCst, Ordering::SeqCst)
                    .is_ok()
                {
                    // It's ours!
                    break node;
                } else {
                    // Someone else grabbed this node right before us.
                    // Keep walking
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
        // Increment the count _before_ we give anyone a chance to reclaim it.
        self.retired.count.fetch_add(1, Ordering::SeqCst);
        // Stick it at the head of the linked list
        let head_ptr = &self.retired.head;
        let mut head = head_ptr.load(Ordering::SeqCst);
        loop {
            // Safety: retired was never shared, so &mut is ok.
            *unsafe { &mut *retired }.next.get_mut() = head;
            match head_ptr.compare_exchange_weak(head, retired, Ordering::SeqCst, Ordering::SeqCst)
            {
                Ok(_) => break,
                Err(head_now) => {
                    // Head has changed, try again with that as our next ptr.
                    head = head_now
                }
            }
        }

        // Now, check if we need to retire.
        // TODO: better heuristics "once in a while"
        if self.retired.count.load(Ordering::SeqCst) != 0 {
            self.bulk_reclaim(0, false);
        }
    }

    pub fn eager_reclaim(&self, block: bool) -> usize {
        self.bulk_reclaim(0, block)
    }

    fn bulk_reclaim(&self, prev_reclaimed: usize, block: bool) -> usize {
        let steal = self
            .retired
            .head
            .swap(std::ptr::null_mut(), Ordering::SeqCst);
        if steal.is_null() {
            // Nothing to reclaim!
            return 0;
        }

        // Find all guarded addresses.
        #[allow(clippy::mutable_key_type)]
        let mut guarded_ptrs = HashSet::new();
        let mut node = self.hazptrs.head.load(Ordering::SeqCst);
        while !node.is_null() {
            // Safety: HazPtrs are never de-allocated.
            let n = unsafe { &*node };
            if n.active.load(Ordering::SeqCst) {
                guarded_ptrs.insert(n.ptr.load(Ordering::SeqCst));
            }
            node = n.next.load(Ordering::SeqCst);
        }

        // Reclaim any retired objects that aren't guarded
        let mut node = steal;
        let mut remaining = std::ptr::null_mut();
        let mut tail = None;
        let mut reclaimed: usize = 0;
        while !node.is_null() {
            // Safety: All accessors only access the head, and the head is no longer pointing here.
            let current = node;
            let n = unsafe { &*current };
            node = n.next.load(Ordering::SeqCst);

            if guarded_ptrs.contains(&(n.ptr as *mut u8)) {
                // Not safe to reclaim -- still guarded.
                n.next.store(remaining, Ordering::SeqCst);
                remaining = current;
                if tail.is_none() {
                    tail = Some(remaining);
                }
            } else {
                // No longer guarded -- reclaim using deleter.

                // Safety: `current` has no hazard pointers guarding it, so we have the only
                // remaining pointer.
                let n = unsafe { Box::from_raw(current) };

                // Safety:
                //  - `n.ptr` has not yet been dropped because it was still on `retired`.
                //  - it will not be dropped again because we have removed it from `retired`.
                //  - `n.ptr` was allocated by the corresponding allocation method as per the
                //    safety guarantees of calling `retire`.
                unsafe { n.deleter.delete(n.ptr) };

                reclaimed += 1;
            }
        }

        self.retired.count.fetch_sub(reclaimed, Ordering::SeqCst);
        let total_reclaimed = prev_reclaimed + reclaimed;

        let tail = if let Some(tail) = tail {
            assert!(!remaining.is_null());
            tail
        } else {
            assert!(remaining.is_null());
            return total_reclaimed;
        };

        let head_ptr = &self.retired.head;
        let mut head = head_ptr.load(Ordering::SeqCst);
        loop {
            // Safety: we still have exclusive access to remaining, which includes tail.
            *unsafe { &mut *tail }.next.get_mut() = head;
            match head_ptr.compare_exchange_weak(
                head,
                remaining,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break,
                Err(head_now) => {
                    // Head has changed, try again with that as our next ptr.
                    head = head_now
                }
            }
        }

        if !remaining.is_null() && block {
            // Caller wants to reclaim _everything_, but some were left, so try again.
            std::thread::yield_now();
            // NOTE: Allows tail recursion by passing down reclaimed
            return self.bulk_reclaim(total_reclaimed, true);
        }

        total_reclaimed
    }
}

impl<F> Drop for HazPtrDomain<F> {
    fn drop(&mut self) {
        // There should be no hazard pointers active, so all retired objects can be reclaimed.
        let nretired = *self.retired.count.get_mut();
        let nreclaimed = self.bulk_reclaim(0, false);
        assert_eq!(nretired, nreclaimed);
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
    count: AtomicUsize,
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
