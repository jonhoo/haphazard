use crate::{Deleter, HazPtr, Reclaim};
use std::collections::HashSet;
use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize};

pub static SHARED_DOMAIN: HazPtrDomain = HazPtrDomain {
    hazptrs: HazPtrs {
        head: AtomicPtr::new(std::ptr::null_mut()),
    },
    retired: RetiredList {
        head: AtomicPtr::new(std::ptr::null_mut()),
        count: AtomicUsize::new(0),
    },
};

// Holds linked list of HazPtrs
pub struct HazPtrDomain {
    hazptrs: HazPtrs,
    retired: RetiredList,
}

impl HazPtrDomain {
    pub(crate) fn acquire(&self) -> &'static HazPtr {
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

    pub(crate) fn retire(&self, ptr: *mut dyn Reclaim, deleter: &'static dyn Deleter) {
        // First, stick ptr onto the list of retired objects.
        let retired = Box::into_raw(Box::new(Retired {
            ptr,
            deleter,
            next: AtomicPtr::new(std::ptr::null_mut()),
        }));
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

impl Drop for HazPtrDomain {
    fn drop(&mut self) {
        todo!()
    }
}

struct HazPtrs {
    head: AtomicPtr<HazPtr>,
}

struct Retired {
    ptr: *mut dyn Reclaim,
    deleter: &'static dyn Deleter,
    next: AtomicPtr<Retired>,
}

struct RetiredList {
    head: AtomicPtr<Retired>,
    count: AtomicUsize,
}
