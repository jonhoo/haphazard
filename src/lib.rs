#![feature(arbitrary_self_types)]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

use std::collections::HashSet;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize};

static SHARED_DOMAIN: HazPtrDomain = HazPtrDomain {
    hazptrs: HazPtrs {
        head: AtomicPtr::new(std::ptr::null_mut()),
    },
    retired: RetiredList {
        head: AtomicPtr::new(std::ptr::null_mut()),
        count: AtomicUsize::new(0),
    },
};

#[derive(Default)]
pub struct HazPtrHolder(Option<&'static HazPtr>);

impl HazPtrHolder {
    fn hazptr(&mut self) -> &'static HazPtr {
        if let Some(hazptr) = self.0 {
            hazptr
        } else {
            let hazptr = SHARED_DOMAIN.acquire();
            self.0 = Some(hazptr);
            hazptr
        }
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in AtomicPtr is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the AtomicPtr will only be deallocated
    /// through calls to [`HazPtrObject::retire`].
    pub unsafe fn load<'l, T>(&'l mut self, ptr: &'_ AtomicPtr<T>) -> Option<&'l T> {
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
                    unsafe { nn.as_ref() }
                });
            } else {
                ptr1 = ptr2;
            }
        }
    }

    pub fn reset(&mut self) {
        if let Some(hazptr) = self.0 {
            hazptr.ptr.store(std::ptr::null_mut(), Ordering::SeqCst);
        }
    }
}

impl Drop for HazPtrHolder {
    fn drop(&mut self) {
        self.reset();

        // Return self.0 to domain if Some
        if let Some(hazptr) = self.0 {
            hazptr.active.store(false, Ordering::SeqCst);
        }
    }
}

pub struct HazPtr {
    ptr: AtomicPtr<u8>,
    next: AtomicPtr<HazPtr>,
    active: AtomicBool,
}

impl HazPtr {
    fn protect(&self, ptr: *mut u8) {
        self.ptr.store(ptr, Ordering::SeqCst);
    }
}

pub trait Deleter {
    /// # Safety
    /// `ptr` must have been allocated by the corresponding allocation method.
    /// delete must be called at most once for each `ptr`.
    unsafe fn delete(&self, ptr: *mut dyn Drop);
}

impl Deleter for unsafe fn(*mut (dyn Drop + 'static)) {
    unsafe fn delete(&self, ptr: *mut dyn Drop) {
        unsafe { (*self)(ptr) }
    }
}

pub mod deleters {
    unsafe fn _drop_in_place(ptr: *mut dyn Drop) {
        // Safe by the contract on HazPtrObject::retire.
        unsafe { std::ptr::drop_in_place(ptr) };
    }

    /// Always safe to use given requirements on HazPtrObject::retire,
    /// but may lead to memory leaks if the pointer type itself needs drop.
    #[allow(non_upper_case_globals)]
    pub static drop_in_place: unsafe fn(*mut dyn Drop) = _drop_in_place;

    unsafe fn _drop_box(ptr: *mut dyn Drop) {
        // Safety: Safe by the safety gurantees of retire and because it's only used when
        // retiring Box objects.
        let _ = unsafe { Box::from_raw(ptr) };
    }

    /// # Safety
    ///
    /// Can only be used on values that were originally derived from a Box.
    #[allow(non_upper_case_globals)]
    pub static drop_box: unsafe fn(*mut dyn Drop) = _drop_box;
}

#[allow(drop_bounds)]
pub trait HazPtrObject
where
    Self: Sized + Drop + 'static,
{
    fn domain(&self) -> &HazPtrDomain;

    /// # Safety
    ///
    /// 1. Caller must guarantee that pointer is a valid reference.
    /// 2. Caller must guarantee that Self is no longer accessible to readers.
    /// 3. Caller must guarantee that the deleter is a valid deleter for Self.
    /// It is okay for existing readers to still refer to Self.
    ///   
    unsafe fn retire(self: *mut Self, deleter: &'static dyn Deleter) {
        if !std::mem::needs_drop::<Self>() {
            return;
        }
        unsafe { &*self }
            .domain()
            .retire(self as *mut dyn Drop, deleter);
    }
}

pub struct HazPtrObjectWrapper<T> {
    inner: T,
    // domain: HazPtrDomain,
}

impl<T> HazPtrObjectWrapper<T> {
    pub fn with_default_domain(t: T) -> Self {
        Self { inner: t }
    }
}

impl<T: 'static> HazPtrObject for HazPtrObjectWrapper<T> {
    fn domain(&self) -> &HazPtrDomain {
        &SHARED_DOMAIN
    }
}

// TODO: get rid of this requirement
impl<T> Drop for HazPtrObjectWrapper<T> {
    fn drop(&mut self) {}
}

impl<T> Deref for HazPtrObjectWrapper<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for HazPtrObjectWrapper<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

// Holds linked list of HazPtrs
pub struct HazPtrDomain {
    hazptrs: HazPtrs,
    retired: RetiredList,
}

impl HazPtrDomain {
    fn acquire(&self) -> &'static HazPtr {
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

    fn retire(&self, ptr: *mut dyn Drop, deleter: &'static dyn Deleter) {
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
            let mut n = unsafe { Box::from_raw(node) };
            node = *n.next.get_mut();

            if guarded_ptrs.contains(&(n.ptr as *mut u8)) {
                // Not safe to reclaim -- still guarded.
                *n.next.get_mut() = remaining;
                remaining = Box::into_raw(n);
                if tail.is_none() {
                    tail = Some(remaining);
                }
            } else {
                // No longer guarded -- reclaim using deleter.
                // Safety:
                // - `n.ptr` has not yet been dropped and will not be dropped again (we have removed it from `remaining`)
                // - `n.ptr` has been allocated the corresponding allocation method corresponding to `n.deleter`
                //   as per the safety guarantees of calling `retire`.
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
    ptr: *mut dyn Drop,
    deleter: &'static dyn Deleter,
    next: AtomicPtr<Retired>,
}

struct RetiredList {
    head: AtomicPtr<Retired>,
    count: AtomicUsize,
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::Arc;
    struct CountDrops(Arc<AtomicUsize>);
    impl Drop for CountDrops {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn feels_good() {
        let drops_42 = Arc::new(AtomicUsize::new(0));

        let x = AtomicPtr::new(Box::into_raw(Box::new(
            HazPtrObjectWrapper::with_default_domain((42, CountDrops(Arc::clone(&drops_42)))),
        )));

        // As a reader:
        let mut h = HazPtrHolder::default();

        // Safety:
        //
        //  1. AtomicPtr points to a Box, so is always valid.
        //  2. Writers to AtomicPtr use HazPtrObject::retire.
        let my_x = unsafe { h.load(&x) }.expect("not null");
        // valid:
        assert_eq!(my_x.0, 42);
        h.reset();
        // invalid:
        // let _: i32 = my_x.0;

        let my_x = unsafe { h.load(&x) }.expect("not null");
        // valid:
        assert_eq!(my_x.0, 42);
        drop(h);
        // invalid:
        // let _: i32 = my_x.0;

        let mut h = HazPtrHolder::default();
        let my_x = unsafe { h.load(&x) }.expect("not null");

        let mut h_tmp = HazPtrHolder::default();
        let _ = unsafe { h_tmp.load(&x) }.expect("not null");
        drop(h_tmp);

        // As a writer:
        let drops_9001 = Arc::new(AtomicUsize::new(0));
        let old = x.swap(
            Box::into_raw(Box::new(HazPtrObjectWrapper::with_default_domain((
                9001,
                CountDrops(Arc::clone(&drops_9001)),
            )))),
            std::sync::atomic::Ordering::SeqCst,
        );

        let mut h2 = HazPtrHolder::default();
        let my_x2 = unsafe { h2.load(&x) }.expect("not null");

        assert_eq!(my_x.0, 42);
        assert_eq!(my_x2.0, 9001);

        // Safety:
        //
        //  1. The pointer came from Box, so is valid.
        //  2. The old value is no longer accessible.
        //  3. The deleter is valid for Box types.
        unsafe { old.retire(&deleters::drop_box) };

        assert_eq!(drops_42.load(Ordering::SeqCst), 0);
        assert_eq!(my_x.0, 42);

        let n = SHARED_DOMAIN.eager_reclaim(false);
        assert_eq!(n, 0);

        assert_eq!(drops_42.load(Ordering::SeqCst), 0);
        assert_eq!(my_x.0, 42);

        drop(h);
        assert_eq!(drops_42.load(Ordering::SeqCst), 0);
        // _not_ drop(h2);

        let n = SHARED_DOMAIN.eager_reclaim(false);
        assert_eq!(n, 1);

        assert_eq!(drops_42.load(Ordering::SeqCst), 1);
        assert_eq!(drops_9001.load(Ordering::SeqCst), 0);

        drop(h2);
        let n = SHARED_DOMAIN.eager_reclaim(false);
        assert_eq!(n, 0);
        assert_eq!(drops_9001.load(Ordering::SeqCst), 0);
    }
}
