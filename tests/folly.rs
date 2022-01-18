use haphazard::*;

use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize};
use std::sync::Arc;

#[derive(Default, Debug)]
struct Count {
    ctors: AtomicUsize,
    dtors: AtomicUsize,
    retires: AtomicUsize,
}

impl Count {
    fn test_local() -> &'static Count {
        Box::leak(Box::new(Self::default()))
    }

    fn ctors(&self) -> usize {
        self.ctors.load(Ordering::SeqCst)
    }

    fn dtors(&self) -> usize {
        self.dtors.load(Ordering::SeqCst)
    }
}

struct Node {
    count: &'static Count,
    val: usize,
    next: AtomicPtr<Node>,
}

impl Node {
    fn new(count: &'static Count, val: usize, next: *mut Node) -> Self {
        count.ctors.fetch_add(1, Ordering::AcqRel);
        Self {
            count,
            val,
            next: AtomicPtr::new(next),
        }
    }

    fn value(&self) -> usize {
        self.val
    }

    fn next(&self) -> *const Node {
        self.next.load(Ordering::Acquire)
    }
}

impl Drop for Node {
    fn drop(&mut self) {
        self.count.dtors.fetch_add(1, Ordering::AcqRel);
    }
}

#[test]
fn basic_objects() {
    let count = Count::test_local();
    let domain = unique_domain!();
    let mut num = 0;
    {
        num += 1;
        let obj = Node::new(count, 0, std::ptr::null_mut());
        let x = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, obj)));
        unsafe { HazPtrObjectWrapper::retire(x, &deleters::drop_box) };
    }
    assert_eq!(num, count.ctors());
    domain.cleanup();
    assert_eq!(num, count.dtors());
}

#[test]
fn basic_holders() {
    {
        let _h = HazardPointer::make_global();
    }
    {
        let _h = HazardPointer::make_many_global::<2>();
    }
}

#[test]
fn basic_protection() {
    let count = Count::test_local();
    let domain = unique_domain!();
    let obj = Node::new(count, 0, std::ptr::null_mut());
    let obj = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, obj)));
    let mut h = HazardPointer::make_in_domain(&domain);
    unsafe { h.protect_raw(obj) };
    unsafe { HazPtrObjectWrapper::retire(obj, &deleters::drop_box) };
    assert_eq!(1, count.ctors());
    domain.cleanup();
    assert_eq!(0, count.dtors());
    h.reset_protection();
    domain.cleanup();
    assert_eq!(1, count.dtors());
}

#[test]
fn destruction() {
    let domain = unique_domain!();
    let dtors = Box::leak(Box::new(AtomicUsize::new(0)));

    struct HeadRetireNext<'domain, F: 'static> {
        next: *mut HazPtrObjectWrapper<'domain, Self, F>,
        dtors: &'static AtomicUsize,
    }

    impl<F: 'static> Drop for HeadRetireNext<'_, F> {
        fn drop(&mut self) {
            self.dtors.fetch_add(1, Ordering::AcqRel);
            if !self.next.is_null() {
                unsafe { HazPtrObjectWrapper::retire(self.next, &deleters::drop_box) };
            }
        }
    }

    let mut last = std::ptr::null_mut();
    for _ in 0..2000 {
        last = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(
            &domain,
            HeadRetireNext { next: last, dtors },
        )));
    }
    unsafe { HazPtrObjectWrapper::retire(last, &deleters::drop_box) };
    domain.cleanup();
    assert_eq!(2000, dtors.load(Ordering::SeqCst));
}

#[test]
fn move_test() {
    // This test is mostly irrelevant in Rust, since there is no move constructor to check the
    // correctness of.
    let count = Count::test_local();
    let domain = unique_domain!();
    for i in 0..100 {
        let obj = Node::new(count, i, std::ptr::null_mut());
        let x = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, obj)));
        let mut hptr0 = HazardPointer::make_in_domain(&domain);
        unsafe { hptr0.protect_raw(x) };
        unsafe { HazPtrObjectWrapper::retire(x, &deleters::drop_box) };
        let hptr1 = hptr0;
        let hptr1 = hptr1;
        let mut hptr2;
        hptr2 = hptr1;
        // x is still protected from the call to protect_raw earlier.
        assert_eq!(unsafe { &*x }.val, i);
        hptr2.reset_protection();
    }
    domain.cleanup();
}

#[test]
fn array() {
    let count = Count::test_local();
    let domain = unique_domain!();
    for i in 0..100 {
        let obj = Node::new(count, i, std::ptr::null_mut());
        let x = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, obj)));
        let mut hptr = HazardPointer::make_many_in_domain::<3>(&domain);
        let hptr = hptr.hazard_pointers();
        unsafe { hptr[2].protect_raw(x) };
        unsafe { HazPtrObjectWrapper::retire(x, &deleters::drop_box) };
        // x is still protected from the call to protect_raw earlier.
        assert_eq!(unsafe { &*x }.val, i);
        hptr[2].reset_protection();
    }
    domain.cleanup();
}

#[test]
fn free_function_retire() {
    let domain = unique_domain!();
    let foo = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, 0)));
    unsafe { HazPtrObjectWrapper::retire(foo, &deleters::drop_box) };
    let foo2 = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, 0)));
    unsafe fn _custom_drop(ptr: *mut (dyn Reclaim + 'static)) {
        let _ = Box::from_raw(ptr);
    }
    const CUSTOM_DROP: unsafe fn(*mut dyn Reclaim) = _custom_drop;
    unsafe { HazPtrObjectWrapper::retire(foo2, &CUSTOM_DROP) };

    // Third test just checks that dtor is called, which is already covered by other tests.
    // It is _not_ using a custom deleter/retirer.

    domain.cleanup();
}

#[test]
fn array_part_of_cleanup() {
    let count = Count::test_local();
    let domain = unique_domain!();
    {
        let _h = HazardPointer::make_many_in_domain::<2>(&domain);
    }
    {
        let mut h = HazardPointer::make_many_in_domain::<2>(&domain);
        let p0 = Node::new(count, 0, std::ptr::null_mut());
        let p0 = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, p0)));
        let p1 = Node::new(count, 0, std::ptr::null_mut());
        let p1 = Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(&domain, p1)));
        let h = h.hazard_pointers();
        unsafe { h[0].protect_raw(p0) };
        unsafe { h[1].protect_raw(p1) };
        unsafe { HazPtrObjectWrapper::retire(p0, &deleters::drop_box) };
        unsafe { HazPtrObjectWrapper::retire(p1, &deleters::drop_box) };
    }
    assert_eq!(2, count.ctors());
    domain.cleanup();
    assert_eq!(2, count.dtors());
}
