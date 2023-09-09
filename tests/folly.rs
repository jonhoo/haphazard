use haphazard::*;

use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicPtr, AtomicUsize};

#[derive(Default, Debug)]
pub struct Count {
    ctors: AtomicUsize,
    dtors: AtomicUsize,
    _retires: AtomicUsize,
}

#[cfg(miri)]
extern "Rust" {
    fn miri_static_root(ptr: *const u8);
}

impl Count {
    pub fn test_local() -> &'static Count {
        let ptr = Box::leak(Box::default());
        #[cfg(miri)]
        unsafe {
            miri_static_root(ptr as *const _ as *const u8);
        }
        ptr
    }

    pub fn ctors(&self) -> usize {
        self.ctors.load(Ordering::SeqCst)
    }

    pub fn dtors(&self) -> usize {
        self.dtors.load(Ordering::SeqCst)
    }
}

pub struct Node {
    count: &'static Count,
    val: usize,
    next: AtomicPtr<Node>,
}

impl Node {
    pub fn new(count: &'static Count, val: usize, next: *mut Node) -> Self {
        count.ctors.fetch_add(1, Ordering::AcqRel);
        Self {
            count,
            val,
            next: AtomicPtr::new(next),
        }
    }

    pub fn value(&self) -> usize {
        self.val
    }

    pub fn next(&self) -> *const Node {
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
        let x = Box::into_raw(Box::new(obj));
        unsafe { domain.retire_ptr::<_, Box<_>>(x) };
    }
    assert_eq!(num, count.ctors());
    domain.cleanup();
    assert_eq!(num, count.dtors());
}

#[test]
fn basic_holders() {
    {
        let _h = HazardPointer::new();
    }
    {
        let _h = HazardPointer::many::<2>();
    }
}

#[test]
fn basic_protection() {
    let count = Count::test_local();
    let domain = unique_domain!();
    let obj = Node::new(count, 0, std::ptr::null_mut());
    let obj = Box::into_raw(Box::new(obj));
    let mut h = HazardPointer::new_in_domain(&domain);
    h.protect_raw(obj);
    unsafe { domain.retire_ptr::<_, Box<_>>(obj) };
    assert_eq!(1, count.ctors());
    domain.cleanup();
    assert_eq!(0, count.dtors());
    h.reset_protection();
    domain.cleanup();
    assert_eq!(1, count.dtors());
}

// #[test]
// fn destruction() {
//     let domain = unique_domain!();
//     let dtors = Box::leak(Box::new(AtomicUsize::new(0)));
//
//     struct HeadRetireNext<'domain, F: 'static> {
//         next: *mut HazPtrObjectWrapper<'domain, Self, F>,
//         dtors: &'static AtomicUsize,
//     }
//
//     impl<F: 'static> Drop for HeadRetireNext<'_, F> {
//         fn drop(&mut self) {
//             self.dtors.fetch_add(1, Ordering::AcqRel);
//             if !self.next.is_null() {
//                 unsafe { domain.retire_ptr::<_, Box<_>>(self.next) };
//             }
//         }
//     }
//
//     let mut last = std::ptr::null_mut();
//     for _ in 0..2000 {
//         last = Box::into_raw(Box::new(HeadRetireNext { next: last, dtors }));
//     }
//     unsafe { domain.retire_ptr::<_, Box<_>>(last) };
//     domain.cleanup();
//     assert_eq!(2000, dtors.load(Ordering::SeqCst));
// }

#[test]
fn move_test() {
    // This test is mostly irrelevant in Rust, since there is no move constructor to check the
    // correctness of.
    let count = Count::test_local();
    let domain = unique_domain!();
    for i in 0..100 {
        let obj = Node::new(count, i, std::ptr::null_mut());
        let x = Box::into_raw(Box::new(obj));
        let mut hptr0 = HazardPointer::new_in_domain(&domain);
        hptr0.protect_raw(x);
        unsafe { domain.retire_ptr::<_, Box<_>>(x) };
        let hptr1 = hptr0;
        #[allow(clippy::redundant_locals)]
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
        let x = Box::into_raw(Box::new(obj));
        let mut hptr = HazardPointer::many_in_domain::<3>(&domain);
        let hptr = hptr.as_refs();
        hptr[2].protect_raw(x);
        unsafe { domain.retire_ptr::<_, Box<_>>(x) };
        // x is still protected from the call to protect_raw earlier.
        assert_eq!(unsafe { &*x }.val, i);
        hptr[2].reset_protection();
    }
    domain.cleanup();
}

// TODO: free_function_retire()

#[test]
fn array_part_of_cleanup() {
    let count = Count::test_local();
    let domain = unique_domain!();
    {
        let _h = HazardPointer::many_in_domain::<2>(&domain);
    }
    {
        let mut h = HazardPointer::many_in_domain::<2>(&domain);
        let p0 = Node::new(count, 0, std::ptr::null_mut());
        let p0 = Box::into_raw(Box::new(p0));
        let p1 = Node::new(count, 0, std::ptr::null_mut());
        let p1 = Box::into_raw(Box::new(p1));
        let h = h.as_refs();
        h[0].protect_raw(p0);
        h[1].protect_raw(p1);
        unsafe { domain.retire_ptr::<_, Box<_>>(p0) };
        unsafe { domain.retire_ptr::<_, Box<_>>(p1) };
    }
    assert_eq!(2, count.ctors());
    domain.cleanup();
    assert_eq!(2, count.dtors());
}
