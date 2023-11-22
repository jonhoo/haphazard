use haphazard::*;

use std::sync::atomic::Ordering;
use std::sync::atomic::{AtomicPtr, AtomicUsize};
use std::sync::Arc;

struct CountDrops(Arc<AtomicUsize>);
impl Drop for CountDrops {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn acquires_multiple() {
    let drops_42 = Arc::new(AtomicUsize::new(0));

    let domain = Domain::new(&());

    let x = AtomicPtr::new(Box::into_raw(Box::new((42, CountDrops(Arc::clone(&drops_42))))));
    let y = AtomicPtr::new(Box::into_raw(Box::new((42, CountDrops(Arc::clone(&drops_42))))));

    // As a reader:
    let mut hazptr_array = HazardPointer::many_in_domain(&domain);

    // Safety:
    //
    //  1. AtomicPtr points to a Box, so is always valid.
    //  2. Writers to AtomicPtr use HazPtrObject::retire.
    let [one, two] = hazptr_array.as_refs();
    let my_x = unsafe { one.protect(&x) }.expect("not null");
    let my_y = unsafe { two.protect(&y) }.expect("not null");

    // valid:
    assert_eq!(my_x.0, 42);
    assert_eq!(my_y.0, 42);

    hazptr_array.reset_protection();
    // invalid:
    // let _: i32 = my_x.0;
    // let _: i32 = my_y.0;

    let [my_x, my_y] = unsafe { hazptr_array.protect_all([&x, &y]) };

    let my_x = my_x.expect("not null");
    let my_y = my_y.expect("not null");

    // valid:
    assert_eq!(my_x.0, 42);
    assert_eq!(my_y.0, 42);

    drop(hazptr_array);
    // invalid:
    // let _: i32 = my_x.0;
    // invalid:
    // let _: i32 = my_y.0;

    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 0);

    unsafe { domain.retire_ptr::<_, Box<_>>(x.into_inner()) };
    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 1);

    unsafe { domain.retire_ptr::<_, Box<_>>(y.into_inner()) };
    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 2);
}

#[test]
fn feels_good() {
    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::new(Box::into_raw(Box::new((42, CountDrops(Arc::clone(&drops_42))))));

    // As a reader:
    let mut h = HazardPointer::new();

    // Safety:
    //
    //  1. AtomicPtr points to a Box, so is always valid.
    //  2. Writers to AtomicPtr use HazPtrObject::retire.
    let my_x = unsafe { h.protect(&x) }.expect("not null");
    // valid:
    assert_eq!(my_x.0, 42);
    h.reset_protection();
    // invalid:
    // let _: i32 = my_x.0;

    let my_x = unsafe { h.protect(&x) }.expect("not null");
    // valid:
    assert_eq!(my_x.0, 42);
    drop(h);
    // invalid:
    // let _: i32 = my_x.0;

    let mut h = HazardPointer::new();
    let my_x = unsafe { h.protect(&x) }.expect("not null");

    let mut h_tmp = HazardPointer::new();
    let _ = unsafe { h_tmp.protect(&x) }.expect("not null");
    drop(h_tmp);

    // As a writer:
    let drops_9001 = Arc::new(AtomicUsize::new(0));
    let old = x.swap(
        Box::into_raw(Box::new((9001, CountDrops(Arc::clone(&drops_9001))))),
        std::sync::atomic::Ordering::SeqCst,
    );

    let mut h2 = HazardPointer::new();
    let my_x2 = unsafe { h2.protect(&x) }.expect("not null");

    assert_eq!(my_x.0, 42);
    assert_eq!(my_x2.0, 9001);

    // Safety:
    //
    //  1. The pointer came from Box, so is valid.
    //  2. The old value is no longer accessible.
    //  3. The deleter is valid for Box types.
    unsafe { Domain::global().retire_ptr::<_, Box<_>>(old) };

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    let n = Domain::global().eager_reclaim();
    assert_eq!(n, 0);

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    drop(h);
    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    // _not_ drop(h2);

    let n = Domain::global().eager_reclaim();
    assert_eq!(n, 1);

    assert_eq!(drops_42.load(Ordering::SeqCst), 1);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 0);

    drop(h2);
    let n = Domain::global().eager_reclaim();
    assert_eq!(n, 0);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 0);

    unsafe { Domain::global().retire_ptr::<_, Box<_>>(x.into_inner()) };
    let n = Domain::global().eager_reclaim();
    assert_eq!(n, 1);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 1);
}

#[test]
fn drop_domain() {
    let domain = Domain::new(&());

    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::new(Box::into_raw(Box::new((42, CountDrops(Arc::clone(&drops_42))))));

    // As a reader:
    let mut h = HazardPointer::new_in_domain(&domain);
    let my_x = unsafe { h.protect(&x) }.expect("not null");
    // valid:
    assert_eq!(my_x.0, 42);

    // As a writer:
    let drops_9001 = Arc::new(AtomicUsize::new(0));
    let old = x.swap(
        Box::into_raw(Box::new((9001, CountDrops(Arc::clone(&drops_9001))))),
        std::sync::atomic::Ordering::SeqCst,
    );

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    unsafe { domain.retire_ptr::<_, Box<_>>(old) };

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    let n = domain.eager_reclaim();
    assert_eq!(n, 0);

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    h.reset_protection();
    let n = domain.eager_reclaim();
    assert_eq!(n, 1);
    assert_eq!(drops_42.load(Ordering::SeqCst), 1);

    drop(h);

    unsafe { domain.retire_ptr::<_, Box<_>>(x.into_inner()) };
    drop(domain);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 1);
}

#[non_exhaustive]
#[derive(Debug)]
struct Family;

#[test]
fn hazardptr_compare_exchange_fail() {
    // SAFETY: p is null
    let ptr: haphazard::AtomicPtr<u32, Family> =
        unsafe { haphazard::AtomicPtr::new(std::ptr::null_mut()) };

    let not_current = Box::into_raw(Box::new(0u32));

    let new = Box::new(0u32);
    let new_ptr = new.as_ref() as *const _;

    // This will fail and re-construct `new` as a box
    let result = ptr.compare_exchange_weak(not_current, new).unwrap_err();

    // Ensure we got `new` back
    assert_eq!(new_ptr, result.as_ref() as *const _);

    let _ = unsafe { Box::from_raw(not_current) };
}

#[test]
fn manual_validation() {
    struct Node {
        value: usize,
        next: haphazard::AtomicPtr<Self>,
    }

    // Let's imagine a data structure which has the following properties.
    //
    // 1. It always has exactly two nodes.
    // 2. A thread may change its contents by exchanging the `head` pointer with an another
    //    chain consisted of two nodes.
    // 3. After a successful `compare_exchange`, the thread retires popped nodes without unlinking
    //    the first and the second node.
    //
    // Note that the link between the first and the second node won't be changed
    // before the retirement! For this reason, to validate the protection for the second node,
    // one must reload the head pointer and confirm that it has not changed.
    let head =
        haphazard::AtomicPtr::from(Box::new(Node {
            value: 0,
            next: haphazard::AtomicPtr::from(Box::new(Node {
                value: 1,
                next: unsafe { haphazard::AtomicPtr::new(std::ptr::null_mut()) },
            })),
        }));

    const THREADS: usize = 8;
    const ITERS: usize = 512;

    std::thread::scope(|s| {
        for _ in 0..THREADS {
            s.spawn(|| {
                let mut hp1 = HazardPointer::default();
                let mut hp2 = HazardPointer::default();
                for _ in 0..ITERS {
                    loop {
                        let (n1, n2) = loop {
                            // The first node can be loaded in a conventional way.
                            let n1 = head.safe_load(&mut hp1).expect("The first node must exist");

                            let ptr = n1.next.load_ptr();
                            hp2.protect_raw(ptr);

                            // Synchronize with reclaimers.
                            asymmetric_light_barrier();

                            // Validate the second protection by reloading the head pointer.
                            if n1 as *const _ == head.load_ptr().cast_const() {
                                // Safety: Because the head pointer did not change,
                                // the two nodes are not retired, and the previous
                                // protection is valid!
                                let n2 = unsafe { &*ptr };
                                break (n1, n2);
                            }
                        };

                        let next = Box::new(Node {
                            value: n1.value + 1,
                            next: haphazard::AtomicPtr::from(Box::new(Node {
                                value: n2.value + 1,
                                next: unsafe { haphazard::AtomicPtr::new(std::ptr::null_mut()) },
                            })),
                        });
                        if head
                            .compare_exchange(n1 as *const _ as *mut Node, next)
                            .is_ok()
                        {
                            // Safety: As we won the race of exchanging the head node,
                            // they have not already been retired.
                            unsafe {
                                Domain::global()
                                    .retire_ptr::<_, Box<_>>(n1 as *const _ as *mut Node);
                                Domain::global()
                                    .retire_ptr::<_, Box<_>>(n2 as *const _ as *mut Node);
                            }
                            break;
                        }
                    }
                }
            });
        }
    });

    let n1 = unsafe { Box::from_raw(head.into_inner()) };
    let n2 = unsafe { Box::from_raw(n1.next.into_inner()) };
    assert_eq!(n1.value, THREADS * ITERS);
    assert_eq!(n2.value, THREADS * ITERS + 1);
}
