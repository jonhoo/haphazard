use haphazard::*;

use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
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

    let x = AtomicPtr::from(Box::new((42, CountDrops(Arc::clone(&drops_42)))));
    let y = AtomicPtr::from(Box::new((42, CountDrops(Arc::clone(&drops_42)))));

    // As a reader:
    let mut hazptr_array = HazardPointer::many_in_domain(&domain);

    // Safety:
    //
    //  1. AtomicPtr points to a Box, so is always valid.
    //  2. Writers to AtomicPtr use HazPtrObject::retire.
    let [one, two] = hazptr_array.as_refs();
    // Safety: everything that touches x uses `domain`
    let my_x = unsafe { x.load(one).expect("not null") };
    let my_y = unsafe { y.load(two).expect("not null") };

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

    unsafe { x.retire_in(&domain) };
    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 1);

    unsafe { y.retire_in(&domain) };
    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 2);
}

#[test]
fn feels_good() {
    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::from(Box::new((42, CountDrops(Arc::clone(&drops_42)))));

    // As a reader:
    let mut h = HazardPointer::new();

    // Safety:
    //
    //  1. AtomicPtr points to a Box, so is always valid.
    //  2. Writers to AtomicPtr use HazPtrObject::retire.
    let my_x = x.safe_load(&mut h).expect("not null");
    // valid:
    assert_eq!(my_x.0, 42);
    h.reset_protection();
    // invalid:
    // let _: i32 = my_x.0;

    let my_x = x.safe_load(&mut h).expect("not null");
    // valid:
    assert_eq!(my_x.0, 42);
    drop(h);
    // invalid:
    // let _: i32 = my_x.0;

    let mut h = HazardPointer::new();
    let my_x = x.safe_load(&mut h).expect("not null");

    let mut h_tmp = HazardPointer::new();
    let _ = x.safe_load(&mut h_tmp).expect("not null");
    drop(h_tmp);

    // As a writer:
    let drops_9001 = Arc::new(AtomicUsize::new(0));
    let old = x
        .swap(Box::new((9001, CountDrops(Arc::clone(&drops_9001)))))
        .expect("not null");

    let mut h2 = HazardPointer::new();
    let my_x2 = x.safe_load(&mut h2).expect("not null");

    assert_eq!(my_x.0, 42);
    assert_eq!(my_x2.0, 9001);

    // Safety:
    //
    //  1. The pointer came from Box, so is valid.
    //  2. The old value is no longer accessible.
    //  3. The deleter is valid for Box types.
    unsafe { old.retire() };

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

    // Safety:
    //
    //  1. There are no other pointers to *x.
    //  2. We haven't already retired the swapped-in object.
    //  3. Only one domain is in use in this test, which is the only one with `x`.
    unsafe { x.retire() };

    let n = Domain::global().eager_reclaim();
    assert_eq!(n, 1);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 1);
}

#[test]
fn drop_domain() {
    let domain = Domain::new(&());

    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::from(Box::new((42, CountDrops(Arc::clone(&drops_42)))));

    // As a reader:
    let mut h = HazardPointer::new_in_domain(&domain);
    // Safety: everything touching `x` uses `domain`.
    let my_x = unsafe { x.load(&mut h).expect("not null") };
    // valid:
    assert_eq!(my_x.0, 42);

    // As a writer:
    let drops_9001 = Arc::new(AtomicUsize::new(0));
    let old = x
        .swap(Box::new((9001, CountDrops(Arc::clone(&drops_9001)))))
        .expect("not null");

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    unsafe { old.retire_in(&domain) };

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

    unsafe { x.retire_in(&domain) };
    drop(domain);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 1);
}
