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

    let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(
        &domain,
        (42, CountDrops(Arc::clone(&drops_42))),
    ))));
    let y = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(
        &domain,
        (42, CountDrops(Arc::clone(&drops_42))),
    ))));

    // As a reader:
    let mut hazptr_array = HazardPointer::make_many_in_domain(&domain);

    // Safety:
    //
    //  1. AtomicPtr points to a Box, so is always valid.
    //  2. Writers to AtomicPtr use HazPtrObject::retire.
    let [one, two] = hazptr_array.hazard_pointers();
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
    // let _: i32 = my_y.0;
    // invalid:
    // let _: i32 = my_y.0;

    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 0);

    unsafe { HazPtrObjectWrapper::retire(x.into_inner(), &deleters::drop_box) };
    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 1);

    unsafe { HazPtrObjectWrapper::retire(y.into_inner(), &deleters::drop_box) };
    domain.eager_reclaim();
    assert_eq!(drops_42.load(Ordering::SeqCst), 2);
}

#[test]
fn feels_good() {
    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::new(Box::into_raw(Box::new(
        HazPtrObjectWrapper::with_global_domain((42, CountDrops(Arc::clone(&drops_42)))),
    )));

    // As a reader:
    let mut h = HazardPointer::make_global();

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

    let mut h = HazardPointer::make_global();
    let my_x = unsafe { h.protect(&x) }.expect("not null");

    let mut h_tmp = HazardPointer::make_global();
    let _ = unsafe { h_tmp.protect(&x) }.expect("not null");
    drop(h_tmp);

    // As a writer:
    let drops_9001 = Arc::new(AtomicUsize::new(0));
    let old = x.swap(
        Box::into_raw(Box::new(HazPtrObjectWrapper::with_global_domain((
            9001,
            CountDrops(Arc::clone(&drops_9001)),
        )))),
        std::sync::atomic::Ordering::SeqCst,
    );

    let mut h2 = HazardPointer::make_global();
    let my_x2 = unsafe { h2.protect(&x) }.expect("not null");

    assert_eq!(my_x.0, 42);
    assert_eq!(my_x2.0, 9001);

    // Safety:
    //
    //  1. The pointer came from Box, so is valid.
    //  2. The old value is no longer accessible.
    //  3. The deleter is valid for Box types.
    unsafe { HazPtrObjectWrapper::retire(old, &deleters::drop_box) };

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
}

#[test]
#[should_panic]
fn feels_bad() {
    let dw = Domain::new(&());
    let dr = Domain::new(&());

    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(
        &dw,
        (42, CountDrops(Arc::clone(&drops_42))),
    ))));

    // Reader uses a different domain thant the writer!
    let mut h = HazardPointer::make_in_domain(&dr);

    // Let's hope this catches the error (at least in debug mode).
    let _ = unsafe { h.protect(&x) }.expect("not null");
}

#[test]
fn drop_domain() {
    let domain = Domain::new(&());

    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(
        &domain,
        (42, CountDrops(Arc::clone(&drops_42))),
    ))));

    // As a reader:
    let mut h = HazardPointer::make_in_domain(&domain);
    let my_x = unsafe { h.protect(&x) }.expect("not null");
    // valid:
    assert_eq!(my_x.0, 42);

    // As a writer:
    let drops_9001 = Arc::new(AtomicUsize::new(0));
    let old = x.swap(
        Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(
            &domain,
            (9001, CountDrops(Arc::clone(&drops_9001))),
        ))),
        std::sync::atomic::Ordering::SeqCst,
    );

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    unsafe { HazPtrObjectWrapper::retire(old, &deleters::drop_box) };

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
    drop(domain);
}
