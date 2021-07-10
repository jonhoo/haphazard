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
fn feels_good() {
    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::new(Box::into_raw(Box::new(
        HazPtrObjectWrapper::with_global_domain((42, CountDrops(Arc::clone(&drops_42)))),
    )));

    // As a reader:
    let mut h = HazPtrHolder::global();

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

    let mut h = HazPtrHolder::global();
    let my_x = unsafe { h.load(&x) }.expect("not null");

    let mut h_tmp = HazPtrHolder::global();
    let _ = unsafe { h_tmp.load(&x) }.expect("not null");
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

    let mut h2 = HazPtrHolder::global();
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

    let n = HazPtrDomain::global().eager_reclaim(false);
    assert_eq!(n, 0);

    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    assert_eq!(my_x.0, 42);

    drop(h);
    assert_eq!(drops_42.load(Ordering::SeqCst), 0);
    // _not_ drop(h2);

    let n = HazPtrDomain::global().eager_reclaim(false);
    assert_eq!(n, 1);

    assert_eq!(drops_42.load(Ordering::SeqCst), 1);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 0);

    drop(h2);
    let n = HazPtrDomain::global().eager_reclaim(false);
    assert_eq!(n, 0);
    assert_eq!(drops_9001.load(Ordering::SeqCst), 0);
}

#[test]
#[should_panic]
fn feels_bad() {
    let dw = HazPtrDomain::new();
    let dr = HazPtrDomain::new();

    let drops_42 = Arc::new(AtomicUsize::new(0));

    let x = AtomicPtr::new(Box::into_raw(Box::new(HazPtrObjectWrapper::with_domain(
        &dw,
        (42, CountDrops(Arc::clone(&drops_42))),
    ))));

    // Reader uses a different domain thant the writer!
    let mut h = HazPtrHolder::for_domain(&dr);

    // Let's hope this catches the error (at least in debug mode).
    let _ = unsafe { h.load(&x) }.expect("not null");
}
