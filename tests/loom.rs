#![cfg(loom)]

use haphazard::*;

use loom::sync::atomic::AtomicPtr;
use loom::thread;
use std::sync::atomic::Ordering;
use std::sync::Arc;

struct CountDrops(Arc<std::sync::atomic::AtomicUsize>);
impl CountDrops {
    pub fn new() -> Self {
        Self(Default::default())
    }

    pub fn counter(&self) -> Arc<std::sync::atomic::AtomicUsize> {
        Arc::clone(&self.0)
    }
}
impl Drop for CountDrops {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn acquires_multiple() {
    loom::model(|| {
        let drops_1 = CountDrops::new();
        let ndrops_1 = drops_1.counter();
        let drops_2 = CountDrops::new();
        let ndrops_2 = drops_2.counter();

        let domain = Domain::global();

        let x = Arc::new(AtomicPtr::new(Box::into_raw(Box::new(
            HazPtrObjectWrapper::with_domain(&domain, (1, drops_1)),
        ))));
        let y = Arc::new(AtomicPtr::new(Box::into_raw(Box::new(
            HazPtrObjectWrapper::with_domain(&domain, (2, drops_2)),
        ))));

        let (tx, rx) = loom::sync::mpsc::channel();
        let x1 = Arc::clone(&x);
        let y1 = Arc::clone(&y);
        let t1 = thread::spawn(move || {
            let mut hazptr_array = HazardPointer::make_many_in_domain(&domain);

            let [my_x, my_y] = unsafe { hazptr_array.protect_all([&x1, &y1]) };

            let my_x = my_x.expect("not null");
            let my_y = my_y.expect("not null");

            tx.send(()).unwrap();

            assert_eq!(my_x.0, 1);
            assert_eq!(my_y.0, 2);
        });

        let _ = rx.recv();

        domain.eager_reclaim();
        assert_eq!(ndrops_1.load(Ordering::SeqCst), 0);
        assert_eq!(ndrops_2.load(Ordering::SeqCst), 0);

        t1.join().unwrap();

        domain.eager_reclaim();
        assert_eq!(ndrops_1.load(Ordering::SeqCst), 0);
        assert_eq!(ndrops_2.load(Ordering::SeqCst), 0);

        unsafe { HazPtrObjectWrapper::retire(x.load(Ordering::SeqCst), &deleters::drop_box) };
        domain.eager_reclaim();
        assert_eq!(ndrops_1.load(Ordering::SeqCst), 1);
        assert_eq!(ndrops_2.load(Ordering::SeqCst), 0);

        unsafe { HazPtrObjectWrapper::retire(y.load(Ordering::SeqCst), &deleters::drop_box) };
        domain.eager_reclaim();
        assert_eq!(ndrops_1.load(Ordering::SeqCst), 1);
        assert_eq!(ndrops_2.load(Ordering::SeqCst), 1);
    })
}

#[test]
fn single_reader_protection() {
    loom::model(|| {
        let drops_42 = CountDrops::new();
        let ndrops_42_0 = drops_42.counter();
        let ndrops_42_1 = drops_42.counter();

        let x = Arc::new(AtomicPtr::new(Box::into_raw(Box::new(
            HazPtrObjectWrapper::with_global_domain((42, drops_42)),
        ))));

        let (tx, rx) = loom::sync::mpsc::channel();
        let x1 = Arc::clone(&x);
        let t1 = thread::spawn(move || {
            let mut h = HazardPointer::make_global();
            let my_x = unsafe { h.protect(&*x1) }.expect("not null");

            // Now we can let the writer change things.
            tx.send(()).unwrap();

            assert_eq!(ndrops_42_1.load(Ordering::SeqCst), 0);
            assert_eq!(my_x.0, 42);
        });

        // As a writer:

        // Wait until t1 has protected the value.
        let _ = rx.recv();

        let drops_9001 = CountDrops::new();
        let ndrops_9001 = drops_9001.counter();
        let old = x.swap(
            Box::into_raw(Box::new(HazPtrObjectWrapper::with_global_domain((
                9001, drops_9001,
            )))),
            std::sync::atomic::Ordering::SeqCst,
        );
        let n0 = unsafe { HazPtrObjectWrapper::retire(old, &deleters::drop_box) };

        let n1 = Domain::global().eager_reclaim();

        t1.join().unwrap();
        // Should now have reclaimed 42, but not 9001.
        let n2 = Domain::global().eager_reclaim();
        assert_eq!(n0 + n1 + n2, 1);
        assert_eq!(ndrops_42_0.load(Ordering::SeqCst), 1);
        assert_eq!(ndrops_9001.load(Ordering::SeqCst), 0);
    })
}

#[test]
fn multi_reader_protection() {
    loom::model(|| {
        let drops_42 = CountDrops::new();
        let ndrops_42_0 = drops_42.counter();
        let ndrops_42_1 = drops_42.counter();
        let ndrops_42_2 = drops_42.counter();

        let x = Arc::new(AtomicPtr::new(Box::into_raw(Box::new(
            HazPtrObjectWrapper::with_global_domain((42, drops_42)),
        ))));

        let (tx, rx) = loom::sync::mpsc::channel();
        let x1 = Arc::clone(&x);
        let tx1 = tx.clone();
        let t1 = thread::spawn(move || {
            let mut h = HazardPointer::make_global();
            let my_x = unsafe { h.protect(&*x1) }.expect("not null");

            // Now we can let the writer change things.
            tx1.send(()).unwrap();

            assert_eq!(ndrops_42_1.load(Ordering::SeqCst), 0);
            assert_eq!(my_x.0, 42);
        });
        let x2 = Arc::clone(&x);
        let tx2 = tx.clone();
        let t2 = thread::spawn(move || {
            let mut h = HazardPointer::make_global();
            let my_x = unsafe { h.protect(&*x2) }.expect("not null");

            // Now we can let the writer change things.
            tx2.send(()).unwrap();

            assert_eq!(ndrops_42_2.load(Ordering::SeqCst), 0);
            assert_eq!(my_x.0, 42);
        });

        // As a writer:

        // Wait until both threads have protected the value.
        let _ = rx.recv();
        let _ = rx.recv();

        let drops_9001 = CountDrops::new();
        let ndrops_9001 = drops_9001.counter();
        let old = x.swap(
            Box::into_raw(Box::new(HazPtrObjectWrapper::with_global_domain((
                9001, drops_9001,
            )))),
            std::sync::atomic::Ordering::SeqCst,
        );
        let n0 = unsafe { HazPtrObjectWrapper::retire(old, &deleters::drop_box) };

        let n1 = Domain::global().eager_reclaim();

        t1.join().unwrap();

        let n2 = Domain::global().eager_reclaim();

        t2.join().unwrap();

        let n3 = Domain::global().eager_reclaim();

        // Should now have reclaimed 42, but not 9001.
        assert_eq!(n0 + n1 + n2 + n3, 1);
        assert_eq!(ndrops_42_0.load(Ordering::SeqCst), 1);
        assert_eq!(ndrops_9001.load(Ordering::SeqCst), 0);
    })
}
