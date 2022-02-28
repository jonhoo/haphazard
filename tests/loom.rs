#![cfg(loom)]

use haphazard::*;

use loom::sync::{atomic::AtomicUsize, Mutex};
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

#[derive(Default, Debug)]
struct Count {
    ctors: std::sync::atomic::AtomicUsize,
    dtors: std::sync::atomic::AtomicUsize,
    retires: std::sync::atomic::AtomicUsize,
}

impl Count {
    fn test_local() -> &'static Count {
        Box::leak(Box::new(Self::default()))
    }

    fn clear(&self) {
        self.ctors.store(0, Ordering::Release);
        self.dtors.store(0, Ordering::Release);
        self.retires.store(0, Ordering::Release);
    }

    fn ctors(&self) -> usize {
        self.ctors.load(Ordering::SeqCst)
    }

    fn dtors(&self) -> usize {
        self.dtors.load(Ordering::SeqCst)
    }
}

#[allow(unused)]
struct Node {
    count: &'static Count,
    val: usize,
    next: AtomicPtr<Node>,
}

#[allow(dead_code)]
impl Node {
    fn new(count: &'static Count, val: usize, next: *mut Node) -> Self {
        count.ctors.fetch_add(1, Ordering::AcqRel);
        Self {
            count,
            val,
            next: unsafe { AtomicPtr::new(next) },
        }
    }

    fn value(&self) -> usize {
        self.val
    }

    fn next(&self) -> *const Node {
        self.next.load_ptr()
    }
}

impl Drop for Node {
    fn drop(&mut self) {
        self.count.dtors.fetch_add(1, Ordering::AcqRel);
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

        let x = Arc::new(AtomicPtr::from(Box::new((1, drops_1))));
        let y = Arc::new(AtomicPtr::from(Box::new((2, drops_2))));

        let (tx, rx) = loom::sync::mpsc::channel();
        let x1 = Arc::clone(&x);
        let y1 = Arc::clone(&y);
        let t1 = thread::spawn(move || {
            let mut hazptr_array = HazardPointer::many_in_domain(&domain);

            let [my_x, my_y] = unsafe { hazptr_array.protect_all([x1.as_std(), y1.as_std()]) };

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

        let old = unsafe { x.swap_ptr(std::ptr::null_mut()) }.expect("non-null");
        unsafe { old.retire_in(&domain) };
        domain.eager_reclaim();
        assert_eq!(ndrops_1.load(Ordering::SeqCst), 1);
        assert_eq!(ndrops_2.load(Ordering::SeqCst), 0);

        let old = unsafe { y.swap_ptr(std::ptr::null_mut()) }.expect("non-null");
        unsafe { old.retire_in(&domain) };
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

        let x = Arc::new(AtomicPtr::from(Box::new((42, drops_42))));

        let (tx, rx) = loom::sync::mpsc::channel();
        let x1 = Arc::clone(&x);
        let t1 = thread::spawn(move || {
            let mut h = HazardPointer::new();
            let my_x = unsafe { x1.load(&mut h) }.expect("not null");

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
        let old = x.swap(Box::new((9001, drops_9001))).expect("non-null");
        let n0 = unsafe { old.retire() };

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

        let x = Arc::new(AtomicPtr::from(Box::new((42, drops_42))));

        let (tx, rx) = loom::sync::mpsc::channel();
        let x1 = Arc::clone(&x);
        let tx1 = tx.clone();
        let t1 = thread::spawn(move || {
            let mut h = HazardPointer::new();
            let my_x = unsafe { x1.load(&mut h) }.expect("not null");

            // Now we can let the writer change things.
            tx1.send(()).unwrap();

            assert_eq!(ndrops_42_1.load(Ordering::SeqCst), 0);
            assert_eq!(my_x.0, 42);
        });
        let x2 = Arc::clone(&x);
        let tx2 = tx.clone();
        let t2 = thread::spawn(move || {
            let mut h = HazardPointer::new();
            let my_x = unsafe { x2.load(&mut h) }.expect("not null");

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
        let old = x.swap(Box::new((9001, drops_9001))).expect("non-null");
        let n0 = unsafe { old.retire() };

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

// This is `cleanup_test` from folly.
#[test]
fn folly_cleanup() {
    const THREAD_OPS: usize = 9;
    const MAIN_OPS: usize = 3;
    const NUM_THREADS: usize = 2;

    let count = Count::test_local();
    loom::model(move || {
        loom::lazy_static! {
            static ref D: Domain<()> = Domain::new(&());
        };

        count.clear();
        let main_done = Arc::new(Mutex::new(()));
        let main_not_done = main_done.lock();
        let threads_done = Arc::new(AtomicUsize::new(0));
        let threads: Vec<_> = (0..NUM_THREADS)
            .map(|tid| {
                let main_done = Arc::clone(&main_done);
                let threads_done = Arc::clone(&threads_done);
                thread::spawn(move || {
                    for j in (tid..THREAD_OPS).step_by(NUM_THREADS) {
                        let obj = Node::new(count, j, std::ptr::null_mut());
                        let p = Box::into_raw(Box::new(obj));
                        unsafe { D.retire_ptr::<_, Box<_>>(p) };
                    }
                    threads_done.fetch_add(1, Ordering::AcqRel);
                    let _ = main_done.lock();
                })
            })
            .collect();
        {
            for i in 0..MAIN_OPS {
                let obj = Node::new(count, i, std::ptr::null_mut());
                let p = Box::into_raw(Box::new(obj));
                unsafe { D.retire_ptr::<_, Box<_>>(p) };
            }
        }
        while threads_done.load(Ordering::Acquire) < NUM_THREADS {
            thread::yield_now();
        }
        assert_eq!(THREAD_OPS + MAIN_OPS, count.ctors());
        D.cleanup();
        assert_eq!(THREAD_OPS + MAIN_OPS, count.dtors());
        drop(main_not_done);
        for t in threads {
            t.join().unwrap();
        }
    })
}
