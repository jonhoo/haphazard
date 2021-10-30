#[cfg(loom)]
pub(crate) mod atomic {
    pub(crate) use loom::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}

#[cfg(loom)]
pub(crate) use loom::thread::yield_now;

#[cfg(not(loom))]
pub(crate) mod atomic {
    pub(crate) use std::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}

#[cfg(not(loom))]
pub(crate) use std::thread::yield_now;
