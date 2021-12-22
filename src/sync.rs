#[cfg(all(not(feature = "std"), loom))]
compile_error!("loom requires the standard library");

#[cfg(loom)]
pub(crate) mod atomic {
    pub(crate) use loom::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}
#[cfg(loom)]
pub(crate) use loom::thread::yield_now;

#[cfg(not(loom))]
pub(crate) mod atomic {
    pub(crate) use core::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}
#[cfg(all(not(loom), feature = "std"))]
pub(crate) use std::thread::yield_now;
