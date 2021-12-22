#[cfg(all(not(feature = "std"), loom))]
compile_error!("loom requires the standard library");

#[cfg(loom)]
pub(crate) mod atomic {
    pub(crate) use loom::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}

#[cfg(not(loom))]
pub(crate) mod atomic {
    pub(crate) use core::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}
