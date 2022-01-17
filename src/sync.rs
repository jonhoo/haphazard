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
    pub(crate) use core::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicUsize};
    #[cfg(target_pointer_width = "64")]
    pub use core::sync::atomic::AtomicU64;
}
#[cfg(all(not(loom), feature = "std"))]
pub(crate) use std::thread::yield_now;
