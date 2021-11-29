#[cfg(all(not(feature = "std"), loom))]
compile_error!("loom requires the standard library");

//loom support

#[cfg(loom)]
pub(crate) mod atomic {
    pub(crate) use loom::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}
#[cfg(loom)]
pub(crate) use loom::thread::yield_now;

//std imports

#[cfg(all(not(loom), feature = "std"))]
pub(crate) mod atomic {
    pub(crate) use std::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}
#[cfg(all(not(loom), feature = "std"))]
pub(crate) use std::thread::yield_now;

//core imports

#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) mod atomic {
    pub(crate) use core::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize};
}

#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) fn yield_now() {
    // XXX: this can be made better
    core::hint::spin_loop();
}
