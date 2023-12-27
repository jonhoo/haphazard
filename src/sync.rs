#[cfg(all(not(feature = "std"), loom))]
compile_error!("loom requires the standard library");

#[cfg(loom)]
pub(crate) mod atomic {
    pub(crate) use loom::sync::atomic::{fence, AtomicIsize, AtomicPtr, AtomicUsize, Ordering};

    pub fn light_barrier() {
        fence(Ordering::SeqCst)
    }

    pub fn heavy_barrier() {
        fence(Ordering::SeqCst)
    }
}
#[cfg(loom)]
pub(crate) use loom::thread::yield_now;

#[cfg(not(loom))]
pub(crate) mod atomic {
    #[cfg(target_pointer_width = "64")]
    pub use core::sync::atomic::AtomicU64;
    pub(crate) use core::sync::atomic::{AtomicIsize, AtomicPtr, AtomicUsize, Ordering};

    #[cfg(miri)]
    pub fn light_barrier() {
        core::sync::atomic::fence(Ordering::SeqCst)
    }

    #[cfg(miri)]
    pub fn heavy_barrier() {
        core::sync::atomic::fence(Ordering::SeqCst)
    }

    #[cfg(not(miri))]
    pub fn light_barrier() {
        membarrier::light()
    }

    #[cfg(not(miri))]
    pub fn heavy_barrier() {
        membarrier::heavy()
    }
}
#[cfg(all(not(loom), feature = "std"))]
pub(crate) use std::thread::yield_now;
