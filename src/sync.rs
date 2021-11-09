#[cfg(all(not(feature = "std"), loom))]
compile_error!("loom requires the standard library");

//loom support

#[cfg(loom)]
pub(crate) mod atomic {
    pub(crate) use loom::sync::atomic::{
        fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize, Ordering,
    };
}
#[cfg(loom)]
pub(crate) use loom::thread::yield_now;

//std imports

#[cfg(all(not(loom), feature = "std"))]
pub(crate) mod atomic {
    pub(crate) use std::sync::atomic::{
        fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize, Ordering,
    };
}
#[cfg(all(not(loom), feature = "std"))]
pub(crate) use std::thread::yield_now;

//both

#[cfg(any(loom, feature = "std"))]
pub(crate) mod marker {
    pub(crate) use std::marker::PhantomData;
}
#[cfg(any(loom, feature = "std"))]
pub(crate) mod ptr {
    pub(crate) use std::ptr::{null, null_mut, NonNull, drop_in_place};
}
#[cfg(any(loom, feature = "std"))]
pub(crate) mod mem {
    pub(crate) use std::mem::transmute;
}
#[cfg(any(loom, feature = "std"))]
pub(crate) mod boxed {
    pub(crate) use std::boxed::Box;
}
#[cfg(any(loom, feature = "std"))]
pub(crate) mod ops {
    pub(crate) use std::ops::{Deref, DerefMut};
}

//core imports

#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) mod atomic {
    pub(crate) use core::sync::atomic::{
        fence, AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize, Ordering,
    };
}

#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) fn yield_now() {
    //FIXME: What goes here?
}
#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) mod marker {
    pub(crate) use core::marker::PhantomData;
}
#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) mod ptr {
    pub(crate) use core::ptr::{null, null_mut, NonNull, drop_in_place};
}
#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) mod mem {
    pub(crate) use core::mem::transmute;
}
#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) mod boxed {
    pub(crate) use alloc::boxed::Box;
}
#[cfg(all(not(loom), not(feature = "std")))]
pub(crate) mod ops {
    pub(crate) use core::ops::{Deref, DerefMut};
}
