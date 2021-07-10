#![feature(arbitrary_self_types)]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

mod deleter;
mod domain;
mod holder;
mod object;
mod ptr;

fn asymmetric_light_barrier() {
    // TODO: if cfg!(linux) {
    // https://github.com/facebook/folly/blob/bd600cd4e88f664f285489c76b6ad835d8367cd2/folly/portability/Asm.h#L28
    std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
}

enum HeavyBarrierKind {
    Normal,
    Expedited,
}
fn asymmetric_heavy_barrier(_: HeavyBarrierKind) {
    // TODO: if cfg!(linux) {
    // https://github.com/facebook/folly/blob/bd600cd4e88f664f285489c76b6ad835d8367cd2/folly/synchronization/AsymmetricMemoryBarrier.cpp#L84
    std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
}

pub use domain::Global;

pub use deleter::{deleters, Deleter, Reclaim};
pub use domain::HazPtrDomain;
pub use holder::HazPtrHolder;
pub use object::{HazPtrObject, HazPtrObjectWrapper};
pub use ptr::HazPtr;
