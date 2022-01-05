//#![feature(arbitrary_self_types)]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod deleter;
mod domain;
mod holder;
mod object;
mod record;
mod sync;

fn asymmetric_light_barrier() {
    // TODO: if cfg!(linux) {
    // https://github.com/facebook/folly/blob/bd600cd4e88f664f285489c76b6ad835d8367cd2/folly/portability/Asm.h#L28
    crate::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
}

enum HeavyBarrierKind {
    Normal,
    Expedited,
}
fn asymmetric_heavy_barrier(_: HeavyBarrierKind) {
    // TODO: if cfg!(linux) {
    // https://github.com/facebook/folly/blob/bd600cd4e88f664f285489c76b6ad835d8367cd2/folly/synchronization/AsymmetricMemoryBarrier.cpp#L84
    crate::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
}

pub use deleter::{deleters, Deleter, Reclaim};
pub use domain::Domain;
pub use domain::Global;
pub use holder::HazardPointer;
pub use object::{HazPtrObject, HazPtrObjectWrapper};

pub(crate) use record::HazPtrRecord;
