//! Hazard pointers for dynamic memory management in lock-free data structures.
//!
//! This library implements the [_hazard pointer memory reclamation mechanism_][hazptr],
//! specifically as proposed for the [C++ Concurrency Technical Specification][cts]. It is adapted
//! from the [implementation][folly-hazptr] found in Facebook's [Folly library][folly]. The initial
//! phases of implementation were all [live streamed].
//!
//! At a high level, hazard pointers provide a mechanism whereby readers of shared pointers can
//! prevent concurrent reclamation of the pointed-to objects by concurrent writers for as long as
//! the read operation is ongoing. When a writer removes an object from a data structure, it
//! instructs the hazard pointer library that said object is no longer reachable (that it is
//! _retired_), and that the library should eventually drop said object (_reclaim_ it) once it is
//! safe to do so. Readers, meanwhile, inform the library any time they wish to read through a
//! pointer shared with writers. Internally, the library notes down the address that was read in
//! such a way that it can ensure that if the pointed-to object is retired while the reader still
//! has access to it, it is not reclaimed. Only once the reader no longer has access to the read
//! pointer does the library allow the object to be reclaimed.
//!
//! [hazptr]: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.395.378&rep=rep1&type=pdf
//! [cts]: http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2021/p1121r3.pdf
//! [folly-hazptr]: https://github.com/facebook/folly/blob/main/folly/synchronization/Hazptr.h
//! [folly]: https://github.com/facebook/folly
//! [live streamed]: https://www.youtube.com/watch?v=fvcbyCYdR10&list=PLqbS7AVVErFgO7RUIC6lhd0UekFMbjJzb

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
