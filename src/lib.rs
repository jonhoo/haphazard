#![feature(arbitrary_self_types)]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

mod deleter;
mod domain;
mod holder;
mod object;
mod ptr;

pub use deleter::{deleters, Deleter, Reclaim};
pub use domain::HazPtrDomain;
pub use holder::HazPtrHolder;
pub use object::{HazPtrObject, HazPtrObjectWrapper};
pub use ptr::HazPtr;
