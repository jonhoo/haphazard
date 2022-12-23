//! Dynamic memory management for lock-free data structures.
//!
//! This library implements the [_hazard pointer memory reclamation mechanism_][hazptr],
//! specifically as proposed for the [C++ Concurrency Technical Specification][cts]. It is adapted
//! from the [implementation][folly-hazptr] found in Facebook's [Folly library][folly]. The initial
//! phases of implementation were all [live streamed].
//!
//! At a high level, hazard pointers provide a mechanism that allows readers of shared pointers to
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
//! TODO: Can also help with the ABA problem (ensure object isn't reused until there are no
//! pointers to it, so cannot "see" A again until there are no As left).
//!
//! For an overview of concurrent garbage collection with hazard pointers, see "_[Fearless
//! concurrency with hazard pointers]_". Aaron Turon post on "_[Lock-freedom without garbage
//! collection]_" which discusses the alternate approach of using epoch-based reclamation (see
//! below) is also a good reference.
//!
//! # High-level API structure
//!
//! TODO: Ref section 3 of [the proposal][cts] and [folly's docs][folly-hazptr].
//!
//! # Hazard pointers vs. other deferred reclamation mechanisms
//!
//! TODO: Ref sections 3.4 and 4 of [the proposal][cts] and [section from folly's
//! docs](https://github.com/facebook/folly/blob/594b7e770176003d0f6b4cf725dd02a09cba533c/folly/synchronization/Hazptr.h#L139).
//!
//! Note esp. [memory usage](https://github.com/facebook/folly/blob/594b7e770176003d0f6b4cf725dd02a09cba533c/folly/synchronization/Hazptr.h#L120).
//!
//! # Examples
//!
//! TODO: Ref section 5 of [the proposal][cts] and [example from folly's
//! docs](https://github.com/facebook/folly/blob/594b7e770176003d0f6b4cf725dd02a09cba533c/folly/synchronization/Hazptr.h#L76).
//!
//! ```
//! use haphazard::{AtomicPtr, Domain, HazardPointer};
//!
//! // First, create something that's intended to be concurrently accessed.
//! let x = AtomicPtr::from(Box::new(42));
//!
//! // All reads must happen through a hazard pointer, so make one of those:
//! let mut h = HazardPointer::new();
//!
//! // We can now use the hazard pointer to read from the pointer without
//! // worrying about it being deallocated while we read.
//! let my_x = x.safe_load(&mut h).expect("not null");
//! assert_eq!(*my_x, 42);
//!
//! // We can willingly give up the guard to allow writers to reclaim the Box.
//! h.reset_protection();
//! // Doing so invalidates the reference we got from .load:
//! // let _ = *my_x; // won't compile
//!
//! // Hazard pointers can be re-used across multiple reads.
//! let my_x = x.safe_load(&mut h).expect("not null");
//! assert_eq!(*my_x, 42);
//!
//! // Dropping the hazard pointer releases our guard on the Box.
//! drop(h);
//! // And it also invalidates the reference we got from .load:
//! // let _ = *my_x; // won't compile
//!
//! // Multiple readers can access a value at once:
//!
//! let mut h = HazardPointer::new();
//! let my_x = x.safe_load(&mut h).expect("not null");
//!
//! let mut h_tmp = HazardPointer::new();
//! let _ = x.safe_load(&mut h_tmp).expect("not null");
//! drop(h_tmp);
//!
//! // Writers can replace the value, but doing so won't reclaim the old Box.
//! let old = x.swap(Box::new(9001)).expect("not null");
//!
//! // New readers will see the new value:
//! let mut h2 = HazardPointer::new();
//! let my_x2 = x.safe_load(&mut h2).expect("not null");
//! assert_eq!(*my_x2, 9001);
//!
//! // And old readers can still access the old value:
//! assert_eq!(*my_x, 42);
//!
//! // The writer can retire the value old readers are seeing.
//! //
//! // Safety: this value has not been retired before.
//! unsafe { old.retire() };
//!
//! // Reads will continue to work fine, as they're guarded by the hazard.
//! assert_eq!(*my_x, 42);
//!
//! // Even if the writer actively tries to reclaim retired objects, the hazard makes readers safe.
//! let n = Domain::global().eager_reclaim();
//! assert_eq!(n, 0);
//! assert_eq!(*my_x, 42);
//!
//! // Only once the last hazard guarding the old value goes away will the value be reclaimed.
//! drop(h);
//! let n = Domain::global().eager_reclaim();
//! assert_eq!(n, 1);
//!
//! // Remember to also retire the item stored in the AtomicPtr when it's dropped
//! // (assuming of course that the pointer is not shared elsewhere):
//! unsafe { x.retire(); }
//! ```
//!
//! # Differences from the specification
//!
//! # Differences from the folly
//!
//! TODO: Note differences from spec and from folly. Among other things, see [this note from
//! folly](https://github.com/facebook/folly/blob/594b7e770176003d0f6b4cf725dd02a09cba533c/folly/synchronization/Hazptr.h#L193).
//!
//!
//! [hazptr]: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.395.378&rep=rep1&type=pdf
//! [cts]: http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2021/p1121r3.pdf
//! [folly-hazptr]: https://github.com/facebook/folly/blob/main/folly/synchronization/Hazptr.h
//! [folly]: https://github.com/facebook/folly
//! [live streamed]: https://www.youtube.com/watch?v=fvcbyCYdR10&list=PLqbS7AVVErFgO7RUIC6lhd0UekFMbjJzb
//! [Fearless concurrency with hazard pointers]: https://web.archive.org/web/20210306120313/https://ticki.github.io/blog/fearless-concurrency-with-hazard-pointers/
//! [Lock-freedom without garbage collection]: https://aturon.github.io/blog/2015/08/27/epoch/

// TODO: Incorporate doc strings around expectations from section 6 of the hazptr TS2 proposal.

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(missing_docs)]
#![warn(rustdoc::broken_intra_doc_links, rust_2018_idioms)]
#![allow(dead_code)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod domain;
mod hazard;
mod pointer;
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

/// Raw building blocks for managing hazard pointers.
pub mod raw {
    pub use crate::domain::Domain;
    /// Well-known domain families.
    pub mod families {
        pub use crate::domain::Global;
    }
    pub use crate::hazard::HazardPointer;
    pub use crate::pointer::{Pointer, Reclaim};
}

use core::marker::PhantomData;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ptr::NonNull;
use core::sync::atomic::Ordering;

pub use domain::Domain;
pub use domain::Global;
pub use domain::Singleton;
pub use hazard::{HazardPointer, HazardPointerArray};

/// A managed pointer type which can be safely shared between threads.
///
/// This type has the same in-memory representation as a [`std::sync::atomic::AtomicPtr`], but
/// provides additional functionality and stricter guarantees:
///
/// - `haphazard::AtomicPtr` can safely load `&T` directly, and ensure that the referenced `T` is
///   not deallocated until the `&T` is dropped, even in the presence of concurrent writers.
/// - All loads and stores on this type use `Acquire` and `Release` semantics.
///
/// **Note:** This type is only available on platforms that support atomic loads and stores of
/// pointers. Its size depends on the target pointer’s size.
///
/// # Basic usage
///
/// To construct one, use [`AtomicPtr::from`]:
///
/// ```rust
/// # use haphazard::AtomicPtr;
/// let ptr: AtomicPtr<usize> = AtomicPtr::from(Box::new(42));
///
/// // Remember to retire the item stored in the AtomicPtr when it's dropped
/// // (assuming of course that the pointer is not also shared elsewhere):
/// unsafe { ptr.retire(); }
/// ```
///
/// Note the explicit use of `AtomicPtr<usize>`, which is needed to get the default values for the
/// generic arguments `F` and `P`, the domain family and pointer types of the stored values.
/// Families are discussed in the documentation for [`Domain`]. The pointer type `P`, which must
/// implement [`raw::Pointer`], is the type originaly used to produce the stored pointer. This is
/// used to ensure that when writers drop a value, it is dropped using the appropriate `Drop`
/// implementation.
///
/// **Warning:** When this type is dropped, it does _not_ automatically retire the object it is
/// currently pointing to. In order to retire (and eventually reclaim) that object, use
/// [`AtomicPtr::retire`] or [`AtomicPtr::retire_in`].
///
// The unsafe constract enforced throughout this crate is that a given `AtomicPtr<T, F, P>` only
// ever holds the address of a valid `T` allocated through `P` from a domain with family `F`, or
// `null`. This generally means that there are a fair few safety constraints on _writes_ to an
// `AtomicPtr`, but very few safety constraints on _reads_. This is intentional, with the
// assumption being that most consumers will read in more places than they write.
//
// Also, when working with this code, keep in mind that `AtomicPtr<T>` does not _own_ its `T`. It
// is entirely possible for an application to have multiple `AtomicPtr<T>` that all point to the
// _same_ `T`. This is why most of the safety docs refer to "load from any AtomicPtr".
//
// TODO:
//  - copy_and_move test.
//  - requires double-retire protection?
#[repr(transparent)]
pub struct AtomicPtr<T, F = domain::Global, P = alloc::boxed::Box<T>>(
    crate::sync::atomic::AtomicPtr<T>,
    PhantomData<(F, *mut P)>,
);

// # Safety
//
// It's safe to give away ownership of an AtomicPtr to a different thread, because it holds no
// state that would be invalidated by giving ownership to another thread. Basically, this type is
// Sync because std::sync::atomic::AtomicPtr is Sync.
unsafe impl<T, F, P> Send for AtomicPtr<T, F, P> {}

// # Safety
//
// It's safe to share an AtomicPtr between threads, because it internally ensures that such
// accesses are correctly coordinated by using the atomic instructions of AtomicPtr. Furthermore,
// all the accessors of `AtomicPtr` that yield `&T` ensure that `T: Sync`, and any that retire `T`
// (and thus may take ownership of one) ensure that `T: Send`.
unsafe impl<T, F, P> Sync for AtomicPtr<T, F, P> {}

impl<T, F, P> core::fmt::Debug for AtomicPtr<T, F, P> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T, F, P> From<P> for AtomicPtr<T, F, P>
where
    P: raw::Pointer<T>,
{
    fn from(p: P) -> Self {
        Self(
            crate::sync::atomic::AtomicPtr::new(p.into_raw()),
            PhantomData,
        )
    }
}

impl<T, F, P> AtomicPtr<T, F, P> {
    /// Directly construct an `AtomicPtr` from a raw pointer.
    ///
    /// # Safety
    ///
    /// 1. `p` must reference a valid `T`, or be null.
    /// 2. `p` must have been allocated using the pointer type `P`.
    /// 3. `*p` must only be dropped through [`Domain::retire_ptr`].
    pub unsafe fn new(p: *mut T) -> Self {
        Self(crate::sync::atomic::AtomicPtr::new(p), PhantomData)
    }

    /// Directly access the "real" underlying `AtomicPtr`.
    ///
    /// # Safety
    ///
    /// If the stored pointer is modified, the new value must conform to the same safety
    /// requirements as the argument to [`AtomicPtr::new`].
    pub unsafe fn as_std(&self) -> &crate::sync::atomic::AtomicPtr<T> {
        &self.0
    }

    /// Directly access the "real" underlying `AtomicPtr` mutably.
    ///
    /// # Safety
    ///
    /// If the stored pointer is modified, the new value must conform to the same safety
    /// requirements as the argument to [`AtomicPtr::new`].
    pub unsafe fn as_std_mut(&mut self) -> &mut crate::sync::atomic::AtomicPtr<T> {
        &mut self.0
    }
}

/// A `*mut T` that was previously stored in an [`AtomicPtr`].
///
/// This type exists primarily to capture the family and pointer type of the [`AtomicPtr`] the
/// value was previously stored in, so that callers don't need to provide `F` and `P` to
/// [`Replaced::retire`] and [`Replaced::retire_in`].
///
/// This type has the same in-memory representation as a [`std::ptr::NonNull`](core::ptr::NonNull).
#[repr(transparent)]
pub struct Replaced<T, F, P> {
    ptr: NonNull<T>,
    _family: PhantomData<F>,
    _holder: PhantomData<P>,
}

impl<T, F, P> Clone for Replaced<T, F, P> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            _family: self._family,
            _holder: self._holder,
        }
    }
}
impl<T, F, P> Copy for Replaced<T, F, P> {}

impl<T, F, P> Deref for Replaced<T, F, P> {
    type Target = NonNull<T>;
    fn deref(&self) -> &Self::Target {
        &self.ptr
    }
}
impl<T, F, P> DerefMut for Replaced<T, F, P> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ptr
    }
}

impl<T, F, P> AsRef<NonNull<T>> for Replaced<T, F, P> {
    fn as_ref(&self) -> &NonNull<T> {
        &self.ptr
    }
}

impl<T, F, P> Replaced<T, F, P> {
    /// Extract the pointer originally stored in the [`AtomicPtr`].
    pub fn into_inner(self) -> NonNull<T> {
        self.ptr
    }
}

impl<T, F, P> core::fmt::Debug for Replaced<T, F, P> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.ptr.fmt(f)
    }
}

impl<T, P> Replaced<T, raw::families::Global, P>
where
    P: raw::Pointer<T>,
{
    /// Retire the referenced object, and reclaim it once it is safe to do so.
    ///
    /// `T` must be `Send` since it may be reclaimed by a different thread.
    ///
    /// # Safety
    ///
    /// 1. The pointed-to object will never again be returned by any [`AtomicPtr::load`].
    /// 2. The pointed-to object has not already been retired.
    pub unsafe fn retire(self) -> usize
    where
        T: Send,
    {
        // Safety:
        //
        // 1. Same as our caller requirement #1.
        // 2. Same as our caller requirement #2.
        // 3. Since there is exactly one Domain<Global>, we know that all calls to `load` that have
        //    returned this object must have been using the same (global) domain as we're retiring
        //    to.
        unsafe { self.retire_in(Domain::global()) }
    }
}

impl<T, F, P> Replaced<T, F, P>
where
    P: raw::Pointer<T>,
{
    /// Retire the referenced object, and reclaim it once it is safe to do so, through the given
    /// `domain`.
    ///
    /// `T` must be `Send` since it may be reclaimed by a different thread.
    ///
    /// # Safety
    ///
    /// 1. The pointed-to object will never again be returned by any [`AtomicPtr::load`].
    /// 2. The pointed-to object has not already been retired.
    /// 3. All calls to [`load`](AtomicPtr::load) that can have seen the pointed-to object were
    ///    using hazard pointers from `domain`.
    ///
    /// Note that requirement #3 is _partially_ enforced by the domain family (`F`), but it's on
    /// you to ensure that you don't "cross the streams" between multiple `Domain<F>`, if those can
    /// arise in your application.
    pub unsafe fn retire_in(self, domain: &Domain<F>) -> usize
    where
        T: Send,
    {
        // Safety:
        //
        // 1. implied by our #1 and #3: if load won't return it, there's no other way to guard it
        // 2. implied by our #2
        // 3. implied by AtomicPtr::new's #1 and #3
        let ptr = self.ptr.as_ptr();
        unsafe { domain.retire_ptr::<T, P>(ptr) }
    }
}

impl<T, F, P> AtomicPtr<T, F, P>
where
    F: Singleton,
{
    /// Loads the value from the stored pointer and guards it using the given hazard pointer.
    ///
    /// The guard ensures that the loaded `T` will remain valid for as long as you hold a reference
    /// to it.
    ///
    /// This method is only available for domains with _singleton families_, because
    /// implementations of the unsafe [`Singleton`] trait guarantee that there is only ever one
    /// instance of a [`Domain`] with the family in question, which in turn implies that loads and
    /// stores using such a family **must** be using the same (single) instance of that domain.
    pub fn safe_load<'hp, 'd>(&'_ self, hp: &'hp mut HazardPointer<'d, F>) -> Option<&'hp T>
    where
        T: Sync + 'hp,
        F: 'static,
    {
        // Safety: by the safety guarantees of Singleton there is exactly one domain of this
        // family, so we know that all calls to `load` that have returned this object must have
        // been using the same domain as we're retiring to.
        unsafe { self.load(hp) }
    }
}

impl<T, F, P> AtomicPtr<T, F, P> {
    /// Loads the value from the stored pointer and guards it using the given hazard pointer.
    ///
    /// The guard ensures that the loaded `T` will remain valid for as long as you hold a reference
    /// to it.
    ///
    /// # Safety
    ///
    /// All objects stored in this [`AtomicPtr`] are retired through the same [`Domain`] as the one
    /// that produced `hp`.
    ///
    /// This requirement is _partially_ enforced by the domain family (`F`), but it's on you to
    /// ensure that you don't "cross the streams" between multiple `Domain<F>`, if those can arise
    /// in your application.
    pub unsafe fn load<'hp, 'd>(&'_ self, hp: &'hp mut HazardPointer<'d, F>) -> Option<&'hp T>
    where
        T: Sync + 'hp,
        F: 'static,
    {
        unsafe { hp.protect(&self.0) }
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// # Safety
    ///
    /// If the stored pointer is modified, the new value must conform to the same safety
    /// requirements as the argument to [`AtomicPtr::new`].
    #[cfg(not(loom))]
    pub unsafe fn get_mut(&mut self) -> &mut *mut T {
        self.0.get_mut()
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data, and no loads can happen in the future.
    pub fn into_inner(self) -> *mut T {
        #[cfg(not(loom))]
        let ptr = self.0.into_inner();
        // Safety: we own self, so the atomic value is visible to no other threads.
        #[cfg(loom)]
        let ptr = unsafe { self.0.unsync_load() };
        ptr
    }
}

impl<T, P> AtomicPtr<T, raw::families::Global, P>
where
    P: raw::Pointer<T>,
{
    /// Retire the currently-referenced object, and reclaim it once it is safe to do so.
    ///
    /// `T` must be `Send` since it may be reclaimed by a different thread.
    ///
    /// # Safety
    ///
    /// 1. The currently-referenced object will never again be returned by any [`AtomicPtr::load`].
    /// 2. The currently-referenced object has not already been retired.
    pub unsafe fn retire(self) -> usize
    where
        T: Send,
    {
        // Safety:
        //
        // 1. Same as our caller requirement #1.
        // 2. Same as our caller requirement #2.
        // 3. Since there is exactly one Domain<Global>, we know that all calls to `load` that have
        //    returned this object must have been using the same (global) domain as we're retiring
        //    to.
        unsafe { self.retire_in(Domain::global()) }
    }
}

impl<T, F, P> AtomicPtr<T, F, P>
where
    P: raw::Pointer<T>,
{
    /// Retire the currently-referenced object, and reclaim it once it is safe to do so, through
    /// the given `domain`.
    ///
    /// `T` must be `Send` since it may be reclaimed by a different thread.
    ///
    /// # Safety
    ///
    /// 1. The currently-referenced object will never again be returned by any [`AtomicPtr::load`].
    /// 2. The currently-referenced object has not already been retired.
    /// 3. All calls to [`load`](AtomicPtr::load) that can have seen the currently-referenced
    ///    object were using hazard pointers from `domain`.
    ///
    /// Note that requirement #3 is _partially_ enforced by the domain family (`F`), but it's on
    /// you to ensure that you don't "cross the streams" between multiple `Domain<F>`, if those can
    /// arise in your application.
    pub unsafe fn retire_in(self, domain: &Domain<F>) -> usize
    where
        T: Send,
    {
        let ptr = self.into_inner();
        unsafe { domain.retire_ptr::<T, P>(ptr) }
    }

    /// Store an object into the pointer.
    ///
    /// Note, crucially, that this will _not_ automatically retire the pointer that's _currently_
    /// stored, which is why it is safe.
    pub fn store(&self, p: P) {
        let ptr = p.into_raw();
        // Safety (from AtomicPtr::new):
        //
        // #1 & #2 are both satisfied by virtue of `p` being of type `P`, which holds a valid `T`.
        // #3 is satisfied because the `P` is moved into `store`, and so can only be dropped
        // through the `unsafe` retire methods on `AtomicPtr`, all of which call
        // `Domain::retire_ptr`, or by dereferencing a raw pointer which is unsafe anyway.
        unsafe { self.store_ptr(ptr) }
    }

    /// Overwrite the currently stored pointer with the given one, and return the previous pointer.
    pub fn swap(&self, p: P) -> Option<Replaced<T, F, P>> {
        let ptr = p.into_raw();
        // Safety (from AtomicPtr::new):
        //
        // #1 & #2 are both satisfied by virtue of `p` being of type `P`, which holds a valid `T`.
        // #3 is satisfied because the `P` is moved into `store`, and so can only be dropped
        // through the `unsafe` retire methods on `AtomicPtr` and `Replaced`, all of which call
        // `Domain::retire_ptr`, or by dereferencing a raw pointer which is unsafe anyway.
        unsafe { self.swap_ptr(ptr) }
    }

    /// Stores an object into the pointer if the current pointer is `current`.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn compare_exchange(
        &self,
        current: *mut T,
        new: P,
    ) -> Result<Option<Replaced<T, F, P>>, P> {
        let new = new.into_raw();
        // Safety (from AtomicPtr::new):
        //
        // #1 & #2 are both satisfied by virtue of `p` being of type `P`, which holds a valid `T`.
        // #3 is satisfied because the `P` is moved into `store`, and so can only be dropped
        // through the `unsafe` retire methods on `AtomicPtr` and `Replaced`, all of which call
        // `Domain::retire_ptr`, or by dereferencing a raw pointer which is unsafe anyway.
        let r = unsafe { self.compare_exchange_ptr(current, new) };
        r.map_err(move |_ptr| {
            // TODO: Return `_ptr` to the caller somehow.
            // Adding this to the API is a breaking change, so we plan add this later at a more
            // convient time.
            // See: https://github.com/jonhoo/haphazard/pull/38#discussion_r901172203

            // Safety:
            // The swap failed, so still have exclusive access to `new` since it was never shared
            unsafe { P::from_raw(new) }
        })
    }

    /// Stores an object into the pointer if the current pointer is `current`.
    ///
    /// Unlike [`AtomicPtr::compare_exchange`], this function is allowed to spuriously fail even
    /// when the comparison succeeds, which can result in more efficient code on some platforms.
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn compare_exchange_weak(
        &self,
        current: *mut T,
        new: P,
    ) -> Result<Option<Replaced<T, F, P>>, P> {
        let new = new.into_raw();
        // Safety (from AtomicPtr::new):
        //
        // #1 & #2 are both satisfied by virtue of `p` being of type `P`, which holds a valid `T`.
        // #3 is satisfied because the `P` is moved into `store`, and so can only be dropped
        // through the `unsafe` retire methods on `AtomicPtr` and `Replaced`, all of which call
        // `Domain::retire_ptr`, or by dereferencing a raw pointer which is unsafe anyway.
        let r = unsafe { self.compare_exchange_weak_ptr(current, new) };
        r.map_err(move |_| {
            // Safety:
            // The swap failed, so still have exclusive access to `new` since it was never shared
            unsafe { P::from_raw(new) }
        })
    }
}

impl<T, F, P> AtomicPtr<T, F, P> {
    /// Loads the current pointer.
    pub fn load_ptr(&self) -> *mut T {
        self.0.load(Ordering::Acquire)
    }

    /// Overwrite the currently stored pointer with the given one.
    ///
    /// Note, crucially, that this will _not_ automatically retire the pointer that's _currently_
    /// stored.
    ///
    /// # Safety
    ///
    /// `ptr` must conform to the same safety requirements as the argument to [`AtomicPtr::new`].
    pub unsafe fn store_ptr(&self, ptr: *mut T) {
        self.0.store(ptr, Ordering::Release)
    }

    /// Overwrite the currently stored pointer with the given one, and return the previous pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must conform to the same safety requirements as the argument to [`AtomicPtr::new`].
    pub unsafe fn swap_ptr(&self, ptr: *mut T) -> Option<Replaced<T, F, P>> {
        let ptr = self.0.swap(ptr, Ordering::Release);
        NonNull::new(ptr).map(|ptr| Replaced {
            ptr,
            _family: PhantomData::<F>,
            _holder: PhantomData::<P>,
        })
    }

    /// Stores `new` if the current pointer is `current`.
    ///
    /// The return value is a result indicating whether the new pointer was written and containing
    /// the previous pointer. On success this value is guaranteed to be equal to `current`.
    ///
    /// # Safety
    ///
    /// `ptr` must conform to the same safety requirements as the argument to [`AtomicPtr::new`].
    pub unsafe fn compare_exchange_ptr(
        &self,
        current: *mut T,
        new: *mut T,
    ) -> Result<Option<Replaced<T, F, P>>, *mut T> {
        let ptr = self
            .0
            .compare_exchange(current, new, Ordering::Release, Ordering::Relaxed)?;
        Ok(NonNull::new(ptr).map(|ptr| Replaced {
            ptr,
            _family: PhantomData::<F>,
            _holder: PhantomData::<P>,
        }))
    }

    /// Stores `new` if the current pointer is `current`.
    ///
    /// Unlike [`AtomicPtr::compare_exchange_ptr`], this function is allowed to spuriously fail even
    /// when the comparison succeeds, which can result in more efficient code on some platforms.
    ///
    /// The return value is a result indicating whether the new pointer was written and containing
    /// the previous pointer. On success this value is guaranteed to be equal to `current`.
    ///
    /// # Safety
    ///
    /// `ptr` must conform to the same safety requirements as the argument to [`AtomicPtr::new`].
    pub unsafe fn compare_exchange_weak_ptr(
        &self,
        current: *mut T,
        new: *mut T,
    ) -> Result<Option<Replaced<T, F, P>>, *mut T> {
        let ptr =
            self.0
                .compare_exchange_weak(current, new, Ordering::Release, Ordering::Relaxed)?;
        Ok(NonNull::new(ptr).map(|ptr| Replaced {
            ptr,
            _family: PhantomData::<F>,
            _holder: PhantomData::<P>,
        }))
    }
}
