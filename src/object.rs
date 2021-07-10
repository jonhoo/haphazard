use crate::{Deleter, HazPtrDomain, Reclaim};
use std::ops::{Deref, DerefMut};

pub trait HazPtrObject
where
    Self: Sized + 'static,
{
    fn domain(&self) -> &HazPtrDomain;

    /// # Safety
    ///
    /// 1. Caller must guarantee that pointer is a valid reference.
    /// 2. Caller must guarantee that Self is no longer accessible to readers.
    /// 3. Caller must guarantee that the deleter is a valid deleter for Self.
    /// It is okay for existing readers to still refer to Self.
    ///   
    unsafe fn retire(self: *mut Self, deleter: &'static dyn Deleter) {
        unsafe { &*self }
            .domain()
            .retire(self as *mut dyn Reclaim, deleter);
    }
}

pub struct HazPtrObjectWrapper<T> {
    inner: T,
    // domain: HazPtrDomain,
}

impl<T> HazPtrObjectWrapper<T> {
    pub fn with_default_domain(t: T) -> Self {
        Self { inner: t }
    }
}

impl<T: 'static> HazPtrObject for HazPtrObjectWrapper<T> {
    fn domain(&self) -> &HazPtrDomain {
        &crate::SHARED_DOMAIN
    }
}

impl<T> Deref for HazPtrObjectWrapper<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for HazPtrObjectWrapper<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
