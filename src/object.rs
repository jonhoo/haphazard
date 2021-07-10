use crate::{Deleter, HazPtrDomain, Reclaim};
use std::ops::{Deref, DerefMut};

pub trait HazPtrObject<'domain>
where
    Self: Sized + 'domain,
{
    fn domain(&self) -> &'domain HazPtrDomain;

    /// # Safety
    ///
    /// 1. Caller must guarantee that pointer is a valid reference.
    /// 2. Caller must guarantee that Self is no longer accessible to readers.
    /// 3. Caller must guarantee that the deleter is a valid deleter for Self.
    /// 4. Caller must guarantee that Self lives until the `HazPtrDomain` is dropped.
    ///
    /// It is okay for existing readers to still refer to Self.
    ///   
    unsafe fn retire(self: *mut Self, deleter: &'static dyn Deleter) {
        let ptr = self as *mut (dyn Reclaim + 'domain);
        unsafe {
            (&*self).domain().retire(ptr, deleter);
        }
    }
}

pub struct HazPtrObjectWrapper<'domain, T> {
    inner: T,
    domain: &'domain HazPtrDomain,
}

impl<T> HazPtrObjectWrapper<'static, T> {
    pub fn with_global_domain(t: T) -> Self {
        HazPtrObjectWrapper::with_domain(HazPtrDomain::global(), t)
    }
}

impl<'domain, T> HazPtrObjectWrapper<'domain, T> {
    pub fn with_domain(domain: &'domain HazPtrDomain, t: T) -> Self {
        Self { inner: t, domain }
    }
}

impl<'domain, T: 'domain> HazPtrObject<'domain> for HazPtrObjectWrapper<'domain, T> {
    fn domain(&self) -> &'domain HazPtrDomain {
        self.domain
    }
}

impl<T> Deref for HazPtrObjectWrapper<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for HazPtrObjectWrapper<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
