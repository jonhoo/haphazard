use crate::{Deleter, Domain, Reclaim};
use core::ops::{Deref, DerefMut};

pub trait HazPtrObject<'domain, F: 'static>
where
    Self: Sized + 'domain,
{
    fn domain(&self) -> &'domain Domain<F>;

    /// # Safety
    ///
    /// 1. Caller must guarantee that pointer is a valid reference.
    /// 2. Caller must guarantee that Self is no longer accessible to readers.
    /// 3. Caller must guarantee that the deleter is a valid deleter for Self.
    /// 4. Caller must guarantee that Self lives until the `Domain` is dropped.
    ///
    /// It is okay for existing readers to still refer to Self.
    ///   
    unsafe fn retire(self: *mut Self, deleter: &'static dyn Deleter) -> usize {
        let ptr = self as *mut (dyn Reclaim + 'domain);
        unsafe { (&*self).domain().retire(ptr, deleter) }
    }
}

pub struct HazPtrObjectWrapper<'domain, T, F> {
    inner: T,
    domain: &'domain Domain<F>,
}

impl<T> HazPtrObjectWrapper<'static, T, crate::Global> {
    pub fn with_global_domain(t: T) -> Self {
        HazPtrObjectWrapper::with_domain(Domain::global(), t)
    }
}

impl<'domain, T, F> HazPtrObjectWrapper<'domain, T, F> {
    pub fn with_domain(domain: &'domain Domain<F>, t: T) -> Self {
        Self { inner: t, domain }
    }
}

impl<'domain, T: 'domain, F: 'static> HazPtrObject<'domain, F>
    for HazPtrObjectWrapper<'domain, T, F>
{
    fn domain(&self) -> &'domain Domain<F> {
        self.domain
    }
}

impl<T, F> Deref for HazPtrObjectWrapper<'_, T, F> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T, F> DerefMut for HazPtrObjectWrapper<'_, T, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
