use crate::{HazPtr, SHARED_DOMAIN};
use std::sync::atomic::AtomicPtr;
use std::sync::atomic::Ordering;

#[derive(Default)]
pub struct HazPtrHolder(Option<&'static HazPtr>);

impl HazPtrHolder {
    fn hazptr(&mut self) -> &'static HazPtr {
        if let Some(hazptr) = self.0 {
            hazptr
        } else {
            let hazptr = SHARED_DOMAIN.acquire();
            self.0 = Some(hazptr);
            hazptr
        }
    }

    ///
    /// # Safety
    ///
    /// Caller must guarantee that the address in AtomicPtr is valid as a reference, or null.
    /// Caller must also guarantee that the value behind the AtomicPtr will only be deallocated
    /// through calls to [`HazPtrObject::retire`].
    pub unsafe fn load<'l, T>(&'l mut self, ptr: &'_ AtomicPtr<T>) -> Option<&'l T> {
        let hazptr = self.hazptr();
        let mut ptr1 = ptr.load(Ordering::SeqCst);
        loop {
            hazptr.protect(ptr1 as *mut u8);
            let ptr2 = ptr.load(Ordering::SeqCst);
            if ptr1 == ptr2 {
                // All good -- protected
                break std::ptr::NonNull::new(ptr1).map(|nn| {
                    // Safety: this is safe because:
                    //
                    //  1. Target of ptr1 will not be deallocated for the returned lifetime since
                    //     our hazard pointer is active and pointing at ptr1.
                    //  2. Pointer address is valid by the safety contract of load.
                    unsafe { nn.as_ref() }
                });
            } else {
                ptr1 = ptr2;
            }
        }
    }

    pub fn reset(&mut self) {
        if let Some(hazptr) = self.0 {
            hazptr.ptr.store(std::ptr::null_mut(), Ordering::SeqCst);
        }
    }
}

impl Drop for HazPtrHolder {
    fn drop(&mut self) {
        self.reset();

        // Return self.0 to domain if Some
        if let Some(hazptr) = self.0 {
            hazptr.active.store(false, Ordering::SeqCst);
        }
    }
}
