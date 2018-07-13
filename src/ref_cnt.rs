use std::marker::PhantomData;
use std::ptr;
use std::sync::Arc;

use super::{Debt, Guard};

pub unsafe trait RefCnt {
    type Base;
    type Guard;
    fn guard_from_debt(debt: Debt) -> Self::Guard;
    fn guard_upgrade(guard: &Self::Guard) -> Self;
    fn strip(me: Self) -> *mut Self::Base;
    unsafe fn from_ptr(ptr: *const Self::Base) -> Self;
    fn inc(me: &Self);
    unsafe fn dispose(ptr: *const Self::Base);
    fn as_raw(me: &Self) -> *mut Self::Base;
}

unsafe impl<T> RefCnt for Arc<T> {
    type Base = T;
    type Guard = Guard<Arc<T>>;
    fn guard_from_debt(debt: Debt) -> Guard<Arc<T>> {
        let ptr = debt.ptr() as *const T;

        Guard {
            debt,
            ptr,
            _arc: PhantomData,
        }
    }
    fn guard_upgrade(guard: &Guard<Arc<T>>) -> Arc<T> {
        Guard::upgrade(&guard)
    }
    fn strip(me: Arc<T>) -> *mut T {
        // The AtomicPtr requires *mut in its interface. We are more like *const, so we cast it.
        // However, we always go back to *const right away when we get the pointer on the other
        // side, so it should be fine.
        Arc::into_raw(me) as *mut T
    }
    unsafe fn from_ptr(ptr: *const T) -> Arc<T> {
        debug_assert!(!ptr.is_null());
        Arc::from_raw(ptr)
    }
    fn inc(me: &Arc<T>) {
        Arc::into_raw(Arc::clone(me));
    }
    unsafe fn dispose(ptr: *const T) {
        drop(Arc::from_raw(ptr));
    }
    fn as_raw(me: &Arc<T>) -> *mut T {
        me as &T as *const T as *mut T
    }
}

unsafe impl<T> RefCnt for Option<Arc<T>> {
    type Base = T;
    type Guard = Option<Guard<Arc<T>>>;
    fn guard_from_debt(debt: Debt) -> Option<Guard<Arc<T>>> {
        let ptr = debt.ptr() as *const T;
        if ptr.is_null() {
            None
        } else {
            Some(Arc::guard_from_debt(debt))
        }
    }
    fn guard_upgrade(guard: &Option<Guard<Arc<T>>>) -> Option<Arc<T>> {
        guard.as_ref().map(Arc::guard_upgrade)
    }
    fn strip(me: Option<Arc<T>>) -> *mut T {
        me.map(Arc::strip).unwrap_or_else(ptr::null_mut)
    }
    unsafe fn from_ptr(ptr: *const T) -> Option<Arc<T>> {
        if ptr.is_null() {
            None
        } else {
            Some(Arc::from_ptr(ptr))
        }
    }
    fn inc(me: &Self) {
        me.as_ref().map(Arc::inc);
    }
    unsafe fn dispose(ptr: *const T) {
        if !ptr.is_null() {
            Arc::dispose(ptr);
        }
    }
    fn as_raw(me: &Option<Arc<T>>) -> *mut T {
        me.as_ref().map(Arc::as_raw).unwrap_or_else(ptr::null_mut)
    }
}
