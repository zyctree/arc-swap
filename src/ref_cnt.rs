use std::marker::PhantomData;
use std::sync::Arc;

use super::Guard;
use super::debt::Debt;

pub unsafe trait RefCnt {
    type Base;
    type Guard;
    fn guard_from_debt(debt: Debt) -> Self::Guard;
    fn guard_upgrade(guard: &Self::Guard) -> Self;
    fn strip(me: Self) -> *mut Self::Base;
    fn from_null() -> Self;
    fn from_nonnull(ptr: *const Self::Base) -> Self;
    fn inc(me: &Self);
    fn dispose(ptr: *const Self::Base);
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
        Arc::into_raw(me) as *mut T
    }
    fn from_null() -> Arc<T> {
        unreachable!();
    }
    fn from_nonnull(ptr: *const T) -> Arc<T> {
        unsafe { Arc::from_raw(ptr) }
    }
    fn inc(me: &Arc<T>) {
        Arc::into_raw(Arc::clone(me));
    }
    fn dispose(ptr: *const T) {
        drop(unsafe { Arc::from_raw(ptr) });
    }
    fn as_raw(me: &Arc<T>) -> *mut T {
        me as &T as *const T as *mut T
    }
}
