//! The [`AsRaw`](trait.AsRaw.html) trait.

use super::{Guard, RefCnt};

/// A trait describing types that can be turned into a raw pointer.
///
/// Some methods want to only borrow the pointer, so they don't need to consume the whole `Arc`.
/// this trait allows borrowing a raw pointer from both `Arc` and `Guard` (because `Guard` is in a
/// sense a short-term loan).
///
/// The `Borrow` trait is not used, because we want to allow null pointers as well here.
pub trait AsRaw<T> {
    /// Converts to raw pointer.
    fn as_raw(me: &Self) -> *const T;
}

impl<T: RefCnt> AsRaw<T::Base> for T {
    fn as_raw(me: &Self) -> *const T::Base {
        T::as_raw(me)
    }
}

impl<T: RefCnt> AsRaw<T::Base> for Guard<T> {
    fn as_raw(me: &Self) -> *const T::Base {
        &me as &T::Base as *const T::Base
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    /// Make sure both into_raw and our own as_raw act the same.
    #[test]
    fn as_raw_eq_into_raw() {
        let a = Arc::new(42);
        let ptr1 = AsRaw::as_raw(&a);
        let ptr2 = Arc::into_raw(a);
        assert_eq!(ptr1, ptr2);
        drop(unsafe { Arc::from_raw(ptr2) });
    }

    /// The same thing, but for ZSTs, because they sometime act strange.
    #[test]
    fn as_raw_eq_into_raw_zst() {
        let a = Arc::new(42);
        let ptr1 = AsRaw::as_raw(&a);
        let ptr2 = Arc::into_raw(a);
        assert_eq!(ptr1, ptr2);
        drop(unsafe { Arc::from_raw(ptr2) });
    }
}
