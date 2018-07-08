#![doc(html_root_url = "https://docs.rs/arc-swap/0.1.4/arc-swap/", test(attr(deny(warnings))))]
#![deny(missing_docs)]

//! Making [`Arc`] itself atomic
//!
//! The [`Arc`] uses atomic reference counters, so the object behind it can be safely pointed to by
//! several threads at once. However, the [`Arc`] itself is quite ordinary ‒ to change its value
//! (make it point somewhere else), one has to be the sole owner of it (or store it behind a
//! [`Mutex`]).
//!
//! On the other hand, there's [`AtomicPtr`]. It can be modified and read from multiple threads,
//! allowing to pass the value from one thread to another without the use of a [`Mutex`]. The
//! downside is, tracking when the data can be safely deleted is hard.
//!
//! This library provides [`ArcSwap`](struct.ArcSwap.html) that allows both at once. It can be
//! constructed from ordinary [`Arc`], but its value can be loaded and stored atomically, by
//! multiple concurrent threads.
//!
//! # Motivation
//!
//! For one, the C++ [`shared_ptr`] has this
//! [ability](http://en.cppreference.com/w/cpp/memory/shared_ptr/atomic), so it is only fair to
//! have it too.
//!
//! For another, it seemed like a really good exercise.
//!
//! And finally, there are some real use cases for this functionality. For example, when one thread
//! publishes something (for example configuration) and other threads want to have a peek to the
//! current one from time to time. There's a global [`ArcSwap`](struct.ArcSwap.html), holding the
//! current snapshot and everyone is free to make a copy and hold onto it for a while. The
//! publisher thread simply stores a new snapshot every time and the old configuration gets dropped
//! once all the other threads give up their copies of the pointer.
//!
//! # Performance characteristics
//!
//! Benchmarks suggest this is slightly faster than a mutex in all cases, especially when there are
//! multiple concurrent readers.
//!
//! This implementation doesn't suffer from contention. Specifically, arbitrary number of readers
//! can access the shared value and won't block each other. There's however some slowdown in such
//! case (profiling will have to show the reason for that, in theory there should not be). The
//! performance of the writers degrades with the peak number of threads participating and in the
//! number of held references.
//!
//! In other words, both readers and writers are lock-free.
//!
//! Also, the Arc (and the data pointed to) are dropped right away when they stop being used by all
//! owners, and not some unspecified time in future like with a GC.
//!
//! # Orderings
//!
//! The library guarantees the orderings are strong enough to synchronize the data it points to. In
//! other words, store of a pointer is at least `Release` and a load is at least `Acquire` in case
//! the loaded pointer is non-null.
//!
//! Furthermore, each operation contains at least one `SeqCst` atomic operation, making the total
//! order of operations well defined and „sane“. In other words, if one thread makes two stores
//! `s1` and `s2` into two different `ArcSwap`s, if second threads observes `s2`, it must also see
//! `s1` at that time.
//!
//!
//! ```
//! extern crate arc_swap;
//! extern crate crossbeam_utils;
//!
//! use std::sync::Arc;
//!
//! use arc_swap::ArcSwap;
//! use crossbeam_utils::scoped;
//!
//!
//! fn main() {
//!     let a1 = ArcSwap::from(Arc::new(1));
//!     let a2 = ArcSwap::from(Arc::new(2));
//!     scoped::scope(|scope| {
//!         scope.spawn(|| {
//!             a1.store(Arc::new(42));
//!             a2.store(Arc::new(0));
//!         });
//!
//!         scope.spawn(|| {
//!             let v2 = a2.peek();
//!             let v1 = a1.peek();
//!
//!             if *v2 == 0 {
//!                 assert_eq!(42, *v1);
//!             }
//!         });
//!     });
//! }
//! ```
//!
//! # RCU
//!
//! This also offers an [RCU implementation](struct.ArcSwap.html#method.rcu), for read-heavy
//! situations. Note that the RCU update is considered relatively slow operation. In case there's
//! only one update thread, using [`store`](struct.ArcSwap.html#method.store) is enough.
//!
//! # Unix signal handlers
//!
//! Unix signals are hard to use correctly, partly because there is a very restricted set of
//! functions one might use inside them. Specifically, it is *not* allowed to use mutexes inside
//! them (because that could cause a deadlock).
//!
//! The library provides some methods that are safe to use in signal handlers. If they have the
//! [`AllocMode`](enum.AllocMode.html) parameter, `SignalSafe` variant must be used in such case.
//!
//! The safe methods are:
//! * [`peek_with_alloc`](struct.ArcSwap.html#method.peek_with_alloc)
//! * [`swap`](struct.ArcSwap.html#method.swap)
//! * [`store`](struct.ArcSwap.html#method.store)
//! * [`compare_and_swap`](struct.ArcSwap.html#method.compare_and_swap)
//! * [`Guard::upgrade`](struct.Guard.html#method.upgrade)
//!
//! Technically, the signal safe mode isn't fully lock-free and there's only limited number of
//! slots specifically reserved for signal handlers. Therefore it is advised to limit the number of
//! held references inside a signal handler.
//!
//! # Example
//!
//! ```rust
//! extern crate arc_swap;
//! extern crate crossbeam_utils;
//!
//! use std::sync::Arc;
//!
//! use arc_swap::ArcSwap;
//! use crossbeam_utils::scoped as thread;
//!
//! fn main() {
//!     let config = ArcSwap::from(Arc::new(String::default()));
//!     thread::scope(|scope| {
//!         scope.spawn(|| {
//!             let new_conf = Arc::new("New configuration".to_owned());
//!             config.store(new_conf);
//!         });
//!         for _ in 0..10 {
//!             scope.spawn(|| {
//!                 loop {
//!                     let cfg = config.load();
//!                     if !cfg.is_empty() {
//!                         assert_eq!(*cfg, "New configuration");
//!                         return;
//!                     }
//!                 }
//!             });
//!         }
//!     });
//! }
//! ```
//!
//! [`Arc`]: https://doc.rust-lang.org/std/sync/struct.Arc.html
//! [`AtomicPtr`]: https://doc.rust-lang.org/std/sync/atomic/struct.AtomicPtr.html
//! [`Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
//! [`shared_ptr`]: http://en.cppreference.com/w/cpp/memory/shared_ptr

pub mod as_raw;

mod debt;

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Arc;
use std::thread;

pub use debt::AllocMode;

use as_raw::AsRaw;
use debt::Debt;

// # Inner working
//
// The pointer itself is stored as AtomicPtr, which is converted from and to the Arc by into_raw
// and from_raw. The raw pointer in there holds one reference, it's only stored in a „dormant“
// state.
//
// Swapping would be fine ‒ the old one is taken out with its one reference and another one would
// go in with the reference. However, load is a bit worse ‒ it needs to create a new reference. But
// we first need to load the pointer itself and consequently increment the reference count in the
// pointer. There short time in between these two when the pointer is one reference short and if it
// got swapped out and dropped, it could get destroyed. We would then try to increment a ref count
// on a dead Arc, which is considered necromancy and UB.
//
// To work around this, we introduce a system of debts. If a pointer is owed a reference, it is
// stored into a global list. We load the pointer, store the debt and recheck the pointer is still
// valid. If it is, we know it is safe to operate on it, because it is kept alive. The load itself
// can pay the debt or the swap operation can (load pays its own, swap can pay for others) ‒ swap
// pays all the debts before giving the pointer to the caller. In this system, the total number of
// debts + strong count is equal or greater (and it is equal when all the debts are dealt with) to
// the real number of owners.
//
// The strong count never drops to 0 as long as the pointer is inside, so it can't be destroyed.
// When it leaves (through swap), all the debts are paid and turned into strong counts (sometimes
// multiple times, which'd get compensated for later, but that is an error in the safe direction),
// so it's up to the Arc itself to handle them and not create a dangling pointer.
//
// ## Unsafety
//
// This crate contains some amount of unsafe code. In all cases, it is to access raw pointers or to
// convert them into something safe Rust knows how to handle. There are two sources of the raw
// pointers.
//
// * Arcs. These are always originally created as Arc::into_raw and therefore can't produce
//   „garbage“. Therefore, we need to make sure these are not accessed after their lifetime ends ‒
//   and that's ensured by the debt system described above.
// * Nodes in the debt list. These are always converted from references. These nodes are never
//   freed, so there's no chance of creating dangling pointers.
//
// ## Atomic orderings
//
// (You probably want to study the code & comments in debt before going through this).
//
// Both load and swap (and related) contain at least one SeqCst operation on load-store atomic
// operation. That has full AcqRel semantic. In case of swap, it happens at the AtomicPtr itself.
// With load it happens a bit after the load (in writing the debt). Therefore, the data behind the
// pointer is fully synchronized through this ‒ the data is published in the swap and acquired by
// either another swap or load.
//
// As both the swap and writing of a new debt is SeqCst, their relative order is well defined.
// Therefore, a debt is created in one specific „interval“ specified by swaps. As the load happens
// on the same AtomicPtr as the swap, this is also well defined what happens before what.
// Therefore, we can be sure that both the debt and the confirmation load happen for the same
// „interval“. Furthermore, at the time of next swap, the swap will see all the debts from previous
// interval. A new debt must be created after (we showed above „after“ is well defined) and the
// load won't be able to confirm the original value. That leads to the swap knowing safely about
// what debts need to be paid.
//
// Even a relative ordering is enough to claim who pays for each one debt, because it happens on a
// single atomic.
//
// There are further orderings in linking new nodes into the debt list. All the ones that add there
// are Release, and all loads on the linked list are Acquire, making sure anyone able to observe
// the new value of the pointer can also see the data inside the nodes.
//
// There are few more relaxed orderings:
//
// * Resetting the global head without adding new nodes. This is OK, because all the nodes are
//   already „known“ to everyone by previous Release ordering and we don't care much if someone
//   reads the old or new value of the head ‒ this is just optimisation to make sure the beginning
//   doesn't get much more battering than the end and to distribute the ownership of nodes through
//   the linked list.
// * Failed compare_exchange orderings ‒ these don't have to synchronize anything, because they
//   made no changes and the one that succeeds will make the relevant change.
// * Loads of null pointers. But these don't need to synchronize any data.

/// A short-term proxy object from [`peek`](struct.ArcSwap.html#method.peek)
///
/// # Lifetime
///
/// Note that the `Guard` can outlive the `ArcSwap` it comes from. This is by design. Same as it is
/// possible to exchange the content of the `ArcSwap` with a `Guard` alive, it is possible to drop
/// the `ArcSwap` ‒ the `Arc` itself is kept alive as long as at least one `Guard` holds it.
pub struct Guard<T> {
    debt: Debt,
    ptr: *const T,
    _arc: PhantomData<Arc<T>>,
}

impl<T> Guard<T> {
    /// Upgrades the guard to a real `Arc`.
    ///
    /// This shares the reference count with all the `Arc` inside the corresponding `ArcSwap`. Use
    /// this if you need to hold the object for longer periods of time.
    ///
    /// See [`peek`](struct.ArcSwap.html#method.peek) for details.
    ///
    /// Note that this is associated function (so it doesn't collide with the thing pointed to):
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::sync::Arc;
    /// # use arc_swap::{ArcSwap, Guard};
    /// let a = ArcSwap::from(Arc::new(42));
    /// let mut ptr = None;
    /// { // limit the scope where the guard lives
    ///     let guard = a.peek();
    ///     if *guard > 40 {
    ///         ptr = Some(Guard::upgrade(&guard));
    ///     }
    /// }
    /// # let _ = ptr;
    /// ```
    pub fn upgrade(guard: &Self) -> Arc<T> {
        let arc = unsafe { Arc::from_raw(guard.ptr) };
        Arc::into_raw(Arc::clone(&arc));
        arc
    }
}

impl<T> Deref for Guard<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref().unwrap() }
    }
}

impl<T> Drop for Guard<T> {
    fn drop(&mut self) {
        if !self.debt.pay() {
            ArcSwap::<T>::dispose(self.ptr);
        }
    }
}

/// Turn the arc into a raw pointer.
fn strip<T>(arc: Arc<T>) -> *mut T {
    Arc::into_raw(arc) as *mut T
}

/// An atomic storage for [`Arc`].
///
/// This is a storage where an [`Arc`] may live. It can be read and written atomically from several
/// threads, but doesn't act like a pointer itself.
///
/// One can be created [`from`] an [`Arc`]. To get an [`Arc`] back, use the [`load`](#method.load)
/// method.
///
/// # Examples
///
/// ```rust
/// # use std::sync::Arc;
/// # use arc_swap::ArcSwap;
/// let arc = Arc::new(42);
/// let arc_swap = ArcSwap::from(arc);
/// assert_eq!(42, *arc_swap.load());
/// // It can be read multiple times
/// assert_eq!(42, *arc_swap.load());
///
/// // Put a new one in there
/// let new_arc = Arc::new(0);
/// assert_eq!(42, *arc_swap.swap(new_arc));
/// assert_eq!(0, *arc_swap.load());
/// ```
///
/// [`Arc`]: https://doc.rust-lang.org/std/sync/struct.Arc.html
/// [`from`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html#tymethod.from
pub struct ArcSwap<T> {
    // Notes: AtomicPtr needs Sized
    /// The actual pointer, extracted from the Arc.
    ptr: AtomicPtr<T>,

    /// We are basically an Arc in disguise. Inherit parameters from Arc by pretending to contain
    /// it.
    _phantom_arc: PhantomData<Arc<T>>,
}

impl<T> From<Arc<T>> for ArcSwap<T> {
    fn from(arc: Arc<T>) -> Self {
        // The AtomicPtr requires *mut in its interface. We are more like *const, so we cast it.
        // However, we always go back to *const right away when we get the pointer on the other
        // side, so it should be fine.
        let ptr = strip(arc);
        Self {
            ptr: AtomicPtr::new(ptr),
            _phantom_arc: PhantomData,
        }
    }
}

impl<T> Drop for ArcSwap<T> {
    fn drop(&mut self) {
        let ptr = *self.ptr.get_mut();
        // Note: the extract associated function pays all the debts on this. We are doing drop, so
        // this is the only instance here and therefore it is safe to assume more won't be created.
        // So Guards can live on.
        drop(Self::extract(ptr));
    }
}

impl<T> Clone for ArcSwap<T> {
    fn clone(&self) -> Self {
        Self::from(self.load())
    }
}

impl<T: Debug> Debug for ArcSwap<T> {
    fn fmt(&self, formatter: &mut Formatter) -> FmtResult {
        self.load().fmt(formatter)
    }
}

impl<T: Display> Display for ArcSwap<T> {
    fn fmt(&self, formatter: &mut Formatter) -> FmtResult {
        self.load().fmt(formatter)
    }
}

impl<T> ArcSwap<T> {
    /// Removes one reference from this pointer (or, the Arc belonging to this pointer).
    fn dispose(ptr: *const T) {
        drop(unsafe { Arc::from_raw(ptr) });
    }

    /// Increases the reference on the pointer and turns it into an Arc.
    ///
    /// If the debt was already paid by someone else, the reference is not increased.
    fn load_bump(ptr: *const T, mut debt: Debt) -> Arc<T> {
        let arc = unsafe { Arc::from_raw(ptr) };
        // Bump the reference count by one to cover the newly created Arc.
        if debt.active() {
            // We need to first increment it and then pay the debt. But that can have false
            // positive (paying it twice), so we need to compensate if that happens.
            Arc::into_raw(Arc::clone(&arc));
            if !debt.pay() {
                Self::dispose(ptr);
            }
        }
        arc
    }

    /// Loads the value.
    ///
    /// This makes another copy (reference) and returns it, atomically (it is safe even when other
    /// thread stores into the same instance at the same time).
    ///
    /// The method is lock-free.
    ///
    /// This method is *not* safe inside signal handlers. Use
    /// [`peek_with_alloc`](#method.peek_with_alloc) for that.
    pub fn load(&self) -> Arc<T> {
        Guard::upgrade(&self.peek())
    }

    /// Loans the value for a short time.
    ///
    /// This returns a temporary borrow of the object currently held inside. This is slightly
    /// faster than [`load`](#method.load), but it is not suitable for holding onto for longer
    /// periods of time.
    ///
    /// If you discover later on that you need to hold onto it for longer, you can
    /// [`Gruard::upgrade`](struct.Guard.html#method.upgrade) it.
    ///
    /// # Warning
    ///
    /// The performance of both reads and writes decrease with the (global) number of guards alive.
    /// Therefore, this is more suitable to have a one-time look into the data than storing in some
    /// data structures or doing extensive queries into the data. Prefer [`load`](#method.load) for
    /// that and store the actual `Arc` (which is *slightly* more expensive to get, but has no
    /// penalty to store).
    ///
    /// This method is *not* safe inside signal handlers. Use
    /// [`peek_with_alloc`](#method.peek_with_alloc) for that.
    pub fn peek(&self) -> Guard<T> {
        self.peek_with_alloc(AllocMode::Allowed)
    }

    /// Loans the value for a short time, with specified allocation mode.
    ///
    /// This acts like [`peek`](#method.peek.html), but allows specifying the [allocation
    /// mode](enum.AllocMode.html). The main usage is to allow using it inside signal handlers.
    pub fn peek_with_alloc(&self, alloc_mode: AllocMode) -> Guard<T> {
        // We can do Relaxed here, the debt contains SeqCst one and will therefore load the other
        // data properly. Well, with the exception the pointer is null, but then there's nothing to
        // synchronize.
        //
        // TODO: Once we support nulls, put a SeqCst barrier here, because the debt will be skipped
        // and we promised at least one SeqCst operation.
        let debt = Debt::confirmed(alloc_mode, || self.ptr.load(Ordering::Relaxed) as usize);
        let ptr = debt.ptr() as *const T;

        Guard {
            debt,
            ptr,
            _arc: PhantomData,
        }
    }

    /// Replaces the value inside this instance.
    ///
    /// Further loads will yield the new value. Uses [`swap`](#method.swap) internally.
    pub fn store(&self, arc: Arc<T>) {
        drop(self.swap(arc));
    }

    /// Takes the raw pointer, pays all the debt related to it and turns it into an `Arc`.
    ///
    /// This is a helper function for things like `swap`, when the inner pointer is being
    /// extracted and leaves the `ArcSwap`.
    fn extract(old: *const T) -> Arc<T> {
        let old_ptr = old as usize;
        let old_arc = unsafe { Arc::from_raw(old) };
        let inc = || {
            Arc::into_raw(Arc::clone(&old_arc));
        };
        // Pre-charge (the pay_all pays after claiming a debt, which is wrong ‒ we need to pay
        // upfront to stay safe.
        inc();
        Debt::pay_all(old_ptr, inc);
        // We create a new Arc here. The `old_arc` will be dropped on the exit of the function,
        // returning back the pre-charge.
        unsafe { Arc::from_raw(old) }
    }

    /// Exchanges the value inside this instance.
    pub fn swap(&self, arc: Arc<T>) -> Arc<T> {
        let new = strip(arc);
        // AcqRel needed to publish the target of the new pointer and get the target of the old
        // one.
        //
        // SeqCst to synchronize the time lines with the debts ‒ this takes a „snapshot“ (we'll see
        // debt no older than when this change happens).
        let old = self.ptr.swap(new, Ordering::SeqCst);
        Self::extract(old)
    }

    /// Swaps the stored Arc if it is equal to `current`.
    ///
    /// If the current value of the `ArcSwap` is equal to `current`, the `new` is stored inside. If
    /// not, nothing happens.
    ///
    /// The previous value is returned. It can be used to check if the change actually happened.
    ///
    /// In other words, if the caller „guesses“ the value of current correctly, it acts like
    /// [`swap`](#method.swap), otherwise it acts like [`load`](#method.load) (including the
    /// limitations).
    ///
    /// The previous can be either an `Arc` or a [`Guard`](struct.Guard.html) returned by
    /// [`peek`](#method.peek).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use arc_swap::{AllocMode, ArcSwap};
    ///
    /// let arc = Arc::new(42);
    /// let arc_swap = ArcSwap::from(Arc::clone(&arc));
    /// let another = Arc::new(0);
    ///
    /// let orig = arc_swap.compare_and_swap(&another, Arc::clone(&another), AllocMode::Allowed);
    /// assert!(Arc::ptr_eq(&arc, &orig));
    /// assert_eq!(42, *arc_swap.peek());
    ///
    /// let orig = arc_swap.compare_and_swap(&arc, another, AllocMode::Allowed);
    /// assert!(Arc::ptr_eq(&arc, &orig));
    /// assert_eq!(0, *arc_swap.peek());
    /// ```
    pub fn compare_and_swap<C: AsRaw<T>>(
        &self,
        current: &C,
        new: Arc<T>,
        alloc_mode: AllocMode,
    ) -> Arc<T> {
        let current = current.as_raw() as *mut _;
        let new = strip(new);
        // We may want to share the debt between iterations...
        let mut debt_store: Option<Debt> = None;

        'outer: loop {
            // In case we succeed, we want SeqCst to act like a swap.
            let previous = self.ptr.compare_and_swap(current, new, Ordering::SeqCst);
            let swapped = current == previous;

            if swapped {
                if let Some(mut debt) = debt_store {
                    // A debt was left from previous iteration.
                    // We didn't actually need the debt, so get rid of it.
                    // (this is a rare corner case ‒ the first CAS failed, but the second succeeded
                    // in replacing).
                    if !debt.pay() {
                        // Someone already paid the debt… that nobody needed :-|
                        Self::dispose(debt.ptr() as *const _);
                    }
                }
                // New went into us, so leave it at that
                return Self::extract(previous);
            } else {
                let mut debt =
                    debt_store.unwrap_or_else(|| Debt::new(previous as usize, alloc_mode));
                let mut previous = previous;
                loop {
                    // This works the same as Relaxed in load, it relies on the SeqCst in the Debt
                    // allocation.
                    let confirm = self.ptr.load(Ordering::Relaxed);
                    if confirm == previous {
                        Self::dispose(new);
                        return Self::load_bump(previous, debt);
                    } else if confirm == current {
                        // There's a chance the next attempt at CAS would succeed, retry the whole
                        // thing. But keep the debt around.
                        debt_store = Some(debt);
                        continue 'outer;
                    } else if debt.replace(confirm as usize) {
                        // We have a new pointer to confirm, retry.
                        previous = confirm;
                    } else {
                        // The debt was paid before we saw the new one, so we are safe using it.
                        Self::dispose(new);
                        return Self::load_bump(previous, debt);
                    }
                }
            }
        }
    }

    /// Read-Copy-Update of the pointer inside.
    ///
    /// This is useful in read-heavy situations with several threads that sometimes update the data
    /// pointed to. The readers can just repeatedly use the [`peek`](#method.peek) without any
    /// locking. The writer uses this method to perform the update.
    ///
    /// In case there's only one thread that does updates or in case the next version is
    /// independent of the previous one, simple [`swap`](#method.swap) or [`store`](#method.store)
    /// is enough. Otherwise, it may be needed to retry the update operation if some other thread
    /// made an update in between. This is what this method does.
    ///
    /// # Signal safety
    ///
    /// This method is *not* safe to use inside signal handlers.
    ///
    /// # Examples
    ///
    /// This will *not* work as expected, because between loading and storing, some other thread
    /// might have updated the value.
    ///
    /// ```rust
    /// extern crate arc_swap;
    /// extern crate crossbeam_utils;
    ///
    /// use std::sync::Arc;
    ///
    /// use arc_swap::ArcSwap;
    /// use crossbeam_utils::scoped as thread;
    ///
    /// fn main() {
    ///     let cnt = ArcSwap::from(Arc::new(0));
    ///     thread::scope(|scope| {
    ///         for _ in 0..10 {
    ///             scope.spawn(|| {
    ///                 let inner = cnt.load();
    ///                 let updated = *inner + 1;
    ///                 // Another thread might have stored some other number than what we have
    ///                 // between the load and store.
    ///                 cnt.store(Arc::new(updated));
    ///             });
    ///         }
    ///     });
    ///     // This will likely fail:
    ///     // assert_eq!(10, *cnt.load());
    /// }
    /// ```
    ///
    /// This will, but it can call the closure multiple times to do retries:
    ///
    /// ```rust
    /// extern crate arc_swap;
    /// extern crate crossbeam_utils;
    ///
    /// use std::sync::Arc;
    ///
    /// use arc_swap::ArcSwap;
    /// use crossbeam_utils::scoped as thread;
    ///
    /// fn main() {
    ///     let cnt = ArcSwap::from(Arc::new(0));
    ///     thread::scope(|scope| {
    ///         for _ in 0..10 {
    ///             scope.spawn(|| cnt.rcu(|inner| **inner + 1));
    ///         }
    ///     });
    ///     assert_eq!(10, *cnt.load());
    /// }
    /// ```
    ///
    /// Due to the retries, you might want to perform all the expensive operations *before* the
    /// rcu. As an example, if there's a cache of some computations as a map, and the map is cheap
    /// to clone but the computations are not, you could do something like this:
    ///
    /// ```rust
    /// extern crate arc_swap;
    /// extern crate crossbeam_utils;
    /// #[macro_use]
    /// extern crate lazy_static;
    ///
    /// use std::collections::HashMap;
    /// use std::sync::Arc;
    ///
    /// use arc_swap::ArcSwap;
    ///
    /// fn expensive_computation(x: usize) -> usize {
    ///     x * 2 // Let's pretend multiplication is really expensive
    /// }
    ///
    /// type Cache = HashMap<usize, usize>;
    ///
    /// lazy_static! {
    ///     static ref CACHE: ArcSwap<Cache> = ArcSwap::from(Arc::new(HashMap::new()));
    /// }
    ///
    /// fn cached_computation(x: usize) -> usize {
    ///     let cache = CACHE.load();
    ///     if let Some(result) = cache.get(&x) {
    ///         return *result;
    ///     }
    ///     // Not in cache. Compute and store.
    ///     // The expensive computation goes outside, so it is not retried.
    ///     let result = expensive_computation(x);
    ///     CACHE.rcu(|cache| {
    ///         // The cheaper clone of the cache can be retried if need be.
    ///         let mut cache = HashMap::clone(cache);
    ///         cache.insert(x, result);
    ///         cache
    ///     });
    ///     result
    /// }
    ///
    /// fn main() {
    ///     assert_eq!(42, cached_computation(21));
    ///     assert_eq!(42, cached_computation(21));
    /// }
    /// ```
    ///
    /// # The cost of cloning
    ///
    /// Depending on the size of cache above, the cloning might not be as cheap. You can however
    /// use persistent data structures ‒ each modification creates a new data structure, but it
    /// shares most of the data with the old one. Something like
    /// [`rpds`](https://crates.io/crates/rpds) or [`im`](https://crates.io/crates/im) might do
    /// what you need.
    pub fn rcu<R, F>(&self, mut f: F) -> Arc<T>
    where
        F: FnMut(&Arc<T>) -> R,
        R: Into<Arc<T>>,
    {
        let mut cur = self.load();
        loop {
            let new = f(&cur).into();
            let prev = self.compare_and_swap(&cur, new, AllocMode::Allowed);
            let swapped = Arc::ptr_eq(&cur, &prev);
            if swapped {
                return prev;
            } else {
                cur = prev;
            }
        }
    }

    /// An [`rcu`](#method.rcu) which waits to be the sole owner of the original value and unwraps
    /// it.
    ///
    /// This one works the same way as the [`rcu`](#method.rcu) method, but works on the inner type
    /// instead of `Arc`. After replacing the original, it waits until there are no other owners of
    /// the arc and unwraps it.
    ///
    /// One use case is around signal handlers. The signal handler loads the pointer, but it must
    /// not be the last one to drop it. Therefore, this method makes sure there are no signal
    /// handlers owning it at the time of deconstruction of the `Arc`.
    ///
    /// Another use case might be an RCU with a structure that is rather slow to drop ‒ if it was
    /// left to random reader (the last one to hold the old value), it could cause a timeout or
    /// jitter in a query time. With this, the deallocation is done in the updater thread,
    /// therefore outside of a hot path.
    ///
    /// # Signal safety
    ///
    /// This method is *not* safe inside signal handlers.
    ///
    /// # Warning
    ///
    /// Note that if you store a copy of the `Arc` somewhere except the `ArcSwap` itself for
    /// extended period of time, this'll busy-wait the whole time. Unless you need the assurance
    /// the `Arc` is deconstructed here, prefer [`rcu`](#method.rcu).
    pub fn rcu_unwrap<R, F>(&self, mut f: F) -> T
    where
        F: FnMut(&T) -> R,
        R: Into<Arc<T>>,
    {
        let mut wrapped = self.rcu(|prev| f(&*prev));
        loop {
            match Arc::try_unwrap(wrapped) {
                Ok(val) => return val,
                Err(w) => {
                    wrapped = w;
                    thread::yield_now();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate crossbeam_utils;

    use std::sync::atomic::{self, AtomicUsize};
    use std::sync::Barrier;

    use self::crossbeam_utils::scoped as thread;
    use super::*;

    /// Similar to the one in doc tests of the lib, but more times and more intensive (we want to
    /// torture it a bit).
    ///
    /// Takes some time, presumably because this starts 21 000 threads during its lifetime and 20
    /// 000 of them just wait in a tight loop for the other thread to happen.
    #[test]
    fn publish() {
        for _ in 0..100 {
            let config = ArcSwap::from(Arc::new(String::default()));
            let ended = AtomicUsize::new(0);
            thread::scope(|scope| {
                for _ in 0..20 {
                    scope.spawn(|| loop {
                        let cfg = config.load();
                        if !cfg.is_empty() {
                            assert_eq!(*cfg, "New configuration");
                            ended.fetch_add(1, Ordering::Relaxed);
                            return;
                        }
                        atomic::spin_loop_hint();
                    });
                }
                scope.spawn(|| {
                    let new_conf = Arc::new("New configuration".to_owned());
                    config.store(new_conf);
                });
            });
            assert_eq!(20, ended.load(Ordering::Relaxed));
            assert_eq!(2, Arc::strong_count(&config.load()));
            assert_eq!(0, Arc::weak_count(&config.load()));
        }
    }

    /// Similar to the doc tests of ArcSwap, but happens more times.
    #[test]
    fn swap_load() {
        for _ in 0..100 {
            let arc = Arc::new(42);
            let arc_swap = ArcSwap::from(Arc::clone(&arc));
            assert_eq!(42, *arc_swap.load());
            // It can be read multiple times
            assert_eq!(42, *arc_swap.load());

            // Put a new one in there
            let new_arc = Arc::new(0);
            assert_eq!(42, *arc_swap.swap(Arc::clone(&new_arc)));
            assert_eq!(0, *arc_swap.load());
            // One loaded here, one in the arc_swap, one in new_arc
            assert_eq!(3, Arc::strong_count(&arc_swap.load()));
            assert_eq!(0, Arc::weak_count(&arc_swap.load()));
            // The original got released from the arc_swap
            assert_eq!(1, Arc::strong_count(&arc));
            assert_eq!(0, Arc::weak_count(&arc));
        }
    }

    /// Two different writers publish two series of values. The readers check that it is always
    /// increasing in each serie.
    ///
    /// For performance, we try to reuse the threads here.
    #[test]
    fn multi_writers() {
        let first_value = Arc::new((0, 0));
        let shared = ArcSwap::from(Arc::clone(&first_value));
        const WRITER_CNT: usize = 2;
        const READER_CNT: usize = 3;
        const ITERATIONS: usize = 100;
        const SEQ: usize = 50;
        let barrier = Barrier::new(READER_CNT + WRITER_CNT);
        thread::scope(|scope| {
            for w in 0..WRITER_CNT {
                // We need to move w into the closure. But we want to just reference the other
                // things.
                let barrier = &barrier;
                let shared = &shared;
                let first_value = &first_value;
                scope.spawn(move || {
                    for _ in 0..ITERATIONS {
                        barrier.wait();
                        shared.store(Arc::clone(&first_value));
                        barrier.wait();
                        for i in 0..SEQ {
                            shared.store(Arc::new((w, i + 1)));
                        }
                    }
                });
            }
            for _ in 0..READER_CNT {
                scope.spawn(|| {
                    for _ in 0..ITERATIONS {
                        barrier.wait();
                        barrier.wait();
                        let mut previous = [0; 2];
                        let mut last = Arc::clone(&first_value);
                        loop {
                            let cur = shared.load();
                            if Arc::ptr_eq(&last, &cur) {
                                atomic::spin_loop_hint();
                                continue;
                            }
                            let (w, s) = *cur;
                            assert!(previous[w] < s);
                            previous[w] = s;
                            last = cur;
                            if s == SEQ {
                                break;
                            }
                        }
                    }
                });
            }
        });
    }

    /// Make sure the reference count and compare_and_swap works as expected.
    #[test]
    fn cas_ref_cnt() {
        const ITERATIONS: usize = 50;
        let shared = ArcSwap::from(Arc::new(0));
        for i in 0..ITERATIONS {
            let orig = shared.load();
            assert_eq!(i, *orig);
            // One for orig, one for shared
            assert_eq!(2, Arc::strong_count(&orig));
            let n1 = Arc::new(i + 1);
            // Success
            let prev = shared.compare_and_swap(&orig, Arc::clone(&n1), AllocMode::Allowed);
            assert!(Arc::ptr_eq(&orig, &prev));
            // One for orig, one for prev
            assert_eq!(2, Arc::strong_count(&orig));
            // One for n1, one for shared
            assert_eq!(2, Arc::strong_count(&n1));
            assert_eq!(i + 1, *shared.load());
            let n2 = Arc::new(i);
            drop(prev);
            // Failure
            let prev = shared.compare_and_swap(&orig, Arc::clone(&n2), AllocMode::Allowed);
            assert!(Arc::ptr_eq(&n1, &prev));
            // One for orig
            assert_eq!(1, Arc::strong_count(&orig));
            // One for n1, one for shared, one for prev
            assert_eq!(3, Arc::strong_count(&n1));
            // n2 didn't get increased
            assert_eq!(1, Arc::strong_count(&n2));
            assert_eq!(i + 1, *shared.load());
        }
    }

    /// Multiple RCUs interacting.
    #[test]
    fn rcu() {
        const ITERATIONS: usize = 50;
        const THREADS: usize = 10;
        let shared = ArcSwap::from(Arc::new(0));
        thread::scope(|scope| {
            for _ in 0..THREADS {
                scope.spawn(|| {
                    for _ in 0..ITERATIONS {
                        shared.rcu(|old| **old + 1);
                    }
                });
            }
        });
        assert_eq!(THREADS * ITERATIONS, *shared.load());
    }

    /// Multiple RCUs interacting, with unwrapping.
    #[test]
    fn rcu_unwrap() {
        const ITERATIONS: usize = 50;
        const THREADS: usize = 10;
        let shared = ArcSwap::from(Arc::new(0));
        thread::scope(|scope| {
            for _ in 0..THREADS {
                scope.spawn(|| {
                    for _ in 0..ITERATIONS {
                        shared.rcu_unwrap(|old| *old + 1);
                    }
                });
            }
        });
        assert_eq!(THREADS * ITERATIONS, *shared.load());
    }

    /// Test the guard can outlive the `ArcSwap` it comes from without problems.
    #[test]
    fn guard_outlive() {
        let s = ArcSwap::from(Arc::new(42));
        let g = s.peek();
        drop(s);
        let a = Guard::upgrade(&g);
        drop(g);
        assert_eq!(1, Arc::strong_count(&a));
    }

    /// ZSTs are special. Make sure they don't break things here.
    #[test]
    fn zst() {
        let s1 = ArcSwap::from(Arc::new(()));
        let s2 = ArcSwap::from(Arc::new(()));
        let a1 = s1.load();
        let a2 = s2.load();
        assert_eq!(2, Arc::strong_count(&a1));
        assert_eq!(2, Arc::strong_count(&a2));
        s1.store(Arc::new(()));
        assert_eq!(1, Arc::strong_count(&a1));
        drop(s2);
        assert_eq!(1, Arc::strong_count(&a2));
    }
}
