//! A backend module to track debts.
//!
//! A debt is a missing strong reference count inside an `Arc`. This is OK as long as the `Arc` has
//! at least one reference inside the `ArcSwap` ‒ that prevents it from being destroyed or turned
//! into inner. But these debts must be paid before the `Arc` leaves.
//!
//! The structure is a cyclic linked list. Each active thread owns a node where it tries to insert
//! its debts and if it can't find a free slot, it continues to following nodes until one is found
//! or the whole cycle is traversed. In the latter case, a new node is inserted (unowned).
//!
//! There's also a global head for the list, which changes from time to time, to distribute the
//! load across the nodes.
//!
//! There are some corner-cases ‒ support for signal handlers and modes that are not allowed to
//! allocate can lead to situations where a thread doesn't own a head, or when the thread is being
//! shut down and thread local storage is already deinitialized.

use std::cell::Cell;
use std::ptr;
use std::sync::atomic::{self, AtomicBool, AtomicPtr, AtomicUsize, Ordering};
use std::thread;

/// Describes allowed allocation strategy.
///
/// The [`Guard`](struct.Guard.html) and read methods need a slot inside a global list.
/// Each thread also holds its own list node with several slots. If you keep too many `Guard`s or
/// if a new thread is started, it may be useful or even needed to allocate. This describes under
/// which circumstances it is possible to do.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum AllocMode {
    /// The algorithm can allocate whenever it wishes.
    Allowed,
    /// The algorithm can allocate when a new thread started.
    ///
    /// However, if there aren't enough slots, it'll block (and busy-loop) until some are released
    /// by other threads. This may lead to a deadlock if all the guards are owned by this thread.
    /// You should prefer not to use this unless you know what you're doing.
    ThreadHead,
    /// No allocation is allowed.
    ///
    /// The same busy looping as with `ThreadHead` can happen. Furthermore, the current thread may
    /// not have its own node with slots and the performance in normal (when not full) situation
    /// will be degraded.
    Disallowed,
    /// A mode safe to use in signal handlers.
    ///
    /// In addition to not allowing any allocations, it also can't use thread local storage and
    /// never uses the „this thread's“ node optimisation. The performance is expected to be worse
    /// than with allowed allocation, so use *only* in signal handlers.
    ///
    /// To avoid the busy-looping and deadlocking, signal handlers have a small global reserve just
    /// for their use.
    SignalSafe,
}

/// Number of slots in each node.
const SLOT_CNT: usize = 4;
/// A marker of empty slot.
///
/// We don't assume NULL = 0 (no idea if Rust aims at any like these). But we assume all pointers
/// inside Arcs are aligned to at least 2, because there are the two counts which are usizes.
const EMPTY_SLOT: usize = 1;
/// Whenever busy-looping, do a full yield this many iterations.
const YIELD_EVERY: usize = 8;

/// One node of the global debt list
#[derive(Debug)] // Note: Make sure *not* to derive any clone or eq ‒ high risk of footguns here.
struct Node {
    slots: [AtomicUsize; SLOT_CNT],
    owned: AtomicBool,
    reserve: bool,
    next: AtomicPtr<Node>,
}

impl Node {
    /// Create a new node and link it into the global list.
    ///
    /// It creates a new owned node, fills in the first slot and links it after the `prev` node.
    /// The `current` node is a hint what the caller things is the one after `prev`.
    fn link_new(
        prev: &'static Node,
        mut current: &'static Node,
        first: usize,
        owned: bool,
    ) -> &'static Node {
        let new = Node {
            slots: [
                AtomicUsize::new(first),
                AtomicUsize::new(EMPTY_SLOT),
                AtomicUsize::new(EMPTY_SLOT),
                AtomicUsize::new(EMPTY_SLOT),
            ],
            owned: AtomicBool::new(owned),
            reserve: false,
            next: AtomicPtr::new(current.ptr()),
        };

        let new = Box::leak(Box::new(new));

        while let Err(next) = prev.next.compare_exchange_weak(
            current.ptr(),
            new.ptr(),
            // To publish the data
            Ordering::Release,
            // Will retry and do the release on the next try
            Ordering::Relaxed,
        ) {
            // Will be published with the next link attempt
            new.next.store(next, Ordering::Relaxed);
            current = unsafe { next.as_ref().unwrap() };
        }

        new
    }

    /// Loads a node from an atomic pointer.
    fn load(from: &AtomicPtr<Node>) -> &'static Node {
        // To get any new content of the node
        let ptr = from.load(Ordering::Acquire);
        unsafe { ptr.as_ref().unwrap() }
    }

    /// Turns the node reference into a raw pointer.
    fn ptr(&self) -> *mut Node {
        self as *const _ as *mut _
    }

    /// Tries to claim ownership of the node.
    ///
    /// Returns success or failure.
    fn claim(&self) -> bool {
        if self.reserve {
            // Can't claim a reserve, sorry…
            return false;
        }
        // Does not synchronize anything else, only to claim the ownership ‒ and that's enough with
        // having a separate timeline for this atomic only.
        !self.owned.compare_and_swap(false, true, Ordering::Relaxed)
    }
}

/// Helper macro to generate basic set of nodes to start with.
macro_rules! node {
    ($name:ident, $next:ident, $reserve:expr) => {
        static $name: Node = Node {
            slots: [
                AtomicUsize::new(EMPTY_SLOT),
                AtomicUsize::new(EMPTY_SLOT),
                AtomicUsize::new(EMPTY_SLOT),
                AtomicUsize::new(EMPTY_SLOT),
            ],
            owned: AtomicBool::new(false),
            reserve: $reserve,
            next: AtomicPtr::new(&$next as *const _ as *mut _),
        };
    };
}

// Basic set of nodes, some of them are reserves. Forms a base of a cyclic linked list.
node!(N1, N2, false);
node!(N2, N3, false);
node!(N3, R1, false);
node!(R1, R2, true);
node!(R2, R3, true);
node!(R3, N1, true);

/// Global head to the cyclic linked list.
static HEAD: AtomicPtr<Node> = AtomicPtr::new(&N1 as *const _ as *mut _);

/// A hint for each thread to know where to start.
struct ThreadHint(Cell<Option<&'static Node>>);

impl Drop for ThreadHint {
    fn drop(&mut self) {
        if let Some(node) = self.0.get() {
            // Does not synchronize with anything else, just with itself so someone can claim it ‒
            // independent timeline.
            assert!(node.owned.swap(false, Ordering::Relaxed));
        }
    }
}

thread_local! {
    static THREAD_HINT: ThreadHint = ThreadHint(Cell::new(None));
}

/// Goes through the cyclic linked list.
///
/// It tries to search the linked list according to the given predicate. If the predicate returns
/// `Some` value, the value is returned as successful result. If the whole list is traversed
/// without matching, an error result is returned with the last node visited (one that points to
/// `head`.
fn traverse<R, F>(head: &'static Node, f: F) -> Result<R, &'static Node>
where
    F: Fn(&'static Node) -> Option<R>,
{
    let mut current = head;
    loop {
        if let Some(result) = f(current) {
            return Ok(result);
        }

        let next = Node::load(&current.next);
        if ptr::eq(next, head) {
            return Err(current);
        }

        current = next;
    }
}

/// Gets a head of the cyclic linked list.
///
/// Since the list is cyclic, it doesn't matter much which node is considered as the head. But this
/// one picks a head for the caller, solving some corner cases.
///
/// * If a thread local hint for an already owned head is available, it is used.
/// * If not, it searches for a node it can claim, sets it into the thread local storage for future
///   and returns that one.
/// * If none can be claimed and allocation is allowed, a new one is allocated.
/// * If all of the above fails or signal-safe allocation mode is used, an arbitrary node is
///   returned without claiming ownership.
fn get_head(alloc_mode: AllocMode) -> &'static Node {
    // Look if we already have a thread hint. Signal handlers aren't allowed to touch the thread
    // local storage (because the data there is neither atomic, not `volatile sigatomic_t`).
    //
    // This is the happy and expected case.
    if alloc_mode != AllocMode::SignalSafe {
        if let Ok(Some(hint)) = THREAD_HINT.try_with(|h| h.0.get()) {
            return hint;
        }
    } else {
        // Signals will just have to take some slot somewhere (maybe in the reserve), but can't do
        // much else, so just give up and don't do the complex stuff.
        return Node::load(&HEAD);
    }

    // OK, we don't have a hint yet. Try to find an available node.
    let head = Node::load(&HEAD);
    let found = traverse(head, |node| if node.claim() { Some(node) } else { None });

    let prev = match found {
        Ok(node) => {
            // Update the head so we start searching from some other place next time.
            // (doesn't publish or get any new info, just turns the wheel a bit, only optimisation
            // ‒ it wouldn't matter much if someone got the stale info)
            HEAD.store(node.ptr(), Ordering::Relaxed);
            // Also update our thread hint once we claimed it (and ignore errors if we are shutting
            // down the thread)
            if THREAD_HINT.try_with(|h| h.0.set(Some(node))).is_err() {
                // In case the thread is already dying, we need to not claim the ownership
                // (Relaxed: doesn't synchronize anything else, independent timeline)
                node.owned.store(false, Ordering::Relaxed);
            }
            return node;
        }
        Err(prev) => prev,
    };

    // We didn't find any node which we could claim :-(. Can we allocate?
    if alloc_mode == AllocMode::Allowed || alloc_mode == AllocMode::ThreadHead {
        let new = Node::link_new(prev, head, EMPTY_SLOT, true);
        // Now we've created the new node, we already own it, so we link it into the thread local
        // hint.
        if THREAD_HINT.try_with(|h| h.0.set(Some(new))).is_err() {
            // In case the thread is already dying, we need to not claim the ownership
            // (Relaxed: doesn't synchronize anything else, independent timeline)
            new.owned.store(false, Ordering::Relaxed);
        }
        new
    } else {
        // We can't allocate. So we'll have to use what's there' already and it doesn't really
        // matter where exactly. Specifically, we do *not* update the thread hint, because we don't
        // have one (and hope it'll go better next time or that we may be able to allocate next
        // time).
        head
    }
}

/// A representation of one debt.
///
/// The debt may be already paid for.
pub struct Debt {
    ptr: usize,
    slot: &'static AtomicUsize,
    active: bool,
}

impl Debt {
    /// Allocates a new debt slot.
    ///
    /// Finds a free slot for a debt and uses it, by putting the provided `ptr` into it. Note that
    /// by the time this finishes, the loaded pointer might already be stale.
    pub(crate) fn new(ptr: usize, alloc_mode: AllocMode) -> Debt {
        debug_assert_ne!(ptr, EMPTY_SLOT);
        let head = get_head(alloc_mode);
        let mut it = 0usize;
        loop {
            let found = traverse(head, |node| {
                if node.reserve && alloc_mode != AllocMode::SignalSafe {
                    // Only signals are allowed into the reserve.
                    return None;
                }
                node.slots.iter().find(|slot| {
                    // The failed attempts don't matter at all, no synchronization with the rest is
                    // needed on them. But we need to place the success attempt firmly in between
                    // the loads.
                    slot.compare_exchange(EMPTY_SLOT, ptr, Ordering::SeqCst, Ordering::Relaxed)
                        .is_ok()
                })
            });

            let prev = match found {
                Ok(slot) => {
                    return Debt {
                        ptr,
                        slot,
                        active: true,
                    }
                }
                Err(prev) => prev,
            };

            if alloc_mode == AllocMode::Allowed {
                let new = Node::link_new(prev, head, ptr, false);
                // Let the next thread find this new node faster, there are 3 empty slots now.
                // (Release so the thread reading through HEAD sees the content)
                HEAD.store(new.ptr(), Ordering::Release);
                return Debt {
                    ptr,
                    slot: &new.slots[0],
                    active: true,
                };
            } else {
                it = it.wrapping_add(1);
                if it % YIELD_EVERY == 0 {
                    thread::yield_now();
                } else {
                    atomic::spin_loop_hint();
                }
            }
        }
    }

    /// Replaces the pointer inside the debt.
    ///
    /// Returns false if the debt for the previous pointer was already paid. In such case, the debt
    /// is not changed and is still considered already paid.
    pub(crate) fn replace(&mut self, ptr: usize) -> bool {
        if self.active
            // The order ‒ same as in new. In the failure case, we need the un-paying of the debt
            // to stay after this, so acquire.
            && self
                .slot
                .compare_exchange(self.ptr, ptr, Ordering::SeqCst, Ordering::Acquire)
                .is_ok()
        {
            self.ptr = ptr;
            true
        } else {
            self.active = false;
            false
        }
    }

    /// Creates a new debt and confirms it is valid.
    ///
    /// To properly claim a pointer, a debt must be noted. But because a stale value might be
    /// noted, this also confirms the debt is still for the correct pointer by re-reading it once
    /// more afterwards. If it changed, it tries to replace the pointer in the debt.
    ///
    /// The returned debt may already be paid when this returns.
    pub(crate) fn confirmed<F: Fn() -> usize>(alloc_mode: AllocMode, read_ptr: F) -> Debt {
        let mut ptr = read_ptr();
        let mut debt = Debt::new(ptr, alloc_mode);

        loop {
            let current = read_ptr();
            if ptr == current {
                return debt;
            }
            debug_assert_ne!(current, EMPTY_SLOT);
            if !debt.replace(current) {
                return debt;
            }
            ptr = current;
        }
    }

    /// Is there still a debt?
    pub(crate) fn active(&self) -> bool {
        self.active
    }

    /// The pointer for which the debt is.
    pub(crate) fn ptr(&self) -> usize {
        self.ptr
    }

    /// Releases the slot and marks the debt as paid.
    ///
    /// It is up to the caller to actually make sure the debt is paid, this only marks it so.
    ///
    /// If this returns false, the debt was already paid before (maybe by someone else). In such
    /// case the caller should compensate, because it was paid twice.
    pub(crate) fn pay(&mut self) -> bool {
        let result = self.replace(EMPTY_SLOT);
        self.active = false;
        result
    }

    /// Pays all the debts of the given pointer.
    ///
    /// Traverses the whole linked list, paying off all the debts by calling the provided closure.
    ///
    /// # Note
    ///
    /// * If the pointer is still active somewhere, new debts may appear. But that's OK, because
    ///   once *that* instance of the pointer will leave, it'll also pay all remaining debts.
    /// * The closure is called *after* claiming the debt. That is technically wrong (but can't
    ///   reasonably be done in other way), therefore the caller is supposed to „pre-pay“ one
    ///   strong count and then decrement it once more after this is done. Therefore, there'd be no
    ///   time when it is short one count, but there are times when there's one extra ‒ which is
    ///   safe to do.
    pub(crate) fn pay_all<P: Fn()>(ptr: usize, pay: P) {
        let head = Node::load(&HEAD);
        assert!(
            traverse(head, |n| {
                for s in &n.slots {
                    // In the success case, we need the previous payment to stay before and the
                    // final discarge of the pre-pay after the last one, AcqRel makes it a barrier
                    // for these.
                    //
                    // In the failure case, it's unrelated to our debt, we don't change anything,
                    // so there's nothing to synchronize (and we would have seen the debt because
                    // of the snapshot of SeqCst on swap).
                    if s.compare_exchange(ptr, EMPTY_SLOT, Ordering::AcqRel, Ordering::Relaxed)
                        .is_ok()
                    {
                        pay();
                    }
                }
                None::<()>
            }).is_err()
        );
    }
}

#[cfg(test)]
mod tests {
    extern crate crossbeam_utils;

    use std::collections::HashSet;
    use std::sync::{Barrier, Mutex};

    use self::crossbeam_utils::scoped as thread;

    use super::*;

    #[test]
    fn linked_list_circular() {
        assert!(traverse(&N1, |_| None::<()>).is_err());
    }

    #[test]
    fn find_reserve() {
        assert!(ptr::eq(
            &R1,
            traverse(&N1, |n| if n.reserve { Some(n) } else { None }).unwrap(),
        ));
    }

    const PAR: usize = 16;

    #[test]
    fn head_stays_the_same() {
        let bar = Barrier::new(PAR);
        let heads = Mutex::new(HashSet::new());
        thread::scope(|scope| {
            for _ in 0..PAR {
                scope.spawn(|| {
                    let h1 = get_head(AllocMode::Allowed);
                    let h2 = get_head(AllocMode::Disallowed);
                    assert!(ptr::eq(h1, h2));
                    bar.wait();
                    let mut heads = heads.lock().unwrap();
                    assert!(heads.insert(h1 as *const _ as usize));
                });
            }
        });

        let cnt = AtomicUsize::new(0);
        assert!(
            traverse(&N1, |_| {
                cnt.fetch_add(1, Ordering::Relaxed);
                None::<()>
            }).is_err()
        );
        assert!(cnt.into_inner() >= PAR + 3 /* 3 for the reserves R1, R2 and R3 */);
    }

    const TEST_PTR_1: usize = 7;

    #[test]
    fn get_debt() {
        let mut debt_1 = Debt::new(TEST_PTR_1, AllocMode::Allowed);
        assert_eq!(debt_1.ptr, TEST_PTR_1);
        assert_eq!(debt_1.slot.load(Ordering::Relaxed), TEST_PTR_1);

        let mut debt_2 = Debt::new(TEST_PTR_1, AllocMode::SignalSafe);
        assert_eq!(debt_2.ptr, TEST_PTR_1);
        assert_eq!(debt_2.slot.load(Ordering::Relaxed), TEST_PTR_1);

        let slot = debt_1.slot;

        assert!(debt_1.pay());
        // We can't really check it is empty, because someone else might have claimed the slot in
        // between.
        assert_ne!(TEST_PTR_1, slot.load(Ordering::Relaxed));
        assert!(debt_2.pay());
    }

    const TEST_PTR_2: usize = 9;

    #[test]
    fn debt_par() {
        thread::scope(|scope| {
            // Many threads, to use up all the threads ‒ we check it can wait a bit if there are
            // too many and it can't allocate.
            for _ in 0..PAR * 4 * SLOT_CNT {
                scope.spawn(|| {
                    let mut debt = Debt::new(TEST_PTR_2, AllocMode::Disallowed);
                    ::std::thread::yield_now();
                    assert!(debt.pay());
                });
            }
        });
    }

    const TEST_PTR_3: usize = 11;
    const TEST_PTR_4: usize = 13;

    #[test]
    fn pay_all_replace() {
        for _ in 0..1000 {
            let mut debt_1 = Debt::new(TEST_PTR_3, AllocMode::Allowed);
            let mut debt_2 = Debt::new(TEST_PTR_3, AllocMode::Allowed);
            let mut debt_3 = Debt::new(TEST_PTR_3, AllocMode::Allowed);

            assert_eq!(debt_1.ptr, TEST_PTR_3);
            assert_eq!(debt_1.slot.load(Ordering::Relaxed), TEST_PTR_3);

            assert_eq!(debt_2.ptr, TEST_PTR_3);
            assert_eq!(debt_2.slot.load(Ordering::Relaxed), TEST_PTR_3);

            assert_eq!(debt_3.ptr, TEST_PTR_3);
            assert_eq!(debt_3.slot.load(Ordering::Relaxed), TEST_PTR_3);

            assert!(debt_3.replace(TEST_PTR_4));

            assert_eq!(debt_3.ptr, TEST_PTR_4);
            assert_eq!(debt_3.slot.load(Ordering::Relaxed), TEST_PTR_4);

            let cnt = AtomicUsize::new(0);
            Debt::pay_all(TEST_PTR_3, || {
                cnt.fetch_add(1, Ordering::Relaxed);
            });
            assert_eq!(2, cnt.load(Ordering::Relaxed));

            assert!(!debt_1.replace(TEST_PTR_4));
            assert_eq!(debt_1.ptr, TEST_PTR_3);
            assert!(!debt_1.active);
            // We can't really do this, other test might have used that slot already!
            // assert_eq!(debt_1.slot.load(Ordering::Relaxed), EMPTY_SLOT);
            assert_ne!(debt_1.slot.load(Ordering::Relaxed), TEST_PTR_1);

            assert!(!debt_2.pay());
            assert!(debt_3.pay());
        }
    }
}
