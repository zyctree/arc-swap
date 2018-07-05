use std::cell::Cell;
use std::ptr;
use std::sync::atomic::{self, AtomicBool, AtomicPtr, AtomicUsize, Ordering};
use std::thread;

/// TODO
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum AllocMode {
    /// TODO
    Allowed,
    /// TODO
    ThreadHead,
    /// TODO
    Disallowed,
    /// TODO
    SignalSafe,
}

const SLOT_CNT: usize = 4;
const EMPTY_SLOT: usize = 1;
const YIELD_EVERY: usize = 8;

// Note: Make sure *not* to derive any clone or eq, so it is not misused by accident.
#[derive(Debug)]
struct Node {
    slots: [AtomicUsize; SLOT_CNT],
    owned: AtomicBool,
    reserve: bool,
    next: AtomicPtr<Node>,
}

impl Node {
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
            Ordering::Release,
            Ordering::Relaxed,
        ) {
            new.next.store(next, Ordering::Relaxed);
            current = unsafe { next.as_ref().unwrap() };
        }

        new
    }

    fn load(from: &AtomicPtr<Node>) -> &'static Node {
        let ptr = from.load(Ordering::Acquire);
        unsafe { ptr.as_ref().unwrap() }
    }

    fn ptr(&self) -> *mut Node {
        self as *const _ as *mut _
    }

    fn claim(&self) -> bool {
        if self.reserve {
            // Can't claim a reserve, sorry…
            return false;
        }
        !self.owned.compare_and_swap(false, true, Ordering::Relaxed)
    }
}

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

node!(N1, N2, false);
node!(N2, N3, false);
node!(N3, R1, false);
node!(R1, R2, true);
node!(R2, R3, true);
node!(R3, N1, true);

static HEAD: AtomicPtr<Node> = AtomicPtr::new(&N1 as *const _ as *mut _);

struct ThreadHint(Cell<Option<&'static Node>>);

impl Drop for ThreadHint {
    fn drop(&mut self) {
        if let Some(node) = self.0.get() {
            assert!(node.owned.swap(false, Ordering::Relaxed));
        }
    }
}

thread_local! {
    static THREAD_HINT: ThreadHint = ThreadHint(Cell::new(None));
}

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
            HEAD.store(node.ptr(), Ordering::Relaxed);
            // Also update our thread hint once we claimed it (and ignore errors if we are shutting
            // down the thread)
            let _ = THREAD_HINT.try_with(|h| h.0.set(Some(node)));
            return node;
        }
        Err(prev) => prev,
    };

    // We didn't find any node which we could claim :-(. Can we allocate?
    if alloc_mode == AllocMode::Allowed || alloc_mode == AllocMode::ThreadHead {
        let new = Node::link_new(prev, head, EMPTY_SLOT, true);
        // Now we've created the new node, we already own it, so we link it into the thread local
        // hint.
        let _ = THREAD_HINT.try_with(|h| h.0.set(Some(new)));
        new
    } else {
        // We can't allocate. So we'll have to use what's there' already and it doesn't really
        // matter where exactly. Specifically, we do *not* update the thread hint, because we don't
        // have one (and hope it'll go better next time or that we may be able to allocate next
        // time).
        head
    }
}

pub(crate) struct Debt {
    ptr: usize,
    slot: &'static AtomicUsize,
    active: bool,
}

impl Debt {
    pub(crate) fn new(ptr: usize, alloc_mode: AllocMode) -> Debt {
        let head = get_head(alloc_mode);
        let mut it = 0usize;
        loop {
            let found = traverse(head, |node| {
                if node.reserve && alloc_mode != AllocMode::SignalSafe {
                    // Only signals are allowed into the reserve.
                    return None;
                }
                node.slots.iter().find(|slot| {
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
                HEAD.store(new.ptr(), Ordering::Release);
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

    pub(crate) fn replace(&mut self, ptr: usize) -> bool {
        if self.active
            && self
                .slot
                .compare_exchange(self.ptr, ptr, Ordering::SeqCst, Ordering::Relaxed)
                .is_ok()
        {
            self.ptr = ptr;
            true
        } else {
            self.active = false;
            false
        }
    }

    pub(crate) fn confirmed<F: Fn() -> usize>(alloc_mode: AllocMode, read_ptr: F) -> Debt {
        let mut ptr = read_ptr();
        let mut debt = Debt::new(ptr, alloc_mode);

        loop {
            let current = read_ptr();
            if ptr == current {
                return debt;
            }
            if !debt.replace(current) {
                return debt;
            }
            ptr = current;
        }
    }

    pub(crate) fn active(&self) -> bool {
        self.active
    }

    pub(crate) fn ptr(&self) -> usize {
        self.ptr
    }

    pub(crate) fn pay(&mut self) -> bool {
        let result = self.replace(EMPTY_SLOT);
        self.active = false;
        result
    }

    // TODO: Document the pre-charge
    pub(crate) fn pay_all<P: Fn()>(ptr: usize, pay: P) {
        let head = Node::load(&HEAD);
        assert!(
            traverse(head, |n| {
                for s in &n.slots {
                    if s.compare_exchange(ptr, EMPTY_SLOT, Ordering::Relaxed, Ordering::Relaxed)
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

            assert!(!debt_2.pay());
            assert!(debt_3.pay());
        }
    }
}
