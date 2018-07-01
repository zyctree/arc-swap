// TODO: Use NonNull pointers?

use std::cell::Cell;
use std::mem;
use std::sync::atomic::{self, AtomicBool, AtomicPtr, AtomicUsize, Ordering};

const SLOT_CNT: usize = 4;
const EMPTY_SLOT: usize = 1;

// TODO: Align for cache lines?
#[derive(Debug)]
struct Entry {
    /// Pointers that owe a reference. This is usize-encoded, because we don't know the type here.
    slots: [AtomicUsize; SLOT_CNT],
    /// Entries form a cyclic linked list and are never released.
    next: AtomicPtr<Entry>,
    /// Claimed as some thread? If false, it can be assigned to a thread.
    owned: AtomicBool,
    /// Reserved for signal handlers, do not use otherwise.
    reserved: bool,
}

impl Default for Entry {
    fn default() -> Entry {
        let entry = Entry {
            slots: Default::default(),
            next: AtomicPtr::default(),
            owned: AtomicBool::default(),
            reserved: false,
        };
        for slot in &entry.slots {
            slot.store(EMPTY_SLOT, Ordering::Relaxed);
        }
        entry
    }
}

// We assume neither is a valid pointer.
//
// We *don't* assume NULL = 0.
const NO_HEAD: usize = 1;
const ALLOCATING_HEAD: usize = 3;

static HEAD: AtomicUsize = AtomicUsize::new(NO_HEAD);

struct ThreadHint(Cell<Option<&'static Entry>>);

impl Drop for ThreadHint {
    fn drop(&mut self) {
        if let Some(entry) = self.0.get() {
            assert!(entry.owned.swap(false, Ordering::Relaxed));
        }
    }
}

thread_local! {
static THREAD_HINT: ThreadHint = ThreadHint(Cell::new(None));
}

// TODO: Something about reserves?
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum AllocMode {
    /// Allocation is allowed as needed.
    Allowed,
    /// Do not allocate, either find an empty slot or wait until one is available.
    DontAlloc,
    /// Do not allocate and don't even touch a thread-local storage.
    SignalSafe,
}

const ENTRIES_INIT: usize = 3;
const ENTRIES_RESERVE: usize = 3;

fn link_entries(entries: &mut [Entry], reserved: bool) {
    let mut next: Option<&mut Entry> = None;
    for entry in entries {
        entry.reserved = reserved;
        if let Some(next) = next {
            entry.next.store(next, Ordering::Relaxed);
        }
        next = Some(entry);
    }
}

fn get_global_head(can_allocate: bool) -> *const Entry {
    let head_store_alloc = if can_allocate {
        ALLOCATING_HEAD
    } else {
        NO_HEAD
    };
    // Acquire ‒ we want to see all the modified pointers and initialized things there.
    match HEAD.compare_and_swap(NO_HEAD, head_store_alloc, Ordering::Acquire) {
        NO_HEAD if can_allocate => {
            /*
             * On the first ever access, we create a cyclic linked lists with few unused entries
             * and few used ones as a reserve for signal handlers.
             *
             * We do the preparation with Ordering::Relaxed ‒ we actually wouldn't need any atomic
             * stuff here at all, because we publish the whole data structure as a whole.
             *
             * It is published with Release, to make all previous writes visible.
             */
            let mut init: Box<[Entry; ENTRIES_INIT]> = Default::default();
            let mut reserve: Box<[Entry; ENTRIES_RESERVE]> = Default::default();
            link_entries(&mut init[..], false);
            link_entries(&mut reserve[..], true);
            {
                let first_reserve: &mut Entry = &mut reserve[0];
                init[ENTRIES_INIT - 1]
                    .next
                    .store(first_reserve, Ordering::Relaxed);
            }
            let first_entry: *const Entry = {
                let first_entry: &mut Entry = &mut init[0];
                reserve[ENTRIES_RESERVE - 1]
                    .next
                    .store(first_entry, Ordering::Relaxed);
                first_entry as *const _
            };
            HEAD.store(first_entry as usize, Ordering::Release);
            mem::forget(init);
            mem::forget(reserve);
            first_entry
        }
        NO_HEAD => panic!("Debt list not initialized but can't allocate"),
        ALLOCATING_HEAD => loop {
            match HEAD.load(Ordering::Acquire) {
                ALLOCATING_HEAD => atomic::spin_loop_hint(),
                ptr => return ptr as *const _,
            }
        },
        ptr => ptr as *const _,
    }
}

fn link_entry(
    new: Box<Entry>,
    current: &Entry,
    mut next: *mut Entry,
    ordering: Ordering,
) -> *const Entry {
    new.owned.store(true, Ordering::Relaxed);
    new.next.store(next, Ordering::Relaxed);
    let new = Box::into_raw(new);
    let _ = THREAD_HINT.try_with(|h| h.0.set(Some(unsafe { new.as_ref().unwrap() })));
    // TODO: Could we use compare_exchange_Weak? Could that be failing forever?
    while let Err(orig) = current
        .next
        .compare_exchange(next, new, ordering, Ordering::Relaxed)
    {
        next = orig;
        atomic::spin_loop_hint();
    }
    new
}

fn get_hint() -> Option<&'static Entry> {
    THREAD_HINT
        .try_with(|h| h.0.get())
        .unwrap_or_else(|_| match HEAD.load(Ordering::Acquire) {
            NO_HEAD | ALLOCATING_HEAD => None,
            ptr => unsafe { (ptr as *const Entry).as_ref() },
        })
}

fn get_head(alloc_mode: AllocMode) -> *const Entry {
    if alloc_mode == AllocMode::SignalSafe {
        return get_global_head(false);
    }

    // This'll actually be the most common thing, hopefully and it doesn't touch anything
    // atomic.
    let local = get_hint();

    if let Some(local) = local {
        return local;
    }

    // We don't have the hint in the local storage (or can't use it). Start with the global head.
    let can_allocate = alloc_mode == AllocMode::Allowed;
    let head = get_global_head(can_allocate);
    let mut current: &Entry = unsafe { head.as_ref().unwrap() };

    loop {
        if !current
            .owned
            .compare_and_swap(false, true, Ordering::Relaxed)
        {
            let _ = THREAD_HINT.try_with(|h| h.0.set(Some(current)));
            HEAD.store(current as *const _ as usize, Ordering::Relaxed);
            return current;
        }

        let next = current.next.load(Ordering::Relaxed);
        if next as *const _ == head {
            if can_allocate {
                let new = Box::new(Entry::default());
                return link_entry(new, current, next, Ordering::Release);
            } else {
                return head;
            }
        }

        current = unsafe { next.as_ref().unwrap() };
    }
}

pub(crate) struct Slot {
    ptr: usize,
    slot: &'static AtomicUsize,
}

impl Slot {
    pub(crate) fn new(ptr: usize, alloc_mode: AllocMode) -> Slot {
        let head = get_head(alloc_mode);
        let mut current = unsafe { head.as_ref().unwrap() };
        loop {
            if !current.reserved || alloc_mode == AllocMode::SignalSafe {
                for slot in &current.slots {
                    // Can we lower the SeqCst here?
                    if slot
                        .compare_exchange(EMPTY_SLOT, ptr, Ordering::SeqCst, Ordering::Relaxed)
                        .is_ok()
                    {
                        return Slot { ptr, slot };
                    }
                }
            }

            let next = current.next.load(Ordering::Relaxed);
            if next as *const _ == head {
                if alloc_mode == AllocMode::Allowed {
                    let new = Box::new(Entry::default());
                    new.slots[0].store(ptr, Ordering::Relaxed);
                    let new = link_entry(new, current, next, Ordering::SeqCst);
                    let new = unsafe { new.as_ref().unwrap() };
                    return Slot {
                        ptr,
                        slot: &new.slots[0],
                    };
                } else {
                    atomic::spin_loop_hint();
                }
            }

            current = unsafe { next.as_ref().unwrap() };
        }
    }

    /// Tries to release the slot.
    ///
    /// If the debt was already paid, it returns false.
    pub(crate) fn release(self) -> bool {
        return self
            .slot
            .compare_and_swap(self.ptr, EMPTY_SLOT, Ordering::Relaxed) == self.ptr;
    }
}
