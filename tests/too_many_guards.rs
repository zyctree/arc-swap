extern crate arc_swap;
extern crate crossbeam_utils;

use std::sync::{Arc, Barrier};

use arc_swap::ArcSwap;
use crossbeam_utils::scoped;

const PARAL: usize = 4;
const ITER: usize = 100;

/// Test the case when we have more guards than reasonable.
///
/// This'll allocate further thread debt nodes, exercising one of the fallback code paths.
///
/// Note that this test is alone in the process, because it doesn't want interference with the
/// global debt list.
#[test]
fn too_many_guards() {
    let bar = Barrier::new(PARAL);
    let a = ArcSwap::from(Arc::new(42));
    scoped::scope(|scope| {
        for _ in 0..PARAL {
            scope.spawn(|| {
                bar.wait();
                let _all = (0..ITER).map(|_| a.peek()).collect::<Vec<_>>();
            });
        }
    });
    let orig = a.swap(Arc::new(0));
    assert_eq!(*orig, 42);
    assert_eq!(Arc::strong_count(&orig), 1);
}
