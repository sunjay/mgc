//! The global garbage collector API

use super::GcState;

pub(crate) static GLOBAL_GC: GcState = GcState::new();

/// Sweeps/collects all allocations from the global garbage collector that have been not been marked
/// as reachable via `trace`
///
/// See [`GcState::sweep`] for more info
#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
pub fn sweep() {
    GLOBAL_GC.sweep();
}

/// Returns true if `sweep` should be called as soon as possible
///
/// See [`GcState::needs_collect`] for more info
#[cfg(feature = "global")]
#[cfg_attr(docsrs, doc(cfg(feature = "global")))]
pub fn needs_collect() -> bool {
    GLOBAL_GC.needs_collect()
}
