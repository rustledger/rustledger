//! Immutable world snapshot for request handling.
//!
//! Each LSP request receives an immutable snapshot of the world state.
//! This allows requests to be processed concurrently without locks.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

/// Global revision counter used by [`Snapshot`].
///
/// Note: the LSP main loop maintains its OWN per-instance revision
/// counter on `MainLoopState`. This global is kept only because the
/// `Snapshot` API exposes `is_current` / `is_cancelled`, which today
/// has no production callers and is exercised only by the test below.
/// New cancellation-detection logic should use the per-instance
/// counter on `MainLoopState` so multiple LSP instances in one
/// process (e.g., integration tests) don't clobber each other.
static REVISION: AtomicU64 = AtomicU64::new(0);

/// Bump the global revision counter. See [`REVISION`] note about
/// preferring the per-instance counter on `MainLoopState`.
///
/// Kept `#[allow(dead_code)]` because production no longer calls it
/// (the per-instance counter on `MainLoopState` replaced it); the
/// remaining caller is `test_snapshot_cancellation` below, which
/// pins the `Snapshot::is_cancelled` contract even though no
/// production handler reads `Snapshot` today.
#[allow(dead_code)]
pub fn bump_revision() -> u64 {
    REVISION.fetch_add(1, Ordering::SeqCst) + 1
}

/// Get the current revision. See [`REVISION`] note about preferring
/// the per-instance counter on `MainLoopState`.
pub fn current_revision() -> u64 {
    REVISION.load(Ordering::SeqCst)
}

/// An immutable snapshot of the world state.
///
/// Snapshots capture the revision at creation time, allowing
/// handlers to detect if they should cancel (revision changed).
#[derive(Debug)]
pub struct Snapshot {
    /// The revision at snapshot creation time.
    revision: u64,
    /// Parsed directives (TODO: replace with actual data)
    _data: Arc<()>,
}

impl Snapshot {
    /// Create a new snapshot at the current revision.
    pub fn new() -> Self {
        Self {
            revision: current_revision(),
            _data: Arc::new(()),
        }
    }

    /// Check if this snapshot is still current (not cancelled).
    pub fn is_current(&self) -> bool {
        self.revision == current_revision()
    }

    /// Check if this snapshot has been cancelled.
    pub fn is_cancelled(&self) -> bool {
        !self.is_current()
    }
}

impl Default for Snapshot {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_snapshot_cancellation() {
        let snap = Snapshot::new();
        assert!(snap.is_current());

        bump_revision();
        assert!(snap.is_cancelled());
    }
}
