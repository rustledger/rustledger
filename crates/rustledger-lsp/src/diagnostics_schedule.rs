//! Debounced scheduling of diagnostics passes for edited documents (#2940).
//!
//! A diagnostics pass validates the whole ledger, which on a large one costs
//! tens of milliseconds (#2858 measured about 46 ms on 108k lines). Running one
//! per `didChange` spends that on every keystroke the client forwards, and only
//! the last pass of a burst is ever looked at. So `didChange` applies the edit
//! at once and only *schedules* a pass here; the main loop runs it once the
//! document has gone [`DIAGNOSTICS_DEBOUNCE`] without another change.
//!
//! This type is the pure bookkeeping: which documents owe a pass, and when.
//! It never reads the clock itself, every method takes `now`, so the logic is
//! tested by advancing an `Instant` by hand instead of sleeping.

use crate::AbsPathBuf;
use lsp_types::Uri;
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// How long a document must go without a change before its diagnostics are
/// recomputed.
///
/// Above Neovim's default `debounce_text_changes` (150 ms), so a client that
/// already batches keystrokes still has its consecutive batches collapse into
/// one pass while the user is typing, and short enough that diagnostics still
/// feel immediate once they stop.
pub const DIAGNOSTICS_DEBOUNCE: Duration = Duration::from_millis(200);

/// A document that owes a diagnostics pass.
#[derive(Debug, Clone)]
struct Pending {
    /// The URI in the client's spelling, which is what the publish must echo.
    /// Replaced on every change, so it is always the latest spelling.
    uri: Uri,
    /// When the pass becomes due: the last change plus the debounce delay.
    deadline: Instant,
}

/// Documents with a pending diagnostics pass, keyed by path like the VFS.
#[derive(Debug)]
pub(crate) struct DiagnosticsSchedule {
    delay: Duration,
    pending: HashMap<AbsPathBuf, Pending>,
}

impl DiagnosticsSchedule {
    /// An empty schedule whose passes fall due `delay` after the last change.
    pub(crate) fn new(delay: Duration) -> Self {
        Self {
            delay,
            pending: HashMap::new(),
        }
    }

    /// Record a change to `path` at `now`: the document owes a pass, due one
    /// delay from now. A later change pushes the deadline back, which is what
    /// collapses a burst into one pass.
    ///
    /// There is deliberately no max-wait cap: a client that keeps sending
    /// changes faster than the delay gets its diagnostics when it pauses, as
    /// with rust-analyzer's coalescing and the TypeScript tooling's trailing
    /// debounce. If continuous typing should ever refresh periodically, the
    /// cap belongs here: keep the first deadline's origin and clamp to it.
    pub(crate) fn schedule(&mut self, path: AbsPathBuf, uri: Uri, now: Instant) {
        let deadline = now + self.delay;
        self.pending.insert(path, Pending { uri, deadline });
    }

    /// Drop every pending pass (on `shutdown`).
    pub(crate) fn clear(&mut self) {
        self.pending.clear();
    }

    /// Drop the pending pass for `path`, if any. Returns its URI so a caller
    /// that wants to run the pass early (a request that reads diagnostics)
    /// can do so.
    pub(crate) fn cancel(&mut self, path: &AbsPathBuf) -> Option<Uri> {
        self.pending.remove(path).map(|p| p.uri)
    }

    /// Whether `path` has a pending pass.
    #[cfg(test)]
    pub(crate) fn is_pending(&self, path: &AbsPathBuf) -> bool {
        self.pending.contains_key(path)
    }

    /// The earliest deadline among pending passes, for the main loop's timer.
    pub(crate) fn next_deadline(&self) -> Option<Instant> {
        self.pending.values().map(|p| p.deadline).min()
    }

    /// Remove and return every pass whose deadline is at or before `now`,
    /// in deadline order (path order on a tie) so the publish order is
    /// deterministic.
    pub(crate) fn take_due(&mut self, now: Instant) -> Vec<(AbsPathBuf, Uri)> {
        let mut due: Vec<(Instant, AbsPathBuf)> = self
            .pending
            .iter()
            .filter(|(_, p)| p.deadline <= now)
            .map(|(path, p)| (p.deadline, path.clone()))
            .collect();
        due.sort();
        due.into_iter()
            .filter_map(|(_, path)| {
                let pending = self.pending.remove(&path)?;
                Some((path, pending.uri))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn doc(name: &str) -> (AbsPathBuf, Uri) {
        let path = AbsPathBuf::new(crate::test_abs(&format!("tmp/rl-sched/{name}")))
            .expect("test_abs is absolute");
        let uri = crate::path_to_uri(&path).expect("file uri");
        (path, uri)
    }

    const DELAY: Duration = Duration::from_millis(200);

    #[test]
    fn test_schedule_burst_is_due_once_after_last_change() {
        let mut sched = DiagnosticsSchedule::new(DELAY);
        let (path, uri) = doc("a.beancount");
        let t0 = Instant::now();
        for i in 0..50u64 {
            sched.schedule(
                path.clone(),
                uri.clone(),
                t0 + Duration::from_millis(i * 10),
            );
        }
        let last = t0 + Duration::from_millis(490);
        assert_eq!(sched.next_deadline(), Some(last + DELAY));
        assert!(
            sched
                .take_due(last + DELAY - Duration::from_millis(1))
                .is_empty()
        );
        let due = sched.take_due(last + DELAY);
        assert_eq!(due.len(), 1, "a burst must owe exactly one pass");
        assert_eq!(due[0].0, path);
        assert!(sched.take_due(last + DELAY * 10).is_empty());
        assert_eq!(sched.next_deadline(), None);
    }

    #[test]
    fn test_schedule_interleaved_documents_each_due_once() {
        let mut sched = DiagnosticsSchedule::new(DELAY);
        let (a, a_uri) = doc("a.beancount");
        let (b, b_uri) = doc("b.beancount");
        let t0 = Instant::now();
        for i in 0..10u64 {
            let t = t0 + Duration::from_millis(i * 20);
            if i % 2 == 0 {
                sched.schedule(a.clone(), a_uri.clone(), t);
            } else {
                sched.schedule(b.clone(), b_uri.clone(), t);
            }
        }
        // a last changed at 160 ms, b at 180 ms.
        let due_a = sched.take_due(t0 + Duration::from_millis(360));
        assert_eq!(due_a.iter().map(|d| &d.0).collect::<Vec<_>>(), vec![&a]);
        let due_b = sched.take_due(t0 + Duration::from_millis(380));
        assert_eq!(due_b.iter().map(|d| &d.0).collect::<Vec<_>>(), vec![&b]);
        assert_eq!(sched.next_deadline(), None);
    }

    #[test]
    fn test_schedule_cancel_drops_the_pass() {
        let mut sched = DiagnosticsSchedule::new(DELAY);
        let (path, uri) = doc("a.beancount");
        let t0 = Instant::now();
        sched.schedule(path.clone(), uri.clone(), t0);
        assert!(sched.is_pending(&path));
        assert_eq!(
            sched.cancel(&path).map(|u| u.as_str().to_string()),
            Some(uri.as_str().to_string())
        );
        assert!(!sched.is_pending(&path));
        assert!(sched.take_due(t0 + DELAY).is_empty());
        assert_eq!(sched.cancel(&path).map(|u| u.as_str().to_string()), None);
    }
}
