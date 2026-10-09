//! The `--ledger` and `--existing` ledgers, loaded once per run (#2503).
//!
//! Three consumers read these files: the `--ledger` profile reader, the
//! currency lookup for an entry that names no `currency`
//! (`resolve_entry_currency`), and `--existing` dedup. Each used to call
//! `rustledger_loader::load` itself, so one ledger given as both flags was
//! parsed and booked three times per import. They all load with the same
//! options (includes followed, plugins and validation skipped), so one load
//! per path, handed to each in turn, gives every consumer the identical
//! `Ledger` it built for itself before.
//!
//! The cache stores the load's `Result` as is. Each consumer still turns a
//! failure into its own message, naming its own flag, at the point in the run
//! where it reported it before; only the work behind the message is shared.

use rustledger_loader::{Ledger, LoadOptions, ProcessError};
use std::path::{Path, PathBuf};

/// The options every consumer loads with. Plugins and validation change
/// neither which accounts are opened nor which transactions exist, and both
/// cost time on every import.
fn load_options() -> LoadOptions {
    LoadOptions {
        run_plugins: false,
        validate: false,
        ..Default::default()
    }
}

/// Ledgers loaded so far in this run, keyed by the path as given.
#[derive(Default)]
pub(super) struct Ledgers {
    loaded: Vec<(PathBuf, Result<Ledger, ProcessError>)>,
    /// How many times `rustledger_loader::load` ran, for the tests that pin
    /// "once per path".
    #[cfg(test)]
    pub(super) loads: usize,
}

impl Ledgers {
    fn index(&mut self, path: &Path) -> usize {
        if let Some(i) = self.loaded.iter().position(|(p, _)| p == path) {
            return i;
        }
        #[cfg(test)]
        {
            self.loads += 1;
        }
        let ledger = rustledger_loader::load(path, &load_options());
        self.loaded.push((path.to_path_buf(), ledger));
        self.loaded.len() - 1
    }

    /// The ledger at `path`, loading it on first use.
    pub(super) fn get(&mut self, path: &Path) -> &Result<Ledger, ProcessError> {
        let i = self.index(path);
        &self.loaded[i].1
    }

    /// The ledger at `path`, owned, for the last consumer of a run (dedup),
    /// which keeps its transactions. Loads it if no one has yet.
    pub(super) fn take(&mut self, path: &Path) -> Result<Ledger, ProcessError> {
        let i = self.index(path);
        self.loaded.swap_remove(i).1
    }
}
