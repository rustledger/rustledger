//! Duplicate transaction detection for extract command.

use super::ledgers::Ledgers;
use anyhow::{Context, Result};
use rustledger_core::{Directive, Transaction};
use std::path::Path;

/// The transactions of [`load_existing`], for tests.
#[cfg(test)]
pub(super) fn load_existing_transactions(path: &Path) -> Result<Vec<Transaction>> {
    Ok(load_existing(&mut Ledgers::default(), path)?.transactions)
}

/// The `--existing` ledger as dedup sees it.
pub(super) struct ExistingLedger {
    /// Every transaction that loaded.
    pub(super) transactions: Vec<Transaction>,
    /// A warning to print when part of the ledger did not load: its
    /// transactions are missing from the comparison, so their duplicates
    /// would be imported again. The ledger's own validation errors are not
    /// counted (validation is skipped); only what stopped entries loading.
    pub(super) warning: Option<String>,
}

/// Load existing transactions from a beancount file for duplicate detection.
///
/// Runs the file through the loader pipeline (`rustledger_loader::load`) rather
/// than a raw parse, so dedup sees the SAME transactions the user does:
///
/// - `include`d files are resolved — a raw parse only saw the top file, so
///   transactions in included ledgers were invisible at dedup time and genuine
///   duplicates got re-imported into the user's real ledger.
/// - Elided amounts are interpolated by booking — a raw parse leaves them `None`,
///   so the account posting had no amount to compare and the match broke.
///
/// Plugins and validation are intentionally skipped: dedup only needs the booked
/// transaction set, and the existing ledger's own diagnostics aren't this
/// command's concern (and would add overhead / failure modes to every import).
///
/// A parse or include error does not stop the import, as before, but it is no
/// longer silent: entries in the part that failed to load cannot be compared,
/// so `extract` would re-import their duplicates without a word.
///
/// Dedup is the last reader of the run's ledgers, so it takes this one out of
/// `ledgers` rather than cloning its transactions; the currency lookup may
/// already have loaded it (#2503).
pub(super) fn load_existing(ledgers: &mut Ledgers, path: &Path) -> Result<ExistingLedger> {
    let ledger = ledgers
        .take(path)
        .with_context(|| format!("Failed to load existing ledger: {}", path.display()))?;
    let errors: Vec<&rustledger_loader::LedgerError> = ledger
        .errors
        .iter()
        .filter(|e| e.severity == rustledger_loader::ErrorSeverity::Error)
        .collect();
    let warning = errors.first().map(|first| {
        format!(
            "--existing ledger {} has {} error(s), first: {}\n  \
             transactions in the parts that failed to load are not compared, so \
             their duplicates may be imported again; `rledger check` shows them all",
            path.display(),
            errors.len(),
            first.message,
        )
    });
    Ok(ExistingLedger {
        transactions: ledger
            .directives
            .into_iter()
            .filter_map(|spanned| match spanned.value {
                Directive::Transaction(txn) => Some(txn),
                _ => None,
            })
            .collect(),
        warning,
    })
}
