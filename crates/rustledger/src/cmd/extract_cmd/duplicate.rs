//! Duplicate transaction detection for extract command.

use anyhow::{Context, Result};
use rustledger_core::{Directive, Transaction};
use std::path::Path;

/// Load existing transactions from a beancount file for duplicate detection.
///
/// Runs the file through the loader pipeline (`rustledger_loader::load`) rather
/// than a raw parse, so dedup sees the SAME transactions the user does:
///
/// - `include`d files are resolved — a raw parse only saw the top file, so
///   transactions in included ledgers were invisible at dedup time and genuine
///   duplicates got re-imported into the user's real ledger.
/// - Elided amounts are interpolated by booking — a raw parse leaves them `None`,
///   so `first_posting_amount` returned `None` and the amount comparison broke.
///
/// Plugins and validation are intentionally skipped: dedup only needs the booked
/// transaction set, and the existing ledger's own diagnostics aren't this
/// command's concern (and would add overhead / failure modes to every import).
pub(super) fn load_existing_transactions(path: &Path) -> Result<Vec<Transaction>> {
    let options = rustledger_loader::LoadOptions {
        run_plugins: false,
        validate: false,
        ..Default::default()
    };
    let ledger = rustledger_loader::load(path, &options)
        .with_context(|| format!("Failed to load existing ledger: {}", path.display()))?;
    Ok(ledger
        .directives
        .into_iter()
        .filter_map(|spanned| match spanned.value {
            Directive::Transaction(txn) => Some(txn),
            _ => None,
        })
        .collect())
}
