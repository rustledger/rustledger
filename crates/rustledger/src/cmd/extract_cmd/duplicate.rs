//! Duplicate transaction detection for extract command.

use anyhow::{Context, Result};
use rustledger_core::{Directive, Transaction};
use std::fs;
use std::path::Path;

/// Load existing transactions from a beancount file for duplicate detection.
pub(super) fn load_existing_transactions(path: &Path) -> Result<Vec<Transaction>> {
    let content = fs::read_to_string(path)
        .with_context(|| format!("Failed to read existing ledger: {}", path.display()))?;
    let parse_result = rustledger_parser::parse(&content);
    let mut transactions = Vec::new();
    for directive in parse_result.directives {
        if let Directive::Transaction(txn) = directive.value {
            transactions.push(txn);
        }
    }
    Ok(transactions)
}
