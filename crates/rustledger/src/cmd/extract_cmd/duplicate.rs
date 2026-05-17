//! Duplicate transaction detection for extract command.

use anyhow::{Context, Result};
use rust_decimal::Decimal;
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

/// Check if a new transaction is a duplicate of an existing one.
///
/// Matches on: same date, same first-posting amount, and fuzzy payee/narration match.
pub(super) fn is_duplicate(new_txn: &Transaction, existing: &[Transaction]) -> bool {
    let new_amount = first_posting_amount(new_txn);
    let new_text = txn_match_text(new_txn);

    existing.iter().any(|existing_txn| {
        if new_txn.date != existing_txn.date {
            return false;
        }
        let existing_amount = first_posting_amount(existing_txn);
        if new_amount != existing_amount {
            return false;
        }
        let existing_text = txn_match_text(existing_txn);
        fuzzy_text_match(&new_text, &existing_text)
    })
}

/// Get the amount from the first posting of a transaction (for comparison).
pub(super) fn first_posting_amount(txn: &Transaction) -> Option<Decimal> {
    txn.postings.first().and_then(|p| {
        p.units
            .as_ref()
            .and_then(rustledger_core::IncompleteAmount::number)
    })
}

/// Build a lowercase string combining payee and narration for fuzzy matching.
pub(super) fn txn_match_text(txn: &Transaction) -> String {
    let mut text = String::new();
    if let Some(ref payee) = txn.payee {
        text.push_str(payee.as_str());
        text.push(' ');
    }
    text.push_str(txn.narration.as_str());
    text.to_lowercase()
}

/// Fuzzy text match: returns true if either string contains the other,
/// or if they share significant word overlap.
pub(super) fn fuzzy_text_match(a: &str, b: &str) -> bool {
    if a.is_empty() || b.is_empty() {
        return false;
    }
    if a == b {
        return true;
    }
    if a.contains(b) || b.contains(a) {
        return true;
    }
    let a_words: Vec<&str> = a.split_whitespace().collect();
    let b_words: Vec<&str> = b.split_whitespace().collect();
    let (shorter, longer) = if a_words.len() <= b_words.len() {
        (&a_words, &b_words)
    } else {
        (&b_words, &a_words)
    };
    let matches = shorter.iter().filter(|w| longer.contains(w)).count();
    matches * 2 > shorter.len()
}
