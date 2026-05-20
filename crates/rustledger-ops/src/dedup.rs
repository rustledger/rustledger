//! Duplicate transaction detection.
//!
//! Provides three deduplication strategies:
//!
//! - **Structural** — exact hash match using [`crate::fingerprint::structural_hash`].
//!   Finds transactions that are byte-for-byte identical (excluding metadata).
//!
//! - **Fuzzy** — approximate match using date + amount + text similarity.
//!   Finds transactions that are likely the same despite minor differences
//!   (e.g., different payee formatting between bank and ledger).
//!
//! - **Fingerprint** (future, Phase 1) — stable BLAKE3 fingerprint match for
//!   import deduplication across runs.

use std::collections::HashSet;

use rust_decimal::Decimal;
use rustledger_plugin_types::{DirectiveData, DirectiveWrapper, PluginError, TransactionData};

use crate::fingerprint::structural_hash;

/// Result of finding a structural duplicate.
#[derive(Debug)]
pub struct StructuralDuplicate {
    /// Index of the duplicate directive in the input slice.
    pub index: usize,
    /// Date of the duplicate transaction.
    pub date: String,
    /// Narration of the duplicate transaction.
    pub narration: String,
}

impl StructuralDuplicate {
    /// Convert to a [`PluginError`] for use in plugin wrappers.
    #[must_use]
    pub fn to_plugin_error(&self) -> PluginError {
        PluginError::error(format!(
            "Duplicate transaction: {} \"{}\"",
            self.date, self.narration
        ))
    }
}

/// Find structurally duplicate transactions in a directive list.
///
/// Returns the indices and details of transactions whose structural hash
/// matches an earlier transaction. The first occurrence is kept; subsequent
/// duplicates are reported.
#[must_use]
pub fn find_structural_duplicates(directives: &[DirectiveWrapper]) -> Vec<StructuralDuplicate> {
    let mut seen: HashSet<u64> = HashSet::new();
    let mut duplicates = Vec::new();

    for (i, wrapper) in directives.iter().enumerate() {
        if let DirectiveData::Transaction(txn) = &wrapper.data {
            let hash = structural_hash(&wrapper.date, txn);
            if !seen.insert(hash) {
                duplicates.push(StructuralDuplicate {
                    index: i,
                    date: wrapper.date.clone(),
                    narration: txn.narration.clone(),
                });
            }
        }
    }

    duplicates
}

// ============================================================================
// Fuzzy dedup — for matching imported transactions against existing ledger
// ============================================================================

/// Configuration for fuzzy duplicate detection.
#[derive(Debug, Clone)]
pub struct FuzzyDedupConfig {
    /// Minimum word overlap ratio to consider text a match (0.0 to 1.0).
    /// Default: 0.5 (50% of the shorter text's words must appear in the longer).
    pub text_similarity_threshold: f64,
}

impl Default for FuzzyDedupConfig {
    fn default() -> Self {
        Self {
            text_similarity_threshold: 0.5,
        }
    }
}

/// Result of a fuzzy duplicate match.
#[derive(Debug)]
pub struct FuzzyDuplicateMatch {
    /// Index of the new transaction that is a duplicate.
    pub new_index: usize,
    /// Index of the existing transaction it matches.
    pub existing_index: usize,
}

/// Find fuzzy duplicates between new and existing transactions.
///
/// Matches on: same date, same first-posting amount, and fuzzy text match
/// on payee/narration. Returns indices of new transactions that are
/// probable duplicates of existing ones.
#[must_use]
pub fn find_fuzzy_duplicates(
    new_directives: &[DirectiveWrapper],
    existing_directives: &[DirectiveWrapper],
    config: &FuzzyDedupConfig,
) -> Vec<FuzzyDuplicateMatch> {
    let mut matches = Vec::new();

    // Pre-compute existing transaction info for efficient comparison
    let existing: Vec<(usize, &str, Option<Decimal>, String)> = existing_directives
        .iter()
        .enumerate()
        .filter_map(|(i, w)| {
            if let DirectiveData::Transaction(txn) = &w.data {
                Some((i, w.date.as_str(), first_posting_amount(txn), txn_text(txn)))
            } else {
                None
            }
        })
        .collect();

    for (new_i, wrapper) in new_directives.iter().enumerate() {
        if let DirectiveData::Transaction(txn) = &wrapper.data {
            let new_amount = first_posting_amount(txn);
            let new_text = txn_text(txn);

            for &(existing_i, existing_date, ref existing_amount, ref existing_text) in &existing {
                if wrapper.date != existing_date {
                    continue;
                }
                if new_amount != *existing_amount {
                    continue;
                }
                if fuzzy_text_match(&new_text, existing_text, config.text_similarity_threshold) {
                    matches.push(FuzzyDuplicateMatch {
                        new_index: new_i,
                        existing_index: existing_i,
                    });
                    break; // One match is enough
                }
            }
        }
    }

    matches
}

/// Get the decimal amount from the first posting of a transaction.
fn first_posting_amount(txn: &TransactionData) -> Option<Decimal> {
    txn.postings.first().and_then(|p| {
        p.units
            .as_ref()
            .and_then(|u| u.number.parse::<Decimal>().ok())
    })
}

/// Build a lowercase string combining payee and narration for fuzzy matching.
fn txn_text(txn: &TransactionData) -> String {
    let mut text = String::new();
    if let Some(ref payee) = txn.payee {
        text.push_str(payee);
        text.push(' ');
    }
    text.push_str(&txn.narration);
    text.to_lowercase()
}

/// Fuzzy text match: returns true if either string contains the other,
/// or if they share significant word overlap.
fn fuzzy_text_match(a: &str, b: &str, threshold: f64) -> bool {
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
    if shorter.is_empty() {
        return false;
    }
    let match_count = shorter.iter().filter(|w| longer.contains(w)).count();
    #[allow(clippy::cast_precision_loss)]
    let ratio = match_count as f64 / shorter.len() as f64;
    ratio >= threshold
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_plugin_types::{AmountData, DirectiveData, PostingData, TransactionData};

    fn make_directive(
        date: &str,
        payee: Option<&str>,
        narration: &str,
        amount: &str,
    ) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: payee.map(String::from),
                narration: narration.to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![PostingData {
                    account: "Assets:Bank".to_string(),
                    units: Some(AmountData {
                        number: amount.to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                }],
            }),
        }
    }

    // ===== Structural dedup tests =====

    #[test]
    fn structural_finds_exact_duplicates() {
        let directives = vec![
            make_directive("2024-01-15", Some("Store"), "Groceries", "-50.00"),
            make_directive("2024-01-15", Some("Store"), "Groceries", "-50.00"),
        ];
        let dups = find_structural_duplicates(&directives);
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].index, 1);
    }

    #[test]
    fn structural_no_false_positives() {
        let directives = vec![
            make_directive("2024-01-15", Some("Store"), "Groceries", "-50.00"),
            make_directive("2024-01-15", Some("Store"), "Groceries", "-51.00"),
        ];
        let dups = find_structural_duplicates(&directives);
        assert!(dups.is_empty());
    }

    #[test]
    fn structural_duplicate_to_plugin_error() {
        let dup = StructuralDuplicate {
            index: 1,
            date: "2024-01-15".to_string(),
            narration: "Test".to_string(),
        };
        let err = dup.to_plugin_error();
        assert!(err.message.contains("Duplicate transaction"));
        assert!(err.message.contains("2024-01-15"));
    }

    // ===== Fuzzy dedup tests =====

    #[test]
    fn fuzzy_finds_matching_transactions() {
        let new = vec![make_directive(
            "2024-01-15",
            Some("WHOLE FOODS"),
            "Groceries",
            "-50.00",
        )];
        let existing = vec![make_directive(
            "2024-01-15",
            Some("Whole Foods Market"),
            "Groceries",
            "-50.00",
        )];
        let config = FuzzyDedupConfig::default();
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn fuzzy_no_match_different_date() {
        let new = vec![make_directive(
            "2024-01-15",
            Some("Store"),
            "Groceries",
            "-50.00",
        )];
        let existing = vec![make_directive(
            "2024-01-16",
            Some("Store"),
            "Groceries",
            "-50.00",
        )];
        let config = FuzzyDedupConfig::default();
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        assert!(matches.is_empty());
    }

    #[test]
    fn fuzzy_no_match_different_amount() {
        let new = vec![make_directive(
            "2024-01-15",
            Some("Store"),
            "Groceries",
            "-50.00",
        )];
        let existing = vec![make_directive(
            "2024-01-15",
            Some("Store"),
            "Groceries",
            "-51.00",
        )];
        let config = FuzzyDedupConfig::default();
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        assert!(matches.is_empty());
    }

    #[test]
    fn fuzzy_text_match_exact() {
        assert!(fuzzy_text_match("hello world", "hello world", 0.5));
    }

    #[test]
    fn fuzzy_text_match_contains() {
        assert!(fuzzy_text_match("hello", "hello world", 0.5));
        assert!(fuzzy_text_match("hello world", "hello", 0.5));
    }

    #[test]
    fn fuzzy_text_match_word_overlap() {
        // "whole foods" shares 2/2 words with "whole foods market" -> 100%
        assert!(fuzzy_text_match("whole foods", "whole foods market", 0.5));
    }

    #[test]
    fn fuzzy_text_match_insufficient_overlap() {
        // "alpha" shares 0/1 words with "beta gamma" -> 0%
        assert!(!fuzzy_text_match("alpha", "beta gamma", 0.5));
    }

    #[test]
    fn fuzzy_text_match_empty() {
        assert!(!fuzzy_text_match("", "hello", 0.5));
        assert!(!fuzzy_text_match("hello", "", 0.5));
    }

    // ===== Additional fuzzy dedup tests =====

    #[test]
    fn fuzzy_multiple_matches_only_first_returned() {
        // Two existing transactions match the same new one; only first match per new txn
        let new = vec![make_directive(
            "2024-01-15",
            Some("Store"),
            "Groceries",
            "-50.00",
        )];
        let existing = vec![
            make_directive("2024-01-15", Some("Store"), "Groceries", "-50.00"),
            make_directive("2024-01-15", Some("Store"), "Groceries run", "-50.00"),
        ];
        let config = FuzzyDedupConfig::default();
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        // Should only return one match (the first existing match, due to `break`)
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].new_index, 0);
        assert_eq!(matches[0].existing_index, 0);
    }

    #[test]
    fn fuzzy_non_transaction_directives_are_skipped() {
        let note_directive = DirectiveWrapper {
            directive_type: "note".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Note(rustledger_plugin_types::NoteData {
                account: "Assets:Bank".to_string(),
                comment: "A note".to_string(),
                metadata: vec![],
            }),
        };
        let txn = make_directive("2024-01-15", Some("Store"), "Groceries", "-50.00");

        // Note in new directives - should be skipped
        let matches = find_fuzzy_duplicates(
            std::slice::from_ref(&note_directive),
            std::slice::from_ref(&txn),
            &FuzzyDedupConfig::default(),
        );
        assert!(matches.is_empty());

        // Note in existing directives - should be skipped
        let matches =
            find_fuzzy_duplicates(&[txn], &[note_directive], &FuzzyDedupConfig::default());
        assert!(matches.is_empty());
    }

    #[test]
    fn fuzzy_empty_directives_list() {
        let config = FuzzyDedupConfig::default();

        // Both empty
        let matches = find_fuzzy_duplicates(&[], &[], &config);
        assert!(matches.is_empty());

        // New empty
        let existing = vec![make_directive(
            "2024-01-15",
            Some("Store"),
            "Test",
            "-50.00",
        )];
        let matches = find_fuzzy_duplicates(&[], &existing, &config);
        assert!(matches.is_empty());

        // Existing empty
        let new = vec![make_directive(
            "2024-01-15",
            Some("Store"),
            "Test",
            "-50.00",
        )];
        let matches = find_fuzzy_duplicates(&new, &[], &config);
        assert!(matches.is_empty());
    }

    #[test]
    fn fuzzy_matching_with_narration_only() {
        // No payee, match on narration text only
        let new = vec![make_directive(
            "2024-01-15",
            None,
            "whole foods market",
            "-50.00",
        )];
        let existing = vec![make_directive(
            "2024-01-15",
            None,
            "Whole Foods Market #123",
            "-50.00",
        )];
        let config = FuzzyDedupConfig::default();
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn fuzzy_matching_payee_vs_narration() {
        // Payee in new matches narration in existing (both lowercased)
        let new = vec![make_directive(
            "2024-01-15",
            Some("Whole Foods"),
            "Payment",
            "-50.00",
        )];
        let existing = vec![make_directive(
            "2024-01-15",
            None,
            "whole foods market",
            "-50.00",
        )];
        let config = FuzzyDedupConfig::default();
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        // "whole foods payment" vs "whole foods market" — shares 2/3 words (67%) > 50%
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn structural_empty_directives_list() {
        let dups = find_structural_duplicates(&[]);
        assert!(dups.is_empty());
    }

    #[test]
    fn structural_non_transaction_not_duplicated() {
        let note1 = DirectiveWrapper {
            directive_type: "note".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Note(rustledger_plugin_types::NoteData {
                account: "Assets:Bank".to_string(),
                comment: "Same note".to_string(),
                metadata: vec![],
            }),
        };
        let note2 = note1.clone();
        let dups = find_structural_duplicates(&[note1, note2]);
        assert!(dups.is_empty());
    }

    #[test]
    fn fuzzy_dedup_config_default() {
        let config = FuzzyDedupConfig::default();
        assert!((config.text_similarity_threshold - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn fuzzy_high_threshold_rejects_partial_matches() {
        let new = vec![make_directive("2024-01-15", None, "whole foods", "-50.00")];
        let existing = vec![make_directive(
            "2024-01-15",
            None,
            "whole foods market special",
            "-50.00",
        )];
        // At threshold 0.9, "whole foods" (2 words) needs 90% of 2 = 1.8 → 2 matches in longer
        // "whole foods" are both in longer text, so 2/2 = 100% → still passes
        let config = FuzzyDedupConfig {
            text_similarity_threshold: 0.9,
        };
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        assert_eq!(matches.len(), 1);

        // Totally different words at high threshold should not match
        let new = vec![make_directive("2024-01-15", None, "alpha beta", "-50.00")];
        let existing = vec![make_directive(
            "2024-01-15",
            None,
            "alpha gamma delta",
            "-50.00",
        )];
        let matches = find_fuzzy_duplicates(&new, &existing, &config);
        // "alpha beta" shares 1/2 words with "alpha gamma delta" → 50% < 90%
        assert!(matches.is_empty());
    }
}
