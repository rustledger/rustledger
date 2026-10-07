//! Duplicate transaction detection.
//!
//! Provides three deduplication strategies:
//!
//! - **Structural** — exact hash match using [`crate::fingerprint::structural_hash`].
//!   Finds transactions that are byte-for-byte identical (excluding metadata).
//!
//! - **Import** — [`find_import_duplicates`] matches imported transactions
//!   against an existing ledger: shared id links (`^ofx-…`, `^csv-…`) first,
//!   then same date + account + commodity + amount with identical or similar
//!   payee/narration text. Existing transactions are a multiset, so each
//!   absorbs at most one new transaction.
//!
//! - **Fingerprint** (future, Phase 1) — stable BLAKE3 fingerprint match for
//!   import deduplication across runs.

use std::collections::HashSet;

use rustc_hash::FxHashMap as HashMap;

use rust_decimal::Decimal;
use rustledger_core::{Directive, Transaction};
use rustledger_plugin_types::{DirectiveData, DirectiveWrapper, PluginError};

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
// Import dedup — matching imported transactions against an existing ledger
// ============================================================================

/// Link prefix marking a bank-assigned OFX transaction id (`FITID`).
pub const OFX_ID_LINK_PREFIX: &str = "ofx-";

/// Link prefix marking a CSV transaction id (an importer's
/// `transaction_id_column`).
pub const CSV_ID_LINK_PREFIX: &str = "csv-";

/// Every link prefix that marks a source-assigned transaction id.
///
/// Each prefix is its own namespace: ids are only compared within one, so an
/// OFX id and a CSV id never contradict each other (a bank whose export moved
/// from OFX to CSV still dedups by text).
pub const ID_LINK_PREFIXES: &[&str] = &[OFX_ID_LINK_PREFIX, CSV_ID_LINK_PREFIX];

/// Render a source transaction id as a beancount link under `prefix`, or
/// `None` if nothing usable survives.
///
/// Links lex as `\^[a-zA-Z0-9-_/.]+`, and a bank's id is an opaque string that
/// need not respect that. Anything outside the set becomes `-`, so the emitted
/// ledger re-parses.
///
/// Two different ids only collide after sanitizing if they differ *only* in
/// characters that all map to `-`, which no real id scheme does. Dedup trusts
/// an equal id link as identity (within the importer's account), so such a
/// collision would drop a transaction; that is the price of ids that survive
/// as links, and it is confined to ids no bank issues.
#[must_use]
pub fn id_link(prefix: &str, raw: &str) -> Option<String> {
    let cleaned: String = raw
        .trim()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '/' | '.') {
                c
            } else {
                '-'
            }
        })
        .collect();

    // An id that sanitizes to only separators carries no information, and the
    // resulting link would be one every such transaction shares — worse than
    // no link at all. `-` is not the only separator that survives: `.`, `_`
    // and `/` are all in the link charset, so `...` and `__/__` pass a
    // `trim_matches('-')` check while meaning exactly as little. Require a
    // character that actually identifies something.
    if !cleaned.chars().any(|c| c.is_ascii_alphanumeric()) {
        return None;
    }
    Some(format!("{prefix}{cleaned}"))
}

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

/// Why a new transaction was matched to an existing one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DuplicateReason {
    /// Both carry this id link (`^ofx-…`, `^csv-…`). Decisive on its own.
    IdLink(String),
    /// Same date, account, commodity and amount, and identical payee/narration.
    ExactText,
    /// Same date, account, commodity and amount, and similar payee/narration.
    FuzzyText,
}

impl std::fmt::Display for DuplicateReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdLink(link) => write!(f, "same id link ^{link}"),
            Self::ExactText => f.write_str("same date, amount and text"),
            Self::FuzzyText => f.write_str("same date and amount, similar text"),
        }
    }
}

/// One new transaction matched to the existing transaction it duplicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDuplicate {
    /// Index of the new transaction in the `new` input.
    pub new_index: usize,
    /// Index of the existing transaction it was matched to. Every existing
    /// transaction appears at most once across all matches.
    pub existing_index: usize,
    /// What the match rests on.
    pub reason: DuplicateReason,
}

/// Match newly imported transactions against an existing ledger.
///
/// The existing transactions are a **multiset**: each one absorbs at most one
/// new transaction, so two identical coffees on one day survive a ledger that
/// already holds one of them (#2421).
///
/// `account` scopes the comparison to the posting each transaction makes to
/// the importer's account: its commodity and amount are what is compared, and
/// an existing transaction that never touches the account is not a candidate.
/// With `None` (a caller with no importer account, such as the component's
/// `session.dedup`), each transaction's first posting — its account,
/// commodity and amount — is compared instead.
///
/// Matching runs in three passes, strongest evidence first, so a weak match
/// can never claim an existing transaction a stronger one needed:
///
/// 1. **Id links.** A shared `^ofx-…` / `^csv-…` link is a duplicate whatever
///    the date, amount or text say.
/// 2. **Exact text.** Same date, commodity and amount, identical
///    (case-insensitive) payee + narration.
/// 3. **Fuzzy text.** Same date, commodity and amount, similar payee +
///    narration (see [`FuzzyDedupConfig`]).
///
/// Passes 2 and 3 never pair two transactions that both carry ids in the same
/// namespace: equal ids were matched in pass 1, so different ids mean two
/// distinct transactions however alike they look. When only one side has an
/// id (a ledger imported before ids were emitted), the text passes decide.
///
/// Existing keys are computed once and bucketed by date, account, commodity
/// and amount, so the cost is near-linear in `new + existing` rather than
/// their product (#2422).
///
/// The result is ordered by `new_index`.
#[must_use]
pub fn find_import_duplicates(
    new: &[&Transaction],
    existing: &[&Transaction],
    account: Option<&str>,
    config: &FuzzyDedupConfig,
) -> Vec<ImportDuplicate> {
    let threshold = config.text_similarity_threshold;

    let existing_keys: Vec<Option<TxnKey<'_>>> =
        existing.iter().map(|t| TxnKey::of(t, account)).collect();
    let mut by_amount: HashMap<AmountKey<'_>, Vec<usize>> = HashMap::default();
    let mut by_id: HashMap<&str, Vec<usize>> = HashMap::default();
    for (i, key) in existing_keys.iter().enumerate() {
        let Some(key) = key else { continue };
        for amount in &key.amounts {
            by_amount.entry(amount.clone()).or_default().push(i);
        }
        for id in &key.ids {
            by_id.entry(id).or_default().push(i);
        }
    }

    let new_keys: Vec<Option<TxnKey<'_>>> = new.iter().map(|t| TxnKey::of(t, account)).collect();
    let mut consumed = vec![false; existing.len()];
    let mut matched: Vec<Option<(usize, DuplicateReason)>> = vec![None; new.len()];

    // Pass 1: shared id links.
    for (new_i, key) in new_keys.iter().enumerate() {
        let Some(key) = key else { continue };
        'ids: for id in &key.ids {
            for &ex in by_id.get(id).map_or(&[][..], Vec::as_slice) {
                if !consumed[ex] {
                    consumed[ex] = true;
                    matched[new_i] = Some((ex, DuplicateReason::IdLink((*id).to_string())));
                    break 'ids;
                }
            }
        }
    }

    // Passes 2 and 3: same amount bucket, text decides.
    for exact in [true, false] {
        for (new_i, key) in new_keys.iter().enumerate() {
            if matched[new_i].is_some() {
                continue;
            }
            let Some(key) = key else { continue };
            'amounts: for amount in &key.amounts {
                for &ex in by_amount.get(amount).map_or(&[][..], Vec::as_slice) {
                    if consumed[ex] {
                        continue;
                    }
                    let Some(ek) = &existing_keys[ex] else {
                        continue;
                    };
                    if ids_conflict(&key.ids, &ek.ids) {
                        continue;
                    }
                    let hit = if exact {
                        !key.text.is_empty() && key.text == ek.text
                    } else {
                        fuzzy_text_match(&key.text, &ek.text, threshold)
                    };
                    if hit {
                        consumed[ex] = true;
                        let reason = if exact {
                            DuplicateReason::ExactText
                        } else {
                            DuplicateReason::FuzzyText
                        };
                        matched[new_i] = Some((ex, reason));
                        break 'amounts;
                    }
                }
            }
        }
    }

    matched
        .into_iter()
        .enumerate()
        .filter_map(|(new_index, m)| {
            m.map(|(existing_index, reason)| ImportDuplicate {
                new_index,
                existing_index,
                reason,
            })
        })
        .collect()
}

/// Result of a fuzzy duplicate match.
#[derive(Debug)]
pub struct FuzzyDuplicateMatch {
    /// Index of the new transaction that is a duplicate.
    pub new_index: usize,
    /// Index of the existing transaction it matches.
    pub existing_index: usize,
}

/// Find duplicates between new and existing directives, with no importer
/// account to scope by.
///
/// [`find_import_duplicates`] with `account = None` over the transactions of
/// each list: each transaction's first posting (account, commodity, amount)
/// is compared, existing transactions are consumed one match each, and id
/// links are decisive. Indices are into the directive slices; directives that
/// are not transactions never match.
#[must_use]
pub fn find_fuzzy_duplicates(
    new_directives: &[Directive],
    existing_directives: &[Directive],
    config: &FuzzyDedupConfig,
) -> Vec<FuzzyDuplicateMatch> {
    fn transactions(directives: &[Directive]) -> (Vec<usize>, Vec<&Transaction>) {
        directives
            .iter()
            .enumerate()
            .filter_map(|(i, d)| match d {
                Directive::Transaction(t) => Some((i, t)),
                _ => None,
            })
            .unzip()
    }
    let (new_pos, new_txns) = transactions(new_directives);
    let (existing_pos, existing_txns) = transactions(existing_directives);
    find_import_duplicates(&new_txns, &existing_txns, None, config)
        .into_iter()
        .map(|m| FuzzyDuplicateMatch {
            new_index: new_pos[m.new_index],
            existing_index: existing_pos[m.existing_index],
        })
        .collect()
}

/// Bucket key: what two transactions must share before their text is compared.
#[derive(Clone, PartialEq, Eq, Hash)]
struct AmountKey<'a> {
    date: rustledger_core::NaiveDate,
    account: &'a str,
    currency: &'a str,
    /// Normalized, so `-2.5` and `-2.50` share a bucket.
    number: Decimal,
}

/// A transaction's dedup comparison key, computed once per transaction.
struct TxnKey<'a> {
    /// One entry per distinct posting on the scoped account (or the first
    /// posting when unscoped). Usually exactly one.
    amounts: Vec<AmountKey<'a>>,
    /// Links under an [`ID_LINK_PREFIXES`] namespace.
    ids: Vec<&'a str>,
    /// Lowercased payee + narration.
    text: String,
}

impl<'a> TxnKey<'a> {
    /// `None` when the transaction makes no posting to `account` (or, unscoped,
    /// has no postings): it cannot be a duplicate of anything the importer
    /// produced.
    fn of(txn: &'a Transaction, account: Option<&str>) -> Option<Self> {
        let amount_of = |p: &'a rustledger_core::Posting| {
            let units = p.units.as_ref()?;
            Some(AmountKey {
                date: txn.date,
                account: p.account.as_str(),
                currency: units.currency()?,
                number: units.number()?.normalize(),
            })
        };
        let mut amounts: Vec<AmountKey<'a>> = match account {
            Some(account) => {
                let mut on_account = txn
                    .postings
                    .iter()
                    .filter(|p| p.account.as_str() == account)
                    .peekable();
                on_account.peek()?;
                on_account.filter_map(|p| amount_of(p)).collect()
            }
            None => txn
                .postings
                .first()
                .and_then(|p| amount_of(p))
                .into_iter()
                .collect(),
        };
        amounts.dedup();
        let ids = txn
            .links
            .iter()
            .map(rustledger_core::Link::as_str)
            .filter(|l| ID_LINK_PREFIXES.iter().any(|p| l.starts_with(p)))
            .collect();
        Some(Self {
            amounts,
            ids,
            text: txn_text(txn),
        })
    }
}

/// Whether two id sets prove two transactions distinct: both carry ids in some
/// shared namespace and no id is common to both.
fn ids_conflict(a: &[&str], b: &[&str]) -> bool {
    ID_LINK_PREFIXES.iter().any(|prefix| {
        let a_ns: Vec<&str> = a
            .iter()
            .copied()
            .filter(|l| l.starts_with(prefix))
            .collect();
        let b_ns: Vec<&str> = b
            .iter()
            .copied()
            .filter(|l| l.starts_with(prefix))
            .collect();
        !a_ns.is_empty() && !b_ns.is_empty() && !a_ns.iter().any(|l| b_ns.contains(l))
    })
}

/// Build a lowercase string combining payee and narration for fuzzy matching.
fn txn_text(txn: &Transaction) -> String {
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

    /// Core-typed transaction directive for the fuzzy-dedup tests (which now run
    /// on `core::Directive`).
    fn make_directive(date: &str, payee: Option<&str>, narration: &str, amount: &str) -> Directive {
        use std::str::FromStr;
        let date: rustledger_core::NaiveDate = date.parse().unwrap();
        let mut txn = Transaction::new(date, narration);
        if let Some(p) = payee {
            txn = txn.with_payee(p);
        }
        txn = txn.with_synthesized_posting(rustledger_core::Posting::new(
            "Assets:Bank",
            rustledger_core::Amount::new(Decimal::from_str(amount).unwrap(), "USD"),
        ));
        Directive::Transaction(txn)
    }

    /// Wire-typed directive for the structural-dedup tests (which stay on
    /// `DirectiveWrapper`, the plugin boundary).
    fn make_wrapper(
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
            make_wrapper("2024-01-15", Some("Store"), "Groceries", "-50.00"),
            make_wrapper("2024-01-15", Some("Store"), "Groceries", "-50.00"),
        ];
        let dups = find_structural_duplicates(&directives);
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].index, 1);
    }

    #[test]
    fn structural_no_false_positives() {
        let directives = vec![
            make_wrapper("2024-01-15", Some("Store"), "Groceries", "-50.00"),
            make_wrapper("2024-01-15", Some("Store"), "Groceries", "-51.00"),
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
        let note_directive = Directive::Open(rustledger_core::Open::new(
            "2024-01-15".parse().unwrap(),
            "Assets:Bank",
        ));
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

    #[test]
    fn fuzzy_threshold_is_inclusive_at_exactly_half() {
        // Exactly 50% word overlap counts as a duplicate (ratio >= 0.5) — the
        // boundary the CLI's now-deleted `> 0.5` copy got wrong. Same date and
        // amount; the two narrations share 1 of 2 words.
        let new = vec![make_directive("2024-01-15", None, "alpha beta", "-50.00")];
        let existing = vec![make_directive("2024-01-15", None, "alpha gamma", "-50.00")];
        assert_eq!(
            find_fuzzy_duplicates(&new, &existing, &FuzzyDedupConfig::default()).len(),
            1,
            "exactly 50% overlap must be a duplicate (>= 0.5)",
        );
    }

    // ===== Import dedup (multiset, scoped, id links) =====

    /// A transaction posting `amount currency` to `account`, with links.
    fn txn(
        date: &str,
        narration: &str,
        account: &str,
        amount: &str,
        currency: &str,
        links: &[&str],
    ) -> Transaction {
        use std::str::FromStr;
        let mut t = Transaction::new(date.parse().unwrap(), narration)
            .with_synthesized_posting(rustledger_core::Posting::new(
                account,
                rustledger_core::Amount::new(Decimal::from_str(amount).unwrap(), currency),
            ))
            .with_synthesized_posting(rustledger_core::Posting::auto("Expenses:Food"));
        for l in links {
            t = t.with_link(*l);
        }
        t
    }

    const BANK: &str = "Assets:Bank:Checking";

    fn import(new: &[Transaction], existing: &[Transaction]) -> Vec<ImportDuplicate> {
        let new: Vec<&Transaction> = new.iter().collect();
        let existing: Vec<&Transaction> = existing.iter().collect();
        find_import_duplicates(&new, &existing, Some(BANK), &FuzzyDedupConfig::default())
    }

    #[test]
    fn existing_transactions_are_a_multiset() {
        // Two identical croissants on one day, one already in the ledger:
        // exactly one of the new pair is a duplicate (#2421).
        let coffee = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &[]);
        let dups = import(
            &[coffee.clone(), coffee.clone()],
            std::slice::from_ref(&coffee),
        );
        assert_eq!(dups.len(), 1, "{dups:?}");
        assert_eq!(dups[0].new_index, 0);
        assert_eq!(dups[0].reason, DuplicateReason::ExactText);

        // Two existing absorb two new; a third new survives.
        let dups = import(
            &[coffee.clone(), coffee.clone(), coffee.clone()],
            &[coffee.clone(), coffee],
        );
        assert_eq!(
            dups.iter()
                .map(|d| (d.new_index, d.existing_index))
                .collect::<Vec<_>>(),
            vec![(0, 0), (1, 1)],
        );
    }

    #[test]
    fn matching_is_scoped_to_the_importer_account_and_commodity() {
        let existing = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &[]);
        // Another account: not a candidate at all.
        let other = txn(
            "2024-01-15",
            "Croissant",
            "Assets:Other:Bank",
            "-2.50",
            "EUR",
            &[],
        );
        assert!(import(&[other], std::slice::from_ref(&existing)).is_empty());
        // Same account, another commodity.
        let usd = txn("2024-01-15", "Croissant", BANK, "-2.50", "USD", &[]);
        assert!(import(&[usd], std::slice::from_ref(&existing)).is_empty());
        // The account posting decides, not the first posting: an existing
        // entry written with the expense leg first still matches.
        let mut reordered = existing;
        reordered.postings.reverse();
        let same = txn("2024-01-15", "Croissant", BANK, "-2.5", "EUR", &[]);
        assert_eq!(import(&[same], &[reordered]).len(), 1);
    }

    #[test]
    fn a_shared_id_link_is_decisive() {
        // Same id: a duplicate even though date, amount and text all differ.
        let existing = txn(
            "2024-01-14",
            "POS 4411 BAKERY",
            BANK,
            "-2.50",
            "EUR",
            &["ofx-77"],
        );
        let new = txn("2024-01-15", "Croissant", BANK, "-2.49", "EUR", &["ofx-77"]);
        let dups = import(&[new], std::slice::from_ref(&existing));
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].reason, DuplicateReason::IdLink("ofx-77".into()));

        // Different ids in one namespace: two transactions, however alike.
        let a = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["csv-1"]);
        let b = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["csv-2"]);
        assert!(import(&[b], std::slice::from_ref(&a)).is_empty());

        // An id on one side only (a ledger imported before ids existed): text decides.
        let plain = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &[]);
        assert_eq!(
            import(std::slice::from_ref(&a), std::slice::from_ref(&plain)).len(),
            1
        );
        assert_eq!(import(&[plain], std::slice::from_ref(&a)).len(), 1);

        // Ids in different namespaces do not contradict each other.
        let ofx = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["ofx-9"]);
        assert_eq!(import(&[ofx], std::slice::from_ref(&a)).len(), 1);

        // A link outside the id namespaces is not an id.
        let tagged = txn(
            "2024-01-15",
            "Croissant",
            BANK,
            "-2.50",
            "EUR",
            &["invoice-1"],
        );
        let tagged2 = txn(
            "2024-01-15",
            "Croissant",
            BANK,
            "-2.50",
            "EUR",
            &["invoice-2"],
        );
        assert_eq!(import(&[tagged2], &[tagged]).len(), 1);
    }

    #[test]
    fn stronger_evidence_claims_an_existing_transaction_first() {
        // The new id-carrying row owns the existing one, even though an
        // earlier new row matches it by text.
        let existing = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["csv-1"]);
        let by_text = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &[]);
        let by_id = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["csv-1"]);
        let dups = import(&[by_text, by_id], std::slice::from_ref(&existing));
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].new_index, 1);

        // An exact text match outranks an earlier fuzzy one.
        let existing = txn("2024-01-15", "coffee shop", BANK, "-4.00", "EUR", &[]);
        let fuzzy = txn("2024-01-15", "coffee", BANK, "-4.00", "EUR", &[]);
        let exact = txn("2024-01-15", "Coffee Shop", BANK, "-4.00", "EUR", &[]);
        let dups = import(&[fuzzy, exact], std::slice::from_ref(&existing));
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].new_index, 1);
        assert_eq!(dups[0].reason, DuplicateReason::ExactText);
    }

    #[test]
    fn unscoped_matching_compares_the_first_posting_account_and_commodity() {
        let usd = make_directive("2024-01-15", Some("Store"), "Groceries", "-50.00");
        let mut eur = usd.clone();
        if let Directive::Transaction(t) = &mut eur {
            t.postings[0].units = Some(rustledger_core::IncompleteAmount::from(
                rustledger_core::Amount::new(Decimal::new(-5000, 2), "EUR"),
            ));
        }
        let config = FuzzyDedupConfig::default();
        assert!(
            find_fuzzy_duplicates(
                std::slice::from_ref(&eur),
                std::slice::from_ref(&usd),
                &config
            )
            .is_empty()
        );
        // And the multiset rule holds here too.
        let pair = [usd.clone(), usd.clone()];
        assert_eq!(
            find_fuzzy_duplicates(&pair, std::slice::from_ref(&usd), &config).len(),
            1
        );
    }

    #[test]
    fn id_link_sanitizes_and_rejects_empty_ids() {
        assert_eq!(id_link("csv-", " tx_00A1 "), Some("csv-tx_00A1".into()));
        assert_eq!(id_link("csv-", "a b:c"), Some("csv-a-b-c".into()));
        assert_eq!(id_link("csv-", "  "), None);
        assert_eq!(id_link("csv-", "./_"), None);
    }
}
