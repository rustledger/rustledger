//! Duplicate transaction detection.
//!
//! Provides three deduplication strategies:
//!
//! - **Structural** — exact hash match using [`crate::fingerprint::structural_hash`].
//!   Finds transactions that are byte-for-byte identical (excluding metadata).
//!
//! - **Import** — [`find_import_duplicates`] matches imported transactions
//!   against an existing ledger: shared id links (`^ofx-…`, `^csv-…`,
//!   `^wasm-<importer>/…`) with
//!   the same account, commodity and amount first, then the same date,
//!   account, commodity and amount with identical or similar payee/narration
//!   text. Existing transactions are a multiset, so each
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

/// Link prefix marking a WASM importer's transaction id; the full link is
/// `wasm-<importer>/<id>`, built by [`wasm_id_link`] (#2519).
pub use rustledger_plugin_types::WASM_ID_LINK_PREFIX;

/// The WASM importer's id link, `wasm-<importer>/<id>` (#2519).
pub use rustledger_plugin_types::wasm_id_link;

/// The fixed link prefixes that mark a source-assigned transaction id. Each
/// is one namespace.
const FIXED_ID_LINK_PREFIXES: &[&str] = &[OFX_ID_LINK_PREFIX, CSV_ID_LINK_PREFIX];

/// The id namespace a link belongs to, or `None` when it is not an id link.
///
/// Ids are only compared within one namespace, so an OFX id and a CSV id
/// never contradict each other (a bank whose export moved from OFX to CSV
/// still dedups by text). The namespaces are `ofx-`, `csv-`, and one per
/// WASM importer, `wasm-<importer>/` (up to the first `/`), so two WASM
/// importers' ids never contradict each other either. A `wasm-` link with no
/// `/`, or nothing on either side of it, is not an id link.
fn id_namespace(link: &str) -> Option<&str> {
    if let Some(prefix) = FIXED_ID_LINK_PREFIXES
        .iter()
        .find(|p| link.starts_with(**p))
    {
        return Some(prefix);
    }
    let rest = link.strip_prefix(WASM_ID_LINK_PREFIX)?;
    let slash = rest.find('/')?;
    (slash > 0 && slash + 1 < rest.len()).then(|| &link[..=WASM_ID_LINK_PREFIX.len() + slash])
}

/// Render a source transaction id as a beancount link under `prefix`, or
/// `None` if nothing usable survives.
///
/// The canonical sanitizer lives in `rustledger-plugin-types`
/// ([`rustledger_plugin_types::id_link`]) so a WASM importer, which cannot
/// depend on this crate, builds its links with the same rule.
///
/// # Example
///
/// ```
/// use rustledger_ops::dedup::{CSV_ID_LINK_PREFIX, id_link};
///
/// assert_eq!(id_link(CSV_ID_LINK_PREFIX, " tx_00A1 ").as_deref(), Some("csv-tx_00A1"));
/// assert_eq!(id_link(CSV_ID_LINK_PREFIX, "a b:c").as_deref(), Some("csv-a-b-c"));
/// assert_eq!(id_link(CSV_ID_LINK_PREFIX, "  "), None);
/// ```
#[must_use]
pub fn id_link(prefix: &str, raw: &str) -> Option<String> {
    rustledger_plugin_types::id_link(prefix, raw)
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
#[non_exhaustive]
pub enum DuplicateReason {
    /// Both carry this id link (`^ofx-…`, `^csv-…`, `^wasm-<importer>/…`) and
    /// the same account,
    /// commodity and amount; the date and text may differ.
    IdLink(String),
    /// Same date, account, commodity and amount, and identical payee/narration.
    ExactText,
    /// Same date, account, commodity and amount, and similar payee/narration.
    FuzzyText,
    /// Same date, account, commodity and amount, and NEITHER side has a payee
    /// or narration, so nothing but the money says they are the same. Kept
    /// apart from [`Self::ExactText`] so a report can flag these: two distinct
    /// description-less rows on one day for one amount are indistinguishable.
    AmountOnly,
}

impl std::fmt::Display for DuplicateReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdLink(link) => write!(f, "same id link ^{link}"),
            Self::ExactText => f.write_str("same date, amount and text"),
            Self::FuzzyText => f.write_str("same date and amount, similar text"),
            Self::AmountOnly => {
                f.write_str("same date and amount, and neither has a payee or narration to compare")
            }
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
/// When the account's leg is split over several postings, its net movement
/// per commodity is compared too. A new transaction that itself never touches
/// `account` (a WASM importer may post elsewhere) is compared unscoped, as
/// below, rather than skipping dedup. With `None` (a caller with no importer
/// account, such as the component's `session.dedup`), each transaction's first
/// posting — its account, commodity and amount — is compared instead.
///
/// Matching runs in three passes, strongest evidence first, so a weak match
/// can never claim an existing transaction a stronger one needed:
///
/// 1. **Id links.** A shared `^ofx-…` / `^csv-…` / `^wasm-<importer>/…` link
///    is a duplicate whatever
///    the date or text say, provided the account, commodity and amount agree
///    (so two different ids that sanitize to the same link cannot drop a
///    different transaction).
/// 2. **Exact text.** Same date, commodity and amount, identical
///    (case-insensitive) payee + narration. When both are empty the match
///    rests on the money alone and is reported as
///    [`DuplicateReason::AmountOnly`].
/// 3. **Fuzzy text.** Same date, commodity and amount, similar payee +
///    narration (see [`FuzzyDedupConfig`]).
///
/// Passes 2 and 3 never pair two transactions that both carry ids in the same
/// namespace: equal ids were matched in pass 1, so different ids mean two
/// distinct transactions however alike they look. When only one side has an
/// id (a ledger imported before ids were emitted), the text passes decide.
///
/// Rows are visited, and candidates offered, in a canonical content order, so
/// which transactions survive depends only on the contents of the statement
/// and the ledger, never on the order either lists them in. Identical empty
/// text counts as identical, so a statement with no description column still
/// re-imports to nothing.
///
/// Existing keys are computed once and bucketed by date, account, commodity
/// and amount, so the cost is near-linear in `new + existing` rather than
/// their product (#2422).
///
/// The result is ordered by `new_index`.
///
/// # Example
///
/// ```
/// use rust_decimal::Decimal;
/// use rustledger_core::{Amount, Posting, Transaction};
/// use rustledger_ops::dedup::{DuplicateReason, FuzzyDedupConfig, find_import_duplicates};
///
/// let coffee = || {
///     Transaction::new("2024-01-15".parse().unwrap(), "Coffee")
///         .with_synthesized_posting(Posting::new(
///             "Assets:Bank",
///             Amount::new(Decimal::new(-450, 2), "EUR"),
///         ))
///         .with_synthesized_posting(Posting::auto("Expenses:Food"))
/// };
/// // Two identical coffees on the statement, one already in the ledger.
/// let (a, b, booked) = (coffee(), coffee(), coffee());
/// let dups = find_import_duplicates(
///     &[&a, &b],
///     &[&booked],
///     Some("Assets:Bank"),
///     &FuzzyDedupConfig::default(),
/// );
/// // The booked one absorbs exactly one row; the other is new.
/// assert_eq!(dups.len(), 1);
/// assert_eq!(dups[0].new_index, 0);
/// assert_eq!(dups[0].reason, DuplicateReason::ExactText);
/// ```
#[must_use]
pub fn find_import_duplicates(
    new: &[&Transaction],
    existing: &[&Transaction],
    account: Option<&str>,
    config: &FuzzyDedupConfig,
) -> Vec<ImportDuplicate> {
    let threshold = config.text_similarity_threshold;

    let scoped = Index::build(existing, account);
    let new_keys = new_keys(new, account);
    // Built only if some new row is out of scope (see `new_keys`).
    let unscoped = new_keys
        .iter()
        .flatten()
        .any(|(_, in_scope)| !in_scope)
        .then(|| Index::build(existing, None));
    let index_for = |in_scope: bool| -> &Index<'_> {
        if in_scope {
            &scoped
        } else {
            unscoped.as_ref().unwrap_or(&scoped)
        }
    };

    let mut consumed = vec![false; existing.len()];
    let mut matched: Vec<Option<(usize, DuplicateReason)>> = vec![None; new.len()];

    // Visit new rows in a canonical content order (input order only among
    // identical rows), and candidates likewise (see `Index::build`, ranked by `TxnKey::rank`), so the
    // rows that survive are a function of the two statements' CONTENTS: the
    // order rows appear in the file or the ledger cannot change which
    // transactions are kept. Without this, the greedy fuzzy pass let an
    // earlier row claim the entry a later, better row needed.
    let ranks: Vec<_> = new_keys
        .iter()
        .map(|k| k.as_ref().map(|(k, _)| k.rank()))
        .collect();
    let mut order: Vec<usize> = (0..new.len()).collect();
    order.sort_by(|&a, &b| ranks[a].cmp(&ranks[b]));

    // Pass 1: shared id links. The id decides whatever the date or text say,
    // but the money must agree: a sanitized link can collide (`a b` and `a:b`
    // both become `…-a-b`), and a collision must not drop a different
    // transaction. A bank's id for one transaction does not change amount.
    for &new_i in &order {
        let Some((key, in_scope)) = &new_keys[new_i] else {
            continue;
        };
        let index = index_for(*in_scope);
        'ids: for id in &key.ids {
            for &ex in index.by_id.get(id).map_or(&[][..], Vec::as_slice) {
                if consumed[ex] {
                    continue;
                }
                let Some(ek) = &index.keys[ex] else { continue };
                if !same_money(&key.amounts, &ek.amounts) {
                    continue;
                }
                consumed[ex] = true;
                matched[new_i] = Some((ex, DuplicateReason::IdLink((*id).to_string())));
                break 'ids;
            }
        }
    }

    // Passes 2 and 3: same amount bucket, text decides.
    for exact in [true, false] {
        for &new_i in &order {
            if matched[new_i].is_some() {
                continue;
            }
            let Some((key, in_scope)) = &new_keys[new_i] else {
                continue;
            };
            let index = index_for(*in_scope);
            'amounts: for amount in &key.amounts {
                for &ex in index.by_amount.get(amount).map_or(&[][..], Vec::as_slice) {
                    if consumed[ex] {
                        continue;
                    }
                    let Some(ek) = &index.keys[ex] else {
                        continue;
                    };
                    if ids_conflict(&key.ids, &ek.ids) {
                        continue;
                    }
                    let hit = if exact {
                        // Equal text, empty included: a statement with no
                        // description column still re-imports to nothing.
                        key.text == ek.text
                    } else {
                        fuzzy_text_match(&key.text, &ek.text, threshold)
                    };
                    if hit {
                        consumed[ex] = true;
                        let reason = if exact && key.text.is_empty() {
                            DuplicateReason::AmountOnly
                        } else if exact {
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

/// Each new transaction's key, and whether it is in the importer's scope:
/// one that never touches `account` (a WASM importer may post elsewhere) is
/// keyed unscoped, by its first posting, instead of escaping dedup.
fn new_keys<'a>(new: &[&'a Transaction], account: Option<&str>) -> Vec<Option<(TxnKey<'a>, bool)>> {
    new.iter()
        .map(|t| match TxnKey::of(t, account) {
            Some(key) => Some((key, true)),
            None if account.is_some() => TxnKey::of(t, None).map(|key| (key, false)),
            None => None,
        })
        .collect()
}

/// Existing transactions keyed once for one scope.
struct Index<'a> {
    keys: Vec<Option<TxnKey<'a>>>,
    by_amount: HashMap<AmountKey<'a>, Vec<usize>>,
    by_id: HashMap<&'a str, Vec<usize>>,
}

impl<'a> Index<'a> {
    fn build(existing: &[&'a Transaction], account: Option<&str>) -> Self {
        let keys: Vec<Option<TxnKey<'a>>> =
            existing.iter().map(|t| TxnKey::of(t, account)).collect();
        let mut by_amount: HashMap<AmountKey<'a>, Vec<usize>> = HashMap::default();
        let mut by_id: HashMap<&'a str, Vec<usize>> = HashMap::default();
        for (i, key) in keys.iter().enumerate() {
            let Some(key) = key else { continue };
            for amount in &key.amounts {
                by_amount.entry(amount.clone()).or_default().push(i);
            }
            for id in &key.ids {
                by_id.entry(id).or_default().push(i);
            }
        }
        // Candidates in canonical content order (index order among equals),
        // so the ledger's directive order cannot decide which entry a row
        // claims.
        let ranks: Vec<_> = keys.iter().map(|k| k.as_ref().map(TxnKey::rank)).collect();
        for bucket in by_amount.values_mut().chain(by_id.values_mut()) {
            // Stable, so index order breaks ties between identical entries.
            bucket.sort_by(|&a, &b| ranks[a].cmp(&ranks[b]));
        }
        Self {
            keys,
            by_amount,
            by_id,
        }
    }
}

/// Whether two keys share an account, commodity and amount, on any date.
fn same_money(a: &[AmountKey<'_>], b: &[AmountKey<'_>]) -> bool {
    a.iter().any(|x| {
        b.iter()
            .any(|y| x.account == y.account && x.currency == y.currency && x.number == y.number)
    })
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
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct AmountKey<'a> {
    date: rustledger_core::NaiveDate,
    account: &'a str,
    currency: &'a str,
    /// Normalized, so `-2.5` and `-2.50` share a bucket.
    number: Decimal,
}

/// A transaction's dedup comparison key, computed once per transaction.
struct TxnKey<'a> {
    /// One entry per distinct posting on the scoped account, plus the
    /// account's net per commodity when it has several postings (or the first
    /// posting when unscoped). Usually exactly one.
    amounts: Vec<AmountKey<'a>>,
    /// Links in an id namespace (see [`id_namespace`]).
    ids: Vec<&'a str>,
    /// Lowercased payee + narration.
    text: String,
}

impl<'a> TxnKey<'a> {
    /// A content-only ordering key (borrowed, so ranking allocates nothing):
    /// sorting by it makes the match independent of input order.
    const fn rank(&self) -> (&str, &[&'a str], &[AmountKey<'a>]) {
        (
            self.text.as_str(),
            self.ids.as_slice(),
            self.amounts.as_slice(),
        )
    }

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
        let amounts: Vec<AmountKey<'a>> = match account {
            Some(account) => {
                let on_account: Vec<&'a rustledger_core::Posting> = txn
                    .postings
                    .iter()
                    .map(|p| &**p)
                    .filter(|p| p.account.as_str() == account)
                    .collect();
                if on_account.is_empty() {
                    return None;
                }
                let mut amounts: Vec<AmountKey<'a>> =
                    on_account.iter().filter_map(|p| amount_of(p)).collect();
                // A ledger entry may split the account's leg across several
                // postings (`-6.00` and `-4.00` for one `-10.00` statement
                // row), so the account's net movement per commodity is a key
                // too.
                if amounts.len() > 1 {
                    // `None` marks a commodity whose net overflows `Decimal`
                    // (only a crafted ledger gets there): it has no net key
                    // rather than panicking the import.
                    let mut nets: Vec<(&'a str, Option<AmountKey<'a>>)> = Vec::new();
                    for a in &amounts {
                        match nets.iter_mut().find(|(c, _)| *c == a.currency) {
                            Some((_, net)) => {
                                *net = net.take().and_then(|mut n| {
                                    n.number = n.number.checked_add(a.number)?;
                                    Some(n)
                                });
                            }
                            None => nets.push((a.currency, Some(a.clone()))),
                        }
                    }
                    for mut n in nets.into_iter().filter_map(|(_, n)| n) {
                        n.number = n.number.normalize();
                        amounts.push(n);
                    }
                }
                amounts
            }
            None => txn
                .postings
                .first()
                .and_then(|p| amount_of(p))
                .into_iter()
                .collect(),
        };
        let mut unique: Vec<AmountKey<'a>> = Vec::with_capacity(amounts.len());
        for a in amounts {
            if !unique.contains(&a) {
                unique.push(a);
            }
        }
        let amounts = unique;
        let ids = txn
            .links
            .iter()
            .map(rustledger_core::Link::as_str)
            .filter(|l| id_namespace(l).is_some())
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
    a.iter().filter_map(|l| id_namespace(l)).any(|ns| {
        let in_ns = |l: &&str| id_namespace(l) == Some(ns);
        let b_ns: Vec<&str> = b.iter().copied().filter(in_ns).collect();
        !b_ns.is_empty() && !a.iter().copied().filter(in_ns).any(|l| b_ns.contains(&l))
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

    /// #2519: a WASM importer's `wasm-<importer>/<id>` link is an id like
    /// `^ofx-` and `^csv-`: decisive when shared (with equal money), proof of
    /// two transactions when it differs within one importer, and silent
    /// across importers, which are separate namespaces.
    #[test]
    fn a_wasm_importer_id_link_is_an_id() {
        let id = |importer: &str, raw: &str| wasm_id_link(importer, raw).unwrap();
        let mt1 = id("MT940", "1");
        let existing = txn(
            "2024-01-14",
            "POS 4411 BAKERY",
            BANK,
            "-2.50",
            "EUR",
            &[&mt1],
        );
        let renamed = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &[&mt1]);
        let dups = import(&[renamed], std::slice::from_ref(&existing));
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].reason, DuplicateReason::IdLink(mt1.clone()));

        // Same importer, different id: two transactions, however alike.
        let a = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &[&mt1]);
        let b = txn(
            "2024-01-15",
            "Croissant",
            BANK,
            "-2.50",
            "EUR",
            &[&id("MT940", "2")],
        );
        assert!(import(&[b], std::slice::from_ref(&a)).is_empty());

        // Another importer's id (or an OFX one) does not contradict it: text
        // decides, as when a bank's export moves from one format to another.
        let camt = txn(
            "2024-01-15",
            "Croissant",
            BANK,
            "-2.50",
            "EUR",
            &[&id("camt", "2")],
        );
        assert_eq!(import(&[camt], std::slice::from_ref(&a)).len(), 1);
        let ofx = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["ofx-2"]);
        assert_eq!(import(&[ofx], std::slice::from_ref(&a)).len(), 1);

        // `wasm-` without an importer namespace is not an id: two such links
        // that differ do not make the rows distinct.
        let bare1 = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["wasm-1"]);
        let bare2 = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["wasm-2"]);
        assert_eq!(import(&[bare2], std::slice::from_ref(&bare1)).len(), 1);
    }

    #[test]
    fn id_namespaces() {
        assert_eq!(id_namespace("ofx-77"), Some("ofx-"));
        assert_eq!(id_namespace("csv-tx_1"), Some("csv-"));
        assert_eq!(id_namespace("wasm-mt940/2024/1"), Some("wasm-mt940/"));
        assert_eq!(id_namespace("wasm-mt940/"), None);
        assert_eq!(id_namespace("wasm-/1"), None);
        assert_eq!(id_namespace("wasm-1"), None);
        assert_eq!(id_namespace("invoice-1"), None);
    }

    #[test]
    fn a_shared_id_link_is_decisive() {
        // Same id and money: a duplicate even though date and text differ (a
        // pending row re-posted on another day, a rewritten narration).
        let existing = txn(
            "2024-01-14",
            "POS 4411 BAKERY",
            BANK,
            "-2.50",
            "EUR",
            &["ofx-77"],
        );
        let new = txn("2024-01-15", "Croissant", BANK, "-2.50", "EUR", &["ofx-77"]);
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

    #[test]
    fn an_id_collision_with_a_different_amount_is_not_a_duplicate() {
        // `a b` and `a:b` both sanitize to `csv-a-b`. Equal links but different
        // money: two transactions, kept — not a silent drop.
        assert_eq!(id_link("csv-", "a b"), id_link("csv-", "a:b"));
        let existing = txn("2024-01-15", "Coffee", BANK, "-4.00", "EUR", &["csv-a-b"]);
        let new = txn("2024-01-15", "Rent", BANK, "-900.00", "EUR", &["csv-a-b"]);
        assert!(import(&[new], std::slice::from_ref(&existing)).is_empty());
    }

    #[test]
    fn a_split_account_leg_matches_its_net_movement() {
        let mut existing = txn("2024-01-15", "Shop", BANK, "-6.00", "EUR", &[]);
        existing.postings.insert(
            1,
            rustledger_core::Spanned::synthesized(rustledger_core::Posting::new(
                BANK,
                rustledger_core::Amount::new(Decimal::new(-400, 2), "EUR"),
            )),
        );
        let new = txn("2024-01-15", "Shop", BANK, "-10.00", "EUR", &[]);
        assert_eq!(import(&[new], &[existing]).len(), 1);
    }

    #[test]
    fn a_transfer_already_booked_from_the_other_statement_is_a_duplicate() {
        // Imported first from the savings statement; the checking statement's
        // row for the same transfer would double-count the checking leg.
        let existing = txn(
            "2024-01-15",
            "Transfer to savings",
            "Assets:Savings",
            "100.00",
            "EUR",
            &[],
        );
        let mut existing = existing;
        existing.postings[1] =
            rustledger_core::Spanned::synthesized(rustledger_core::Posting::new(
                BANK,
                rustledger_core::Amount::new(Decimal::new(-10000, 2), "EUR"),
            ));
        let new = txn(
            "2024-01-15",
            "Transfer to savings",
            BANK,
            "-100.00",
            "EUR",
            &[],
        );
        assert_eq!(import(&[new], &[existing]).len(), 1);
    }

    #[test]
    fn a_new_transaction_outside_the_account_falls_back_to_unscoped() {
        // A WASM importer that posts somewhere other than the configured
        // account must still be deduplicated, by its first posting.
        let other = txn("2024-01-15", "Coffee", "Assets:Wallet", "-4.00", "EUR", &[]);
        assert_eq!(
            import(std::slice::from_ref(&other), std::slice::from_ref(&other)).len(),
            1
        );
    }

    #[test]
    fn row_order_does_not_decide_which_row_a_fuzzy_match_claims() {
        // "coffee" and "shop" both fuzzily match the one "coffee shop" entry.
        // Which survives must not depend on which the statement lists first.
        let existing = txn("2024-01-15", "coffee shop", BANK, "-4.00", "EUR", &[]);
        let a = txn("2024-01-15", "coffee", BANK, "-4.00", "EUR", &[]);
        let b = txn("2024-01-15", "shop", BANK, "-4.00", "EUR", &[]);
        let dropped = |new: &[Transaction]| {
            let d = import(new, std::slice::from_ref(&existing));
            assert_eq!(d.len(), 1);
            new[d[0].new_index].narration.as_str().to_string()
        };
        assert_eq!(dropped(&[a.clone(), b.clone()]), dropped(&[b, a]));
    }

    #[test]
    fn a_match_with_no_text_on_either_side_is_reported_as_amount_only() {
        let a = txn("2024-01-15", "", BANK, "-60.00", "EUR", &[]);
        let dups = import(std::slice::from_ref(&a), std::slice::from_ref(&a));
        assert_eq!(dups.len(), 1);
        assert_eq!(dups[0].reason, DuplicateReason::AmountOnly);
        // Text on one side only is not a match at all.
        let b = txn("2024-01-15", "ATM", BANK, "-60.00", "EUR", &[]);
        assert!(import(&[b], &[a]).is_empty());
    }

    #[test]
    fn a_split_leg_whose_net_overflows_does_not_panic() {
        let max = Decimal::MAX.to_string();
        let mut existing = txn("2024-01-15", "Shop", BANK, &max, "EUR", &[]);
        existing.postings.insert(
            1,
            rustledger_core::Spanned::synthesized(rustledger_core::Posting::new(
                BANK,
                rustledger_core::Amount::new(Decimal::MAX, "EUR"),
            )),
        );
        let new = txn("2024-01-15", "Shop", BANK, "-10.00", "EUR", &[]);
        assert!(import(&[new], &[existing]).is_empty());
    }
}
