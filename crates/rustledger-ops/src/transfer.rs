//! Transfer matching across accounts.
//!
//! Detects transfer pairs — transactions that represent the same real-world
//! money movement appearing in two different account imports (e.g., a $500
//! debit in checking and a $500 credit in savings on the same day).
//!
//! The matcher finds pairs based on:
//! - Opposite-sign amounts (within tolerance)
//! - Same currency
//! - Dates within a configurable window
//! - Narration keyword boosting (strong: TRANSFER/XFER/INTERNAL/SWEEP/MOVE;
//!   weak: PAYMENT/ACH/WIRE — these only boost on same-date matches because
//!   they alone are too eager: every credit-card payment, every direct
//!   deposit, etc.)
//!
//! Pairs that already share a `^link:` tag are skipped — re-running the
//! detector against an already-linked ledger is a no-op (idempotent).

use rust_decimal::Decimal;
use rustledger_plugin_types::{DirectiveData, DirectiveWrapper};
use std::collections::{BTreeMap, HashSet};
use std::str::FromStr;

/// Configuration for transfer matching.
#[derive(Debug, Clone)]
pub struct TransferConfig {
    /// Maximum number of days between matched transactions (default: 3).
    pub date_window_days: i64,
    /// Amount tolerance for matching (default: 0.01).
    pub amount_tolerance: Decimal,
}

impl Default for TransferConfig {
    fn default() -> Self {
        Self {
            date_window_days: 3,
            amount_tolerance: Decimal::new(1, 2), // 0.01
        }
    }
}

/// A detected transfer pair.
#[derive(Debug, Clone)]
pub struct TransferMatch {
    /// Index of the source transaction (debit side) in the first group.
    pub from_group: usize,
    /// Index within that group's directives.
    pub from_index: usize,
    /// Account name of the debit side (if available).
    pub from_account: Option<String>,
    /// Source file of the debit side (if available).
    pub from_filename: Option<String>,
    /// Source line number of the debit side (if available).
    pub from_lineno: Option<u32>,
    /// Index of the destination transaction (credit side) in the second group.
    pub to_group: usize,
    /// Index within that group's directives.
    pub to_index: usize,
    /// Account name of the credit side (if available).
    pub to_account: Option<String>,
    /// Source file of the credit side (if available).
    pub to_filename: Option<String>,
    /// Source line number of the credit side (if available).
    pub to_lineno: Option<u32>,
    /// The matched amount (absolute value).
    pub amount: Decimal,
    /// The matched currency.
    pub currency: String,
    /// Confidence score (0.0 to 1.0).
    pub confidence: f64,
    /// Date of the debit (from) side, in YYYY-MM-DD form.
    pub date: String,
}

/// Find transfer pairs across multiple account import groups.
///
/// Each group is a `(account_name, directives)` pair. Returns matches between
/// groups (never within a single group). For "match all transfers across this
/// ledger regardless of file boundaries," use `find_transfers_in_ledger`.
///
/// Idempotent: pairs whose transactions already share at least one `^link:`
/// tag are skipped.
#[must_use]
pub fn find_transfers(
    groups: &[(String, Vec<DirectiveWrapper>)],
    config: &TransferConfig,
) -> Vec<TransferMatch> {
    let mut matches = Vec::new();
    // Track all matched directives globally so a directive in one group
    // cannot be matched by multiple other groups.
    let mut globally_matched: HashSet<(usize, usize)> = HashSet::new();

    let group_accounts: Vec<&str> = groups.iter().map(|(a, _)| a.as_str()).collect();

    // Compare each pair of groups
    for (g1, (_, directives1)) in groups.iter().enumerate() {
        for (g2, (_, directives2)) in groups.iter().enumerate() {
            if g2 <= g1 {
                continue; // Avoid duplicate comparisons
            }

            find_matches_between(
                g1,
                directives1,
                g2,
                directives2,
                &group_accounts,
                config,
                &mut matches,
                &mut globally_matched,
            );
        }
    }

    matches
}

/// Find transfer pairs across all accounts in a flat directive list.
///
/// Groups directives by the **first posting's account** (the "owning"
/// account of an imported transaction is conventionally the first posting)
/// and runs the same cross-group matching as `find_transfers`. Use this
/// when you have one combined ledger and want all internal transfers
/// detected without manually splitting by file.
///
/// Non-transaction directives (Open, Balance, Pad, etc.) are skipped at
/// grouping time. Transactions whose first posting has no units are still
/// grouped (by that posting's account), but they can never match — the
/// per-pair predicate requires units on both sides.
///
/// Idempotent: pairs whose transactions already share at least one `^link:`
/// tag are skipped.
#[must_use]
pub fn find_transfers_in_ledger(
    directives: &[DirectiveWrapper],
    config: &TransferConfig,
) -> Vec<TransferMatch> {
    // BTreeMap for deterministic group ordering by account name.
    let mut by_account: BTreeMap<String, Vec<DirectiveWrapper>> = BTreeMap::new();
    for d in directives {
        if let Some(account) = first_posting_account(d) {
            by_account
                .entry(account.to_string())
                .or_default()
                .push(d.clone());
        }
    }
    let groups: Vec<(String, Vec<DirectiveWrapper>)> = by_account.into_iter().collect();
    find_transfers(&groups, config)
}

/// Find matching transactions between two directive lists.
#[allow(clippy::too_many_arguments)]
fn find_matches_between(
    g1: usize,
    directives1: &[DirectiveWrapper],
    g2: usize,
    directives2: &[DirectiveWrapper],
    group_accounts: &[&str],
    config: &TransferConfig,
    matches: &mut Vec<TransferMatch>,
    globally_matched: &mut HashSet<(usize, usize)>,
) {
    for (i, d1) in directives1.iter().enumerate() {
        if globally_matched.contains(&(g1, i)) {
            continue;
        }

        let Some((amount1, currency1)) = first_posting_amount_currency(d1) else {
            continue;
        };

        for (j, d2) in directives2.iter().enumerate() {
            if globally_matched.contains(&(g2, j)) {
                continue;
            }

            let Some((amount2, currency2)) = first_posting_amount_currency(d2) else {
                continue;
            };

            // Must be same currency
            if currency1 != currency2 {
                continue;
            }

            // Must be opposite signs and similar absolute amounts
            let sum = (amount1 + amount2).abs();
            if sum > config.amount_tolerance {
                continue;
            }

            // Must be within date window
            if !within_date_window(&d1.date, &d2.date, config.date_window_days) {
                continue;
            }

            // Idempotency: skip if both txns already share a link. Mark both
            // as "used" so they can't pair with a third party and produce a
            // redundant match.
            if shares_link(d1, d2) {
                globally_matched.insert((g1, i));
                globally_matched.insert((g2, j));
                break;
            }

            let same_date = d1.date == d2.date;

            // Compute confidence.
            let mut confidence: f64 = 0.7; // Base for amount + date match

            let kw1 = classify_keywords(d1);
            let kw2 = classify_keywords(d2);
            let strong = kw1.strong || kw2.strong;
            let weak = kw1.weak || kw2.weak;
            if strong || (weak && same_date) {
                confidence += 0.2;
            }

            if same_date {
                confidence += 0.1;
            }

            let confidence = confidence.min(1.0);

            // Determine from/to based on sign
            let (from_group, from_index, to_group, to_index, from, to) =
                if amount1.is_sign_negative() {
                    (g1, i, g2, j, d1, d2)
                } else {
                    (g2, j, g1, i, d2, d1)
                };

            matches.push(TransferMatch {
                from_group,
                from_index,
                from_account: group_accounts
                    .get(from_group)
                    .map(|s| (*s).to_string())
                    .filter(|s| !s.is_empty()),
                from_filename: from.filename.clone(),
                from_lineno: from.lineno,
                to_group,
                to_index,
                to_account: group_accounts
                    .get(to_group)
                    .map(|s| (*s).to_string())
                    .filter(|s| !s.is_empty()),
                to_filename: to.filename.clone(),
                to_lineno: to.lineno,
                amount: amount1.abs(),
                currency: currency1.to_string(),
                confidence,
                date: from.date.clone(),
            });

            globally_matched.insert((g1, i));
            globally_matched.insert((g2, j));
            break; // One match per source transaction
        }
    }
}

/// Extract the first posting's amount and currency from a directive.
fn first_posting_amount_currency(d: &DirectiveWrapper) -> Option<(Decimal, &str)> {
    if let DirectiveData::Transaction(txn) = &d.data
        && let Some(posting) = txn.postings.first()
        && let Some(units) = &posting.units
    {
        let amount = Decimal::from_str(&units.number).ok()?;
        return Some((amount, &units.currency));
    }
    None
}

/// Extract the first posting's account name from a directive.
fn first_posting_account(d: &DirectiveWrapper) -> Option<&str> {
    if let DirectiveData::Transaction(txn) = &d.data
        && let Some(posting) = txn.postings.first()
    {
        return Some(posting.account.as_str());
    }
    None
}

/// True if both transactions share at least one `^link:` tag.
///
/// `link` strings in `TransactionData::links` are stored without the `^`
/// sigil, so we compare them directly.
fn shares_link(a: &DirectiveWrapper, b: &DirectiveWrapper) -> bool {
    let (DirectiveData::Transaction(txn_a), DirectiveData::Transaction(txn_b)) = (&a.data, &b.data)
    else {
        return false;
    };
    if txn_a.links.is_empty() || txn_b.links.is_empty() {
        return false;
    }
    let set: HashSet<&str> = txn_a.links.iter().map(String::as_str).collect();
    txn_b.links.iter().any(|l| set.contains(l.as_str()))
}

/// Check if two date strings are within a given window (in days).
fn within_date_window(date1: &str, date2: &str, days: i64) -> bool {
    // Simple date comparison for YYYY-MM-DD format
    let d1: jiff::civil::Date = match date1.parse() {
        Ok(d) => d,
        Err(_) => return false,
    };
    let d2: jiff::civil::Date = match date2.parse() {
        Ok(d) => d,
        Err(_) => return false,
    };
    let Ok(span) = d2.since(d1) else {
        return false;
    };
    let diff = span.get_days().abs();
    i64::from(diff) <= days
}

/// Strong transfer keywords: explicit transfer language. Boost unconditionally.
const STRONG_KEYWORDS: &[&str] = &["transfer", "xfer", "internal", "sweep", "move"];

/// Weak keywords: appear on transfers but also on many non-transfers (every
/// credit-card payment has "payment"; every direct-deposit paycheck is an
/// ACH credit). Boost only when the two sides also match on date.
const WEAK_KEYWORDS: &[&str] = &["payment", "ach", "wire"];

#[derive(Default, Clone, Copy)]
struct KeywordHit {
    strong: bool,
    weak: bool,
}

fn classify_keywords(d: &DirectiveWrapper) -> KeywordHit {
    let DirectiveData::Transaction(txn) = &d.data else {
        return KeywordHit::default();
    };
    let mut hit = KeywordHit::default();
    let narration_lower = txn.narration.to_lowercase();
    let payee_lower = txn.payee.as_deref().unwrap_or("").to_lowercase();
    let scan = |needles: &[&str]| -> bool {
        needles
            .iter()
            .any(|kw| narration_lower.contains(kw) || payee_lower.contains(kw))
    };
    hit.strong = scan(STRONG_KEYWORDS);
    hit.weak = scan(WEAK_KEYWORDS);
    hit
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_plugin_types::{AmountData, PostingData, TransactionData};

    fn make_txn(date: &str, narration: &str, amount: &str, currency: &str) -> DirectiveWrapper {
        make_txn_with(date, narration, amount, currency, "Assets:Bank", vec![])
    }

    fn make_txn_with(
        date: &str,
        narration: &str,
        amount: &str,
        currency: &str,
        account: &str,
        links: Vec<String>,
    ) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: narration.to_string(),
                tags: vec![],
                links,
                metadata: vec![],
                postings: vec![PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: amount.to_string(),
                        currency: currency.to_string(),
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

    fn make_txn_loc(
        date: &str,
        narration: &str,
        amount: &str,
        currency: &str,
        account: &str,
        filename: &str,
        lineno: u32,
    ) -> DirectiveWrapper {
        let mut d = make_txn_with(date, narration, amount, currency, account, vec![]);
        d.filename = Some(filename.to_string());
        d.lineno = Some(lineno);
        d
    }

    #[test]
    fn matches_opposite_amounts_same_date() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn(
                    "2024-01-15",
                    "Transfer to savings",
                    "-500.00",
                    "USD",
                )],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn(
                    "2024-01-15",
                    "Transfer from checking",
                    "500.00",
                    "USD",
                )],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].amount, Decimal::new(50000, 2));
        assert!(matches[0].confidence > 0.8); // Strong keyword + exact date
    }

    #[test]
    fn matches_within_date_window() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "ACH payment", "-200.00", "USD")],
            ),
            (
                "Assets:CreditCard".to_string(),
                vec![make_txn("2024-01-17", "Payment received", "200.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn no_match_outside_date_window() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "-500.00", "USD")],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-25", "Transfer", "500.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert!(matches.is_empty());
    }

    #[test]
    fn no_match_different_currency() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "-500.00", "USD")],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "500.00", "EUR")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert!(matches.is_empty());
    }

    #[test]
    fn no_match_same_sign() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "Deposit", "500.00", "USD")],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-15", "Deposit", "500.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert!(matches.is_empty());
    }

    #[test]
    fn no_match_different_amounts() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "-500.00", "USD")],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "499.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert!(matches.is_empty());
    }

    #[test]
    fn transfer_keywords_boost_confidence() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn(
                    "2024-01-15",
                    "TRANSFER TO SAVINGS",
                    "-500.00",
                    "USD",
                )],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn(
                    "2024-01-15",
                    "TRANSFER FROM CHECKING",
                    "500.00",
                    "USD",
                )],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        // Strong keyword + exact date = max
        assert!(matches[0].confidence >= 0.9);
    }

    #[test]
    fn no_keywords_lower_confidence() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "Something", "-500.00", "USD")],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-17", "Something else", "500.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        // No keywords, different dates = base only
        assert!(matches[0].confidence < 0.8);
    }

    #[test]
    fn multiple_transfers() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![
                    make_txn("2024-01-15", "Transfer 1", "-500.00", "USD"),
                    make_txn("2024-01-20", "Transfer 2", "-300.00", "USD"),
                ],
            ),
            (
                "Assets:Savings".to_string(),
                vec![
                    make_txn("2024-01-15", "Transfer 1", "500.00", "USD"),
                    make_txn("2024-01-20", "Transfer 2", "300.00", "USD"),
                ],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 2);
    }

    #[test]
    fn one_to_one_matching() {
        // Same amount twice — single savings entry only matches one of them.
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![
                    make_txn("2024-01-15", "Transfer", "-500.00", "USD"),
                    make_txn("2024-01-15", "Transfer", "-500.00", "USD"),
                ],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "500.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn three_groups() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "-500.00", "USD")],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-15", "Transfer", "500.00", "USD")],
            ),
            (
                "Assets:CreditCard".to_string(),
                vec![make_txn("2024-01-15", "Payment", "200.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        // Checking↔Savings matches; CreditCard has no opposite-sign match
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn empty_groups() {
        let groups: Vec<(String, Vec<DirectiveWrapper>)> = vec![];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert!(matches.is_empty());
    }

    // ─── Phase 0 — new behavior ────────────────────────────────────────────

    #[test]
    fn in_ledger_groups_by_first_posting_account() {
        // Single flat list, transfers between accounts inside it.
        let directives = vec![
            make_txn_with(
                "2024-01-15",
                "Transfer to savings",
                "-500.00",
                "USD",
                "Assets:Checking",
                vec![],
            ),
            make_txn_with(
                "2024-01-15",
                "Transfer from checking",
                "500.00",
                "USD",
                "Assets:Savings",
                vec![],
            ),
        ];
        let matches = find_transfers_in_ledger(&directives, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].from_account.as_deref(), Some("Assets:Checking"));
        assert_eq!(matches[0].to_account.as_deref(), Some("Assets:Savings"));
    }

    #[test]
    fn in_ledger_does_not_match_within_same_account() {
        // Two txns on the same account can't be a transfer between accounts.
        let directives = vec![
            make_txn_with(
                "2024-01-15",
                "Out",
                "-500.00",
                "USD",
                "Assets:Checking",
                vec![],
            ),
            make_txn_with(
                "2024-01-15",
                "In",
                "500.00",
                "USD",
                "Assets:Checking",
                vec![],
            ),
        ];
        let matches = find_transfers_in_ledger(&directives, &TransferConfig::default());
        assert!(matches.is_empty());
    }

    #[test]
    fn transfer_match_carries_filename_and_lineno() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn_loc(
                    "2024-01-15",
                    "Transfer",
                    "-500.00",
                    "USD",
                    "Assets:Checking",
                    "checking.bean",
                    42,
                )],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn_loc(
                    "2024-01-15",
                    "Transfer",
                    "500.00",
                    "USD",
                    "Assets:Savings",
                    "savings.bean",
                    18,
                )],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        let m = &matches[0];
        assert_eq!(m.from_filename.as_deref(), Some("checking.bean"));
        assert_eq!(m.from_lineno, Some(42));
        assert_eq!(m.to_filename.as_deref(), Some("savings.bean"));
        assert_eq!(m.to_lineno, Some(18));
    }

    #[test]
    fn already_linked_pair_is_skipped() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn_with(
                    "2024-01-15",
                    "Transfer",
                    "-500.00",
                    "USD",
                    "Assets:Checking",
                    vec!["xfer-001".to_string()],
                )],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn_with(
                    "2024-01-15",
                    "Transfer",
                    "500.00",
                    "USD",
                    "Assets:Savings",
                    vec!["xfer-001".to_string()],
                )],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert!(
            matches.is_empty(),
            "already-linked pair must not be re-detected; got {matches:?}"
        );
    }

    #[test]
    fn unrelated_links_do_not_block_match() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn_with(
                    "2024-01-15",
                    "Transfer",
                    "-500.00",
                    "USD",
                    "Assets:Checking",
                    vec!["batch-import-A".to_string()],
                )],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn_with(
                    "2024-01-15",
                    "Transfer",
                    "500.00",
                    "USD",
                    "Assets:Savings",
                    vec!["batch-import-B".to_string()],
                )],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn weak_keyword_does_not_boost_when_dates_differ() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "PAYMENT", "-200.00", "USD")],
            ),
            (
                "Liabilities:Card".to_string(),
                vec![make_txn("2024-01-17", "PAYMENT", "200.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        assert!(
            (matches[0].confidence - 0.7).abs() < 1e-9,
            "weak keyword + different dates must stay at base 0.7; got {}",
            matches[0].confidence
        );
    }

    #[test]
    fn weak_keyword_boosts_on_same_date() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "PAYMENT", "-200.00", "USD")],
            ),
            (
                "Liabilities:Card".to_string(),
                vec![make_txn("2024-01-15", "PAYMENT", "200.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        // 0.7 base + 0.2 weak + 0.1 same-date = 1.0
        assert!(matches[0].confidence > 0.95);
    }

    #[test]
    fn strong_keyword_boosts_even_on_different_dates() {
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![make_txn("2024-01-15", "TRANSFER", "-500.00", "USD")],
            ),
            (
                "Assets:Savings".to_string(),
                vec![make_txn("2024-01-17", "TRANSFER", "500.00", "USD")],
            ),
        ];
        let matches = find_transfers(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        // 0.7 base + 0.2 strong = 0.9 (no same-date bonus)
        assert!(
            (matches[0].confidence - 0.9).abs() < 1e-9,
            "strong keyword + different dates: expect 0.9, got {}",
            matches[0].confidence
        );
    }
}
