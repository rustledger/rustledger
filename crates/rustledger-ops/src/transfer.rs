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
use rustledger_core::{Directive, IncompleteAmount, Link, NaiveDate};
use std::collections::{BTreeMap, HashSet};

/// A core [`Directive`] paired with its source location — the input to transfer
/// detection.
///
/// Carrying `(filename, lineno)` here keeps `ops` on `core::Directive` (no
/// plugin `DirectiveWrapper` deep clone of the whole directive) while still
/// letting [`TransferMatch`] report and rewrite `file:line`. The directive is
/// borrowed; only the small location is owned, so cloning a `LocatedDirective`
/// (e.g. during grouping) does not deep-copy the directive.
#[derive(Debug, Clone)]
pub struct LocatedDirective<'a> {
    /// The directive (borrowed — not cloned).
    pub directive: &'a Directive,
    /// Source file of the directive, if known.
    pub filename: Option<String>,
    /// 1-based source line of the directive, if known.
    pub lineno: Option<u32>,
}

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
    groups: &[(String, Vec<LocatedDirective<'_>>)],
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
    directives: &[LocatedDirective<'_>],
    config: &TransferConfig,
) -> Vec<TransferMatch> {
    // BTreeMap for deterministic group ordering by account name.
    // Cloning a `LocatedDirective` copies only the borrowed directive pointer
    // and the small location — it does not deep-copy the directive itself.
    let mut by_account: BTreeMap<String, Vec<LocatedDirective<'_>>> = BTreeMap::new();
    for d in directives {
        if let Some(account) = first_posting_account(d.directive) {
            by_account
                .entry(account.to_string())
                .or_default()
                .push(d.clone());
        }
    }
    let groups: Vec<(String, Vec<LocatedDirective<'_>>)> = by_account.into_iter().collect();
    find_transfers(&groups, config)
}

/// Find matching transactions between two directive lists.
#[allow(clippy::too_many_arguments)]
fn find_matches_between(
    g1: usize,
    directives1: &[LocatedDirective<'_>],
    g2: usize,
    directives2: &[LocatedDirective<'_>],
    group_accounts: &[&str],
    config: &TransferConfig,
    matches: &mut Vec<TransferMatch>,
    globally_matched: &mut HashSet<(usize, usize)>,
) {
    for (i, d1) in directives1.iter().enumerate() {
        if globally_matched.contains(&(g1, i)) {
            continue;
        }

        let Some((amount1, currency1, date1)) = first_posting_amount_currency(d1.directive) else {
            continue;
        };

        for (j, d2) in directives2.iter().enumerate() {
            if globally_matched.contains(&(g2, j)) {
                continue;
            }

            let Some((amount2, currency2, date2)) = first_posting_amount_currency(d2.directive)
            else {
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
            if !within_date_window(date1, date2, config.date_window_days) {
                continue;
            }

            // Idempotency: skip if both txns already share a link. Mark both
            // as "used" so they can't pair with a third party and produce a
            // redundant match.
            if shares_link(d1.directive, d2.directive) {
                globally_matched.insert((g1, i));
                globally_matched.insert((g2, j));
                break;
            }

            let same_date = date1 == date2;

            // Compute confidence.
            let mut confidence: f64 = 0.7; // Base for amount + date match

            let kw1 = classify_keywords(d1.directive);
            let kw2 = classify_keywords(d2.directive);
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
            let (from_group, from_index, to_group, to_index, from, to, from_date) =
                if amount1.is_sign_negative() {
                    (g1, i, g2, j, d1, d2, date1)
                } else {
                    (g2, j, g1, i, d2, d1, date2)
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
                date: from_date.to_string(),
            });

            globally_matched.insert((g1, i));
            globally_matched.insert((g2, j));
            break; // One match per source transaction
        }
    }
}

/// Extract the first posting's amount, currency, and the transaction date.
///
/// Mirrors the previous wire behaviour exactly: a `Complete` first posting
/// yields its number and currency; a `NumberOnly` posting yields its number
/// with an empty currency (the wire serialized currency to `""`); a
/// `CurrencyOnly` first posting is skipped (its wire number was `""`, which
/// failed to parse).
fn first_posting_amount_currency(d: &Directive) -> Option<(Decimal, &str, NaiveDate)> {
    let Directive::Transaction(txn) = d else {
        return None;
    };
    let posting = txn.postings.first()?;
    let (number, currency) = match posting.units.as_ref()? {
        IncompleteAmount::Complete(amount) => (amount.number, amount.currency.as_str()),
        IncompleteAmount::NumberOnly(number) => (*number, ""),
        IncompleteAmount::CurrencyOnly(_) => return None,
    };
    Some((number, currency, txn.date))
}

/// Extract the first posting's account name from a directive.
fn first_posting_account(d: &Directive) -> Option<&str> {
    if let Directive::Transaction(txn) = d
        && let Some(posting) = txn.postings.first()
    {
        return Some(posting.account.as_str());
    }
    None
}

/// True if both transactions share at least one `^link:` tag.
///
/// Links are interned without the `^` sigil, so we compare them directly.
fn shares_link(a: &Directive, b: &Directive) -> bool {
    let (Directive::Transaction(txn_a), Directive::Transaction(txn_b)) = (a, b) else {
        return false;
    };
    if txn_a.links.is_empty() || txn_b.links.is_empty() {
        return false;
    }
    let set: HashSet<&str> = txn_a.links.iter().map(Link::as_str).collect();
    txn_b.links.iter().any(|l| set.contains(l.as_str()))
}

/// Check whether two dates are within a given window (in days).
fn within_date_window(date1: NaiveDate, date2: NaiveDate, days: i64) -> bool {
    let Ok(span) = date2.since(date1) else {
        return false;
    };
    i64::from(span.get_days().abs()) <= days
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

fn classify_keywords(d: &Directive) -> KeywordHit {
    let Directive::Transaction(txn) = d else {
        return KeywordHit::default();
    };
    let mut hit = KeywordHit::default();
    let narration_lower = txn.narration.as_str().to_lowercase();
    let payee_lower = txn.payee.as_ref().map_or("", |p| p.as_str()).to_lowercase();
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
    use rustledger_core::{Amount, Posting, Transaction};

    fn make_txn(date: &str, narration: &str, amount: &str, currency: &str) -> Directive {
        make_txn_with(date, narration, amount, currency, "Assets:Bank", vec![])
    }

    fn make_txn_with(
        date: &str,
        narration: &str,
        amount: &str,
        currency: &str,
        account: &str,
        links: Vec<&str>,
    ) -> Directive {
        let mut txn = Transaction::new(date.parse::<NaiveDate>().unwrap(), narration)
            .with_synthesized_posting(Posting::new(
                account,
                Amount::new(amount.parse::<Decimal>().unwrap(), currency),
            ));
        for link in links {
            txn = txn.with_link(link);
        }
        Directive::Transaction(txn)
    }

    /// Wrap a borrowed directive with no source location (test convenience).
    fn loc(d: &Directive) -> LocatedDirective<'_> {
        LocatedDirective {
            directive: d,
            filename: None,
            lineno: None,
        }
    }

    /// Run `find_transfers` over owned directive groups, building the borrowed
    /// `LocatedDirective` view internally so tests can pass owned `Directive`s.
    fn find_in_groups(
        groups: &[(String, Vec<Directive>)],
        config: &TransferConfig,
    ) -> Vec<TransferMatch> {
        let located: Vec<(String, Vec<LocatedDirective<'_>>)> = groups
            .iter()
            .map(|(account, dirs)| (account.clone(), dirs.iter().map(loc).collect()))
            .collect();
        find_transfers(&located, config)
    }

    /// Run `find_transfers_in_ledger` over an owned flat directive list.
    fn find_in_ledger(directives: &[Directive], config: &TransferConfig) -> Vec<TransferMatch> {
        let located: Vec<LocatedDirective<'_>> = directives.iter().map(loc).collect();
        find_transfers_in_ledger(&located, config)
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
        // Checking↔Savings matches; CreditCard has no opposite-sign match
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn empty_groups() {
        let groups: Vec<(String, Vec<Directive>)> = vec![];
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_ledger(&directives, &TransferConfig::default());
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
        let matches = find_in_ledger(&directives, &TransferConfig::default());
        assert!(matches.is_empty());
    }

    #[test]
    fn transfer_match_carries_filename_and_lineno() {
        // Location lives in `LocatedDirective`, not the directive, so build them
        // explicitly here (the directives must outlive the borrowed view).
        let checking = make_txn_with(
            "2024-01-15",
            "Transfer",
            "-500.00",
            "USD",
            "Assets:Checking",
            vec![],
        );
        let savings = make_txn_with(
            "2024-01-15",
            "Transfer",
            "500.00",
            "USD",
            "Assets:Savings",
            vec![],
        );
        let groups = vec![
            (
                "Assets:Checking".to_string(),
                vec![LocatedDirective {
                    directive: &checking,
                    filename: Some("checking.bean".to_string()),
                    lineno: Some(42),
                }],
            ),
            (
                "Assets:Savings".to_string(),
                vec![LocatedDirective {
                    directive: &savings,
                    filename: Some("savings.bean".to_string()),
                    lineno: Some(18),
                }],
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
                    vec!["xfer-001"],
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
                    vec!["xfer-001"],
                )],
            ),
        ];
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
                    vec!["batch-import-A"],
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
                    vec!["batch-import-B"],
                )],
            ),
        ];
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
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
        let matches = find_in_groups(&groups, &TransferConfig::default());
        assert_eq!(matches.len(), 1);
        // 0.7 base + 0.2 strong = 0.9 (no same-date bonus)
        assert!(
            (matches[0].confidence - 0.9).abs() < 1e-9,
            "strong keyword + different dates: expect 0.9, got {}",
            matches[0].confidence
        );
    }
}
