//! Pad directive processing and transaction reconstruction.
//!
//! This module provides functionality to:
//! - Process pad directives and calculate padding amounts
//! - Generate synthetic transactions representing padding adjustments
//!
//! # Pad Processing
//!
//! A `pad` directive inserts a synthetic transaction between the `pad` date and
//! the next `balance` assertion to make the balance match. The synthetic transaction
//! transfers funds from the source account to the target account.
//!
//! ```beancount
//! 2024-01-01 pad Assets:Bank Equity:Opening-Balances
//! 2024-01-02 balance Assets:Bank 1000.00 USD
//! ```
//!
//! This generates a synthetic transaction (matching Python beancount's format):
//! ```beancount
//! 2024-01-01 P "(Padding inserted for Balance of 1000.00 USD for difference 1000.00 USD)"
//!   Assets:Bank             1000.00 USD
//!   Equity:Opening-Balances -1000.00 USD
//! ```

use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Currency, Directive, Inventory, NaiveDate, Pad, Position, Posting, Transaction,
};
use std::collections::HashMap;
use std::ops::Neg;

/// Prefix of the narration on every synthetic padding transaction
/// emitted by `create_padding_transaction` (private).
///
/// Downstream consumers (`rledger report stats`, the WASM
/// `expandPads` API) need to distinguish a synth pad-replacement
/// transaction from a user-written transaction that happens to use
/// the `P` flag (which is a valid user flag per the lexer). The
/// `Spanned::synthesized` marker is reliable when present, but is
/// stripped before some consumers see the directive. The narration
/// prefix is preserved end-to-end and matches Python beancount's
/// own format, so it doubles as a stable cross-tool marker.
pub const SYNTH_PAD_NARRATION_PREFIX: &str = "(Padding inserted for Balance of ";

/// Returns `true` iff `txn` looks like a synth pad-replacement
/// transaction (created by the booking crate's internal padding
/// transaction constructor).
///
/// Matches on flag `'P'` plus the narration prefix
/// [`SYNTH_PAD_NARRATION_PREFIX`]. The flag alone is insufficient:
/// `P` is a valid user-written transaction flag in beancount.
#[must_use]
pub fn is_synthesized_pad(txn: &Transaction) -> bool {
    txn.flag == 'P'
        && txn
            .narration
            .as_str()
            .starts_with(SYNTH_PAD_NARRATION_PREFIX)
}

/// Result of processing pad directives.
#[derive(Debug, Clone)]
pub struct PadResult {
    /// Original directives with pads removed.
    pub directives: Vec<Directive>,
    /// Synthetic padding transactions generated.
    pub padding_transactions: Vec<Transaction>,
    /// Any errors encountered during pad processing.
    pub errors: Vec<PadError>,
}

/// Error during pad processing.
#[derive(Debug, Clone)]
pub struct PadError {
    /// Date of the error.
    pub date: NaiveDate,
    /// Error message.
    pub message: String,
    /// Account involved.
    pub account: Option<rustledger_core::Account>,
}

impl PadError {
    /// Create a new pad error.
    pub fn new(date: NaiveDate, message: impl Into<String>) -> Self {
        Self {
            date,
            message: message.into(),
            account: None,
        }
    }

    /// Add account context.
    pub fn with_account(mut self, account: impl Into<rustledger_core::Account>) -> Self {
        self.account = Some(account.into());
        self
    }
}

/// Pending pad information.
#[derive(Debug, Clone)]
struct PendingPad {
    /// The pad directive.
    pad: Pad,
    /// Whether this pad has been used (has at least one balance assertion).
    used: bool,
    /// Currencies that have already been padded (each currency can only be padded once per pad).
    padded_currencies: std::collections::HashSet<Currency>,
}

/// Process pad directives and generate synthetic transactions.
///
/// This function:
/// 1. Tracks account inventories
/// 2. When a pad is encountered, stores it as pending
/// 3. When a balance assertion is encountered for an account with a pending pad,
///    generates a synthetic transaction to make the balance match
/// 4. Returns the directives with synthetic transactions inserted
///
/// # Arguments
///
/// * `directives` - The directives to process (should be sorted by date)
///
/// # Returns
///
/// A `PadResult` containing:
/// - The original directives (with pads preserved for reference)
/// - Synthetic padding transactions
/// - Any errors encountered
pub fn process_pads(directives: &[Directive]) -> PadResult {
    let num_directives = directives.len();
    let mut inventories: HashMap<rustledger_core::Account, Inventory> =
        HashMap::with_capacity(num_directives.min(16));
    let mut pending_pads: HashMap<rustledger_core::Account, PendingPad> = HashMap::with_capacity(4);
    let mut padding_transactions = Vec::with_capacity(num_directives.min(16));
    let mut errors = Vec::with_capacity(4);

    // Sort directives by date for processing. Carries the
    // original input index as a stable secondary key so two
    // directives sharing a date keep their input-order
    // relationship. `sort_by_key` itself is unstable; preserving
    // determinism via the index tiebreak matters when two pads
    // for the same account share a date — the input order
    // decides which one shadows the other in `pending_pads.insert`,
    // and that decision must not vary across rustc versions or
    // runs.
    let mut sorted: Vec<(usize, &Directive)> = directives.iter().enumerate().collect();
    sorted.sort_by(|(i_a, a), (i_b, b)| a.date().cmp(&b.date()).then(i_a.cmp(i_b)));
    let sorted: Vec<&Directive> = sorted.into_iter().map(|(_, d)| d).collect();

    for directive in sorted {
        match directive {
            Directive::Open(open) => {
                inventories.insert(open.account.clone(), Inventory::new());
            }

            Directive::Transaction(txn) => {
                // Update inventories
                for posting in &txn.postings {
                    if let Some(units) = posting.amount()
                        && let Some(inv) = inventories.get_mut(&posting.account)
                    {
                        let position = if let Some(cost_spec) = &posting.cost {
                            if let Some(cost) = cost_spec.resolve(units.number, txn.date) {
                                Position::with_cost(units.clone(), cost)
                            } else {
                                Position::simple(units.clone())
                            }
                        } else {
                            Position::simple(units.clone())
                        };
                        inv.add(position);
                    }
                }
            }

            Directive::Pad(pad) => {
                // Store pending pad (replaces any existing pad for this account)
                // Reset padded_currencies when a new pad is encountered
                pending_pads.insert(
                    pad.account.clone(),
                    PendingPad {
                        pad: pad.clone(),
                        used: false,
                        padded_currencies: std::collections::HashSet::new(),
                    },
                );
            }

            Directive::Balance(bal) => {
                // Check if there's a pending pad for this account
                // Use get_mut instead of remove - a pad can apply to multiple currencies
                if let Some(pending) = pending_pads.get_mut(&bal.account) {
                    // Only pad if this currency hasn't been padded yet for this pad directive
                    // (each currency can only be padded once per pad)
                    if pending.padded_currencies.contains(&bal.amount.currency) {
                        continue;
                    }

                    // Calculate padding amount
                    let current = inventories
                        .get(&bal.account)
                        .map_or(Decimal::ZERO, |inv| inv.units(&bal.amount.currency));

                    let difference = bal.amount.number - current;

                    if difference != Decimal::ZERO {
                        // Generate synthetic transaction
                        let pad_txn = create_padding_transaction(
                            pending.pad.date,
                            &pending.pad.account,
                            &pending.pad.source_account,
                            Amount::new(difference, &bal.amount.currency),
                            &bal.amount, // target balance for narration
                        );

                        // Apply to inventories
                        if let Some(inv) = inventories.get_mut(&pending.pad.account) {
                            inv.add(Position::simple(Amount::new(
                                difference,
                                &bal.amount.currency,
                            )));
                        }
                        if let Some(inv) = inventories.get_mut(&pending.pad.source_account) {
                            inv.add(Position::simple(Amount::new(
                                -difference,
                                &bal.amount.currency,
                            )));
                        }

                        padding_transactions.push(pad_txn);
                    }

                    // Mark the pad as used and track that this currency has been padded
                    pending.used = true;
                    pending
                        .padded_currencies
                        .insert(bal.amount.currency.clone());
                }
                // If no pending pad, nothing to do (balance will be checked normally)
            }

            _ => {}
        }
    }

    // Check for unused pads (pad without corresponding balance)
    for (account, pending) in pending_pads {
        if !pending.used {
            errors.push(
                PadError::new(
                    pending.pad.date,
                    format!(
                        "Pad directive for account {account} has no corresponding balance assertion"
                    ),
                )
                .with_account(account),
            );
        }
    }

    PadResult {
        directives: directives.to_vec(),
        padding_transactions,
        errors,
    }
}

/// Create a synthetic padding transaction.
///
/// The narration format matches Python beancount:
/// `(Padding inserted for Balance of {balance} for difference {difference})`
fn create_padding_transaction(
    date: NaiveDate,
    target_account: &str,
    source_account: &str,
    difference: Amount,
    balance: &Amount,
) -> Transaction {
    let narration = format!(
        "{prefix}{bal_num} {bal_cur} for difference {diff_num} {diff_cur})",
        prefix = SYNTH_PAD_NARRATION_PREFIX,
        bal_num = balance.number,
        bal_cur = balance.currency,
        diff_num = difference.number,
        diff_cur = difference.currency,
    );
    Transaction::new(date, &narration)
        .with_flag('P')
        .with_synthesized_posting(Posting::new(target_account, difference.clone()))
        .with_synthesized_posting(Posting::new(source_account, difference.neg()))
}

/// Expand a ledger by replacing pad directives with synthetic transactions.
///
/// This is useful for reports that need to show explicit padding transactions.
///
/// # Arguments
///
/// * `directives` - The original directives
///
/// # Returns
///
/// A new list of directives with pad directives replaced by synthetic transactions.
pub fn expand_pads(directives: &[Directive]) -> Vec<Directive> {
    let result = process_pads(directives);

    let mut expanded: Vec<Directive> = Vec::new();

    // Sort original directives by date
    let mut sorted_originals: Vec<&Directive> = directives.iter().collect();
    sorted_originals.sort_by_key(|d| d.date());

    // Track which padding transactions have already been emitted. When
    // two `pad` directives target the same account before a single
    // `balance` (issue #1300), `process_pads` correctly produces ONE
    // synthetic transaction (the later pad shadows the earlier via
    // `pending_pads.insert`), but without dedup the earlier walk pushed
    // the same `Transaction` once per matching `Pad` — double-applying
    // the adjustment. Beancount semantics dictate that only the most
    // recent effective pad applies; the earlier ones are unused (the
    // validator separately reports `E2003`). `consumed` enforces
    // one-emit-per-synth so the directive list reflects that.
    let mut consumed = vec![false; result.padding_transactions.len()];

    // Build a per-date index over `padding_transactions` so the
    // per-Pad lookup is O(#txns at this date), not O(total #txns).
    // On a ledger with many pads scattered across many dates, the
    // naive linear scan would degrade to O(#pads × #txns); the
    // index makes it O(#pads + #txns) total. The values are
    // indices into `padding_transactions` so `consumed[idx]` still
    // applies.
    let mut txns_by_date: HashMap<NaiveDate, Vec<usize>> = HashMap::new();
    for (i, txn) in result.padding_transactions.iter().enumerate() {
        txns_by_date.entry(txn.date).or_default().push(i);
    }

    for directive in sorted_originals {
        match directive {
            Directive::Pad(pad) => {
                // Emit every unconsumed padding transaction whose
                // date+target match this pad. Multi-currency case: one
                // `Pad` can produce multiple padding transactions (one
                // per currency); all match and all should be emitted
                // here. Multi-pad case: only the first iteration that
                // hits an unconsumed match consumes it; subsequent
                // shadowed pads find none and drop silently. NB: we
                // don't `break` — multi-currency requires multiple
                // emissions for a single pad.
                //
                // **Target-only match.** Synth txns have TWO
                // postings (target and source); matching on
                // either could wrongly associate a pad with another
                // pad's synth in a chain like
                // `pad A B / pad B C / balance A / balance B`.
                // `create_padding_transaction` always puts the
                // target posting at index 0.
                let Some(idxs) = txns_by_date.get(&pad.date) else {
                    continue;
                };
                for &i in idxs {
                    if consumed[i] {
                        continue;
                    }
                    let txn = &result.padding_transactions[i];
                    let Some(target_posting) = txn.postings.first() else {
                        continue;
                    };
                    if target_posting.account != pad.account {
                        continue;
                    }
                    expanded.push(Directive::Transaction(txn.clone()));
                    consumed[i] = true;
                }
                // If no unconsumed match found, this pad was shadowed
                // or never matched a balance — omit it from the
                // expansion. The user-facing "unused pad" warning
                // (E2003) is emitted by the validator independently.
            }
            other => {
                expanded.push(other.clone());
            }
        }
    }

    expanded
}

/// Merge original directives with padding transactions, maintaining date order.
///
/// Unlike `expand_pads`, this keeps the original pad directives and adds
/// the synthetic transactions alongside them.
pub fn merge_with_padding(directives: &[Directive]) -> Vec<Directive> {
    let result = process_pads(directives);

    let mut merged: Vec<Directive> = directives.to_vec();

    // Add padding transactions
    for txn in result.padding_transactions {
        merged.push(Directive::Transaction(txn));
    }

    // Sort by date
    merged.sort_by_key(rustledger_core::Directive::date);

    merged
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{Balance, Open};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_process_pads_basic() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);

        let txn = &result.padding_transactions[0];
        assert_eq!(txn.date, date(2024, 1, 1));
        assert_eq!(txn.postings.len(), 2);

        // Check target posting
        assert_eq!(txn.postings[0].account, "Assets:Bank");
        assert_eq!(
            txn.postings[0].amount(),
            Some(&Amount::new(dec!(1000.00), "USD"))
        );

        // Check source posting
        assert_eq!(txn.postings[1].account, "Equity:Opening");
        assert_eq!(
            txn.postings[1].amount(),
            Some(&Amount::new(dec!(-1000.00), "USD"))
        );
    }

    #[test]
    fn test_process_pads_with_existing_balance() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(500.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-500.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);

        let txn = &result.padding_transactions[0];
        // Should pad 500.00 (1000 target - 500 existing)
        assert_eq!(
            txn.postings[0].amount(),
            Some(&Amount::new(dec!(500.00), "USD"))
        );
    }

    #[test]
    fn test_process_pads_negative_adjustment() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Big deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(2000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-2000.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);

        let txn = &result.padding_transactions[0];
        // Should pad -1000.00 (1000 target - 2000 existing)
        assert_eq!(
            txn.postings[0].amount(),
            Some(&Amount::new(dec!(-1000.00), "USD"))
        );
    }

    #[test]
    fn test_process_pads_no_difference() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Exact deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-1000.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        assert!(result.errors.is_empty());
        // No padding transaction needed when balance already matches
        assert!(result.padding_transactions.is_empty());
    }

    #[test]
    fn test_process_pads_unused_pad() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            // Pad without balance assertion
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
        ];

        let result = process_pads(&directives);

        assert_eq!(result.errors.len(), 1);
        assert!(
            result.errors[0]
                .message
                .contains("no corresponding balance")
        );
    }

    #[test]
    fn test_expand_pads() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let expanded = expand_pads(&directives);

        // Should have: 2 opens + 1 synthetic transaction + 1 balance = 4
        assert_eq!(expanded.len(), 4);

        // The pad should be replaced with a transaction
        let has_pad = expanded.iter().any(|d| matches!(d, Directive::Pad(_)));
        assert!(!has_pad, "Pad should be replaced");

        // Should have the synthetic transaction
        let txn_count = expanded
            .iter()
            .filter(|d| matches!(d, Directive::Transaction(_)))
            .count();
        assert_eq!(txn_count, 1);
    }

    /// Regression test for #1300. Two pad directives target the same
    /// account before a single balance assertion. `process_pads`
    /// correctly produces ONE synthetic padding transaction (the
    /// later pad shadows the earlier via the validator-mirrored
    /// "most recent effective pad wins" rule), but before this fix
    /// `expand_pads` emitted the SAME transaction once per matching
    /// `Pad` — double-applying the adjustment.
    ///
    /// Concrete failure under the bug: starting balance 1000 USD,
    /// expected after expansion = 1000 + (-100) = 900 USD. Actual
    /// before fix = 1000 + (-100) + (-100) = 800 USD because the
    /// single synth transaction got pushed twice.
    #[test]
    fn test_expand_pads_does_not_double_apply_multi_pad() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 1), "opening").with_synthesized_posting(
                    Posting::new("Assets:Bank", Amount::new(dec!(1000.00), "USD")),
                ),
            ),
            // Two pads, same date, same target. Per beancount
            // semantics the later one is "active" and the earlier
            // one is "unused" (validator reports E2003).
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 3),
                "Assets:Bank",
                Amount::new(dec!(900.00), "USD"),
            )),
        ];

        let expanded = expand_pads(&directives);

        // Exactly ONE synthetic padding transaction must be present
        // (not two). The 2 Pad directives must both be dropped from
        // the output (one consumed the synth, one shadowed).
        let synth_count = expanded
            .iter()
            .filter(|d| matches!(d, Directive::Transaction(t) if t.flag == 'P'))
            .count();
        assert_eq!(
            synth_count, 1,
            "expected exactly one synthetic padding transaction; \
             got {synth_count} (pre-#1300-fix bug emitted both pads' synths)",
        );

        let has_pad = expanded.iter().any(|d| matches!(d, Directive::Pad(_)));
        assert!(!has_pad, "both pads should be removed from expansion");
    }

    #[test]
    fn test_merge_with_padding() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives);

        // Should have: 2 opens + 1 pad + 1 balance + 1 synthetic = 5
        assert_eq!(merged.len(), 5);

        // Pad should still be there
        let has_pad = merged.iter().any(|d| matches!(d, Directive::Pad(_)));
        assert!(has_pad, "Pad should be preserved");

        // Should also have the synthetic transaction
        let txn_count = merged
            .iter()
            .filter(|d| matches!(d, Directive::Transaction(_)))
            .count();
        assert_eq!(txn_count, 1);
    }

    /// Pins the invariant that `expand_pads` relies on for the
    /// target-only pad↔synth match: the TARGET posting is at index
    /// 0 of `postings`, the source posting is at index 1. If
    /// `create_padding_transaction` ever swaps these (or someone
    /// reorders postings downstream), `expand_pads` would silently
    /// misassociate pads with synth transactions in chain cases
    /// like `pad A B / pad B C / balance A / balance B`.
    #[test]
    fn test_create_padding_transaction_target_posting_at_index_0() {
        let txn = create_padding_transaction(
            date(2024, 1, 1),
            "Assets:Target",
            "Equity:Source",
            Amount::new(dec!(100), "USD"),
            &Amount::new(dec!(100), "USD"),
        );
        assert_eq!(txn.postings.len(), 2);
        assert_eq!(
            txn.postings[0].account, "Assets:Target",
            "target posting must be at index 0",
        );
        assert_eq!(
            txn.postings[1].account, "Equity:Source",
            "source posting must be at index 1",
        );
    }

    #[test]
    fn test_is_synthesized_pad_recognizes_synth_txn() {
        let synth = create_padding_transaction(
            date(2024, 1, 1),
            "Assets:Bank",
            "Equity:Opening",
            Amount::new(dec!(100), "USD"),
            &Amount::new(dec!(100), "USD"),
        );
        assert!(is_synthesized_pad(&synth));
    }

    #[test]
    fn test_is_synthesized_pad_rejects_user_p_flag_txn() {
        // `P` is a valid user-written transaction flag in beancount.
        // A user-written `P`-flagged transaction with arbitrary
        // narration must NOT be classified as a synth pad.
        let user_txn = Transaction::new(date(2024, 1, 1), "rent")
            .with_flag('P')
            .with_synthesized_posting(Posting::new("Expenses:Rent", Amount::new(dec!(500), "USD")));
        assert!(!is_synthesized_pad(&user_txn));
    }

    #[test]
    fn test_is_synthesized_pad_rejects_non_p_flag() {
        let txt = Transaction::new(date(2024, 1, 1), "(Padding inserted for Balance of dummy)")
            .with_flag('*');
        assert!(!is_synthesized_pad(&txt));
    }

    #[test]
    fn test_padding_transaction_has_p_flag() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        assert_eq!(result.padding_transactions.len(), 1);
        assert_eq!(result.padding_transactions[0].flag, 'P');
    }

    #[test]
    fn test_process_pads_multiple_currencies() {
        // From basic.beancount:
        // 2007-12-30 pad  Assets:Cash  Equity:Opening-Balances
        // 2007-12-31 balance  Assets:Cash  200 CAD
        // 2007-12-31 balance  Assets:Cash  300 USD
        //
        // A single pad should generate padding for BOTH currencies
        let directives = vec![
            Directive::Open(Open::new(date(2007, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2007, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(
                date(2007, 12, 30),
                "Assets:Cash",
                "Equity:Opening",
            )),
            Directive::Balance(Balance::new(
                date(2007, 12, 31),
                "Assets:Cash",
                Amount::new(dec!(200), "CAD"),
            )),
            Directive::Balance(Balance::new(
                date(2007, 12, 31),
                "Assets:Cash",
                Amount::new(dec!(300), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        assert!(result.errors.is_empty(), "Should have no errors");
        assert_eq!(
            result.padding_transactions.len(),
            2,
            "Should generate TWO padding transactions (one per currency)"
        );

        // Check that we have both currencies padded
        let currencies: Vec<_> = result
            .padding_transactions
            .iter()
            .filter_map(|txn| txn.postings.first())
            .filter_map(|p| p.amount())
            .map(|a| a.currency.as_str())
            .collect();

        assert!(currencies.contains(&"CAD"), "Should pad CAD");
        assert!(currencies.contains(&"USD"), "Should pad USD");
    }

    #[test]
    fn test_process_pads_transaction_after_balance_ends_pad() {
        // Once a transaction affects the account after the balance assertions,
        // the pad should no longer apply to later balance assertions
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
            // Transaction after balance - this "consumes" the pad
            Directive::Transaction(
                Transaction::new(date(2024, 1, 3), "Spending")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(100), "USD"),
                    )),
            ),
            // This balance should NOT use the pad (too late)
            Directive::Balance(Balance::new(
                date(2024, 1, 5),
                "Assets:Bank",
                Amount::new(dec!(900), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        // Should only generate one padding transaction (for the first balance)
        assert_eq!(result.padding_transactions.len(), 1);
        assert_eq!(
            result.padding_transactions[0]
                .postings
                .first()
                .and_then(|p| p.amount())
                .map(|a| a.number),
            Some(dec!(1000))
        );
    }
}
