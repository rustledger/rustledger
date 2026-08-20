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
    Amount, Currency, Directive, Inventory, NaiveDate, Pad, Position, Posting, Spanned, Transaction,
};
use std::collections::HashMap;
use std::ops::Neg;

/// Prefix of the narration carried by every synth pad transaction
/// produced by this crate (the format string used inside the
/// private `create_padding_transaction` constructor).
///
/// Together with [`is_synthesized_pad`], lets consumers distinguish
/// pad-synth transactions from user-written `P`-flag transactions
/// (`P` is a valid user flag in beancount). The narration prefix
/// matches Python beancount's format and is preserved end-to-end
/// through the booking and merge steps.
pub const SYNTH_PAD_NARRATION_PREFIX: &str = "(Padding inserted for Balance of ";

/// Returns `true` iff `txn` is a pad-synth transaction produced by
/// this crate.
///
/// Checks the `P` flag AND the [`SYNTH_PAD_NARRATION_PREFIX`].
/// A bare flag check would conflate user-written `P`-flag
/// transactions with synth pads.
#[must_use]
pub fn is_synthesized_pad(txn: &Transaction) -> bool {
    txn.flag == 'P'
        && txn
            .narration
            .as_str()
            .starts_with(SYNTH_PAD_NARRATION_PREFIX)
}

/// Result of processing pad directives.
///
/// This holds only what `process_pads` *derives* from the input: the
/// synthesized padding transactions and any errors. It deliberately
/// does NOT echo the input directives back — the caller already owns
/// that slice, so cloning it into the result was pure waste on every
/// call (a full deep-clone of the directive stream the caller then
/// discarded). Callers that want the source merged with the synth
/// transactions for balance math should use [`merge_with_padding`].
#[derive(Debug, Clone)]
pub struct PadResult {
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
///
/// # Arguments
///
/// * `directives` - The directives to process. Order does not matter:
///   `process_pads` sorts a view of them by date internally before
///   applying pad math.
///
/// # Returns
///
/// A `PadResult` containing:
/// - The synthetic padding transactions derived from the input
/// - Any errors encountered
///
/// The input directives are NOT echoed back in the result; the caller
/// already owns them. To get the source merged with the synth
/// transactions, use [`merge_with_padding`].
pub fn process_pads(directives: &[Directive]) -> PadResult {
    let num_directives = directives.len();
    let mut inventories: HashMap<rustledger_core::Account, Inventory> =
        HashMap::with_capacity(num_directives.min(16));
    let mut pending_pads: HashMap<rustledger_core::Account, PendingPad> = HashMap::with_capacity(4);
    let mut padding_transactions = Vec::with_capacity(num_directives.min(16));
    let mut errors = Vec::with_capacity(4);

    // Sort directives by date for processing
    let mut sorted: Vec<&Directive> = directives.iter().collect();
    sorted.sort_by_key(|d| d.date());

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
                        let position =
                            Position::from_posting(units, posting.cost.as_deref(), txn.date);
                        // A running balance that leaves range makes every pad
                        // measured against it wrong, so report it here rather
                        // than pad from a clamped total (#1863).
                        if let Err(e) = inv.add(position) {
                            errors.push(
                                PadError::new(txn.date, e.to_string())
                                    .with_account(posting.account.clone()),
                            );
                        }
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

                    // Calculate padding amount. The balance assertion this pad
                    // targets sums the account AND its sub-accounts (beancount
                    // semantic, verified against bean-check), so the pad
                    // difference must be measured the same way — using only the
                    // leaf account here under-/over-padded a non-leaf target and
                    // then tripped the (sub-account-summing) Late validator.
                    let current = rustledger_core::sum_account_and_subaccounts(
                        inventories.iter(),
                        bal.account.as_str(),
                        &bal.amount.currency,
                    );

                    // A pad amount that cannot be represented must not be
                    // clamped — the synthetic transaction it produces is
                    // written into the ledger as if the user had entered it
                    // (#1863).
                    let Some(difference) = current.and_then(|c| bal.amount.number.checked_sub(c))
                    else {
                        errors.push(PadError::new(
                            bal.date,
                            format!(
                                "cannot compute the pad amount for {}: the {} balance exceeds \
                                 the representable range (±7.9e28)",
                                bal.account, bal.amount.currency
                            ),
                        ));
                        continue;
                    };

                    if difference != Decimal::ZERO {
                        // Generate synthetic transaction
                        let pad_txn = create_padding_transaction(
                            pending.pad.date,
                            &pending.pad.account,
                            &pending.pad.source_account,
                            Amount::new(difference, &bal.amount.currency),
                            &bal.amount, // target balance for narration
                        );

                        // Apply to inventories. `difference` was just derived
                        // from these same balances, so an overflow here means
                        // the pad target itself is out of range — report it
                        // rather than pad to a clamped figure.
                        //
                        // A pad is two halves of one entry, so it applies as a
                        // unit: if the source overflows after the target
                        // succeeded, the target is UNDONE. Leaving it applied
                        // would credit the target without debiting the source
                        // while emitting no synthetic transaction, so the
                        // inventories and the directive list would disagree —
                        // and a later assertion on the target could pass off a
                        // pad that never happened. The undo is always
                        // representable: it restores a total that existed a
                        // moment ago.
                        let currency = &bal.amount.currency;
                        let mut apply = |account, number| {
                            inventories
                                .get_mut(account)
                                .map(|inv| inv.add(Position::simple(Amount::new(number, currency))))
                                .transpose()
                        };
                        if let Err(e) = apply(&pending.pad.account, difference) {
                            errors.push(PadError::new(bal.date, e.to_string()));
                            continue;
                        }
                        if let Err(e) = apply(&pending.pad.source_account, -difference) {
                            drop(apply(&pending.pad.account, -difference));
                            errors.push(PadError::new(bal.date, e.to_string()));
                            continue;
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

/// Merge original directives with padding transactions, maintaining date order.
///
/// Keeps the original pad directives and adds the synthesized
/// transactions alongside them. Use this when downstream
/// consumers want both views: `Pad` directives for source-faithful queries
/// (e.g., BQL `WHERE type = 'pad'`) and the synth transactions for inventory
/// math.
///
/// # Sort ordering on date ties
///
/// Synth transactions carry the pad's date, not the balance's date.
/// On a same-date pad+balance pair (legal in beancount), the synth must
/// appear BEFORE the balance so any consumer that checks balance assertions
/// mid-stream sees the correct inventory. This is achieved by prepending
/// the synth list to the original directives before the stable sort:
/// synths land at the front of their date-group, originals follow.
///
/// # Errors are discarded
///
/// [`process_pads`] can emit `PadError`s (e.g., unused-pad warnings).
/// `merge_with_padding` discards them by design: those diagnostics are the
/// validator's responsibility (`E2003`). If you need them, call
/// [`process_pads`] directly and inspect `result.errors`.
///
/// # Not idempotent
///
/// Re-running `merge_with_padding` on its own output double-counts pad
/// effects because the original `Pad` directives survive and `process_pads`
/// re-applies them against an inventory that already includes the prior
/// synth. A `debug_assert!` guards against this in dev builds.
pub fn merge_with_padding(directives: &[Directive]) -> Vec<Directive> {
    merge_with_padding_owned(directives.to_vec())
}

/// [`merge_with_padding`] for a caller that already owns its directives.
///
/// Exists so consumers holding an owned `Vec` need not clone it a second time
/// just to reach the canonical placement rule. `Ledger::balance_view` used to
/// inline the merge for exactly that reason, and the copy drifted the moment
/// the rule changed — this is the same saving without the duplicate.
#[must_use]
pub fn merge_with_padding_owned(directives: Vec<Directive>) -> Vec<Directive> {
    // Idempotence: input that already contains synth pad transactions has
    // been merged before (e.g. an embedder queries entries it loaded via
    // load-full, which merges pads — rustledger#1712). Re-running would
    // double-count pad effects, so return the input unchanged instead.
    if directives
        .iter()
        .any(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t)))
    {
        return directives;
    }

    let result = process_pads(&directives);

    let mut merged: Vec<Directive> = directives;
    merged.sort_by_key(rustledger_core::Directive::date);

    for txn in result.padding_transactions {
        let insert_at = pad_insertion_index(merged.iter(), txn.date);
        merged.insert(insert_at, Directive::Transaction(txn));
    }

    merged
}

/// Where a synthesized padding transaction dated `date` belongs in an
/// already date-sorted directive stream.
///
/// The rule: immediately BEFORE the first `Balance` sharing its date, and
/// otherwise at the END of its date group.
///
/// The "before a same-date Balance" half is load-bearing: a `pad` and the
/// `balance` it satisfies can share a date, and any consumer checking
/// assertions mid-stream must see the padding first.
///
/// The "otherwise at the end" half is what stops the synth displacing
/// UNRELATED same-date directives. Prepending it to the whole date group did
/// that: on `ledger2beancount/tests_balance-assertion.beancount` a 2019-01-29
/// pad for `Assets:Test6` jumped ahead of an unrelated 2019-01-29 transaction
/// for `Assets:Test5`, and every running balance from that row on was
/// 500.00 USD out relative to bean-query, which orders the padding at the
/// `pad` directive's own position.
///
/// This is the single source of truth for pad placement. It is `pub` because
/// the rule has three consumers with three different element types —
/// [`merge_with_padding_owned`] over `Directive`,
/// [`merge_with_padding_spanned`] over [`Spanned<Directive>`], and
/// `rustledger-ffi-wasi`'s `expand_pads` over `(Directive, tag)` pairs, which
/// carries parallel provenance tags and so cannot call either merge. All three
/// once open-coded the rule; two of the copies were still prepending when this
/// one changed. Compute the index here rather than re-deriving it.
///
/// Cost: one insert per synth into an already-sorted vector, so O(n x k) for
/// k pads rather than a single O(n log n) pass. `pad` is used sparingly by
/// construction — one per account per period — and callers early-return on a
/// ledger with none; the heaviest file in the compat corpus carries 12. If a
/// ledger ever arrives with pads in the thousands, merge the (date-sorted)
/// synths in one pass instead.
#[must_use]
pub fn pad_insertion_index<'a, I>(sorted: I, date: NaiveDate) -> usize
where
    I: IntoIterator<Item = &'a Directive>,
{
    let mut end_of_group = 0;
    for (index, directive) in sorted.into_iter().enumerate() {
        if directive.date() == date && matches!(directive, Directive::Balance(_)) {
            return index;
        }
        if directive.date() <= date {
            end_of_group = index + 1;
        }
    }
    end_of_group
}

/// Span-preserving variant of [`merge_with_padding`].
///
/// Identical merge behavior, but the input/output keep each directive's
/// [`Spanned`] wrapper so downstream consumers (e.g. BQL's `filename`/`lineno`
/// columns) can resolve real source locations. Pad-synthesized transactions
/// have no source representation, so they are wrapped with
/// [`Spanned::synthesized`] ([`Span::ZERO`](rustledger_core::Span) +
/// [`SYNTHESIZED_FILE_ID`](rustledger_core::SYNTHESIZED_FILE_ID)) — exactly how
/// other synthesized directives (plugin output, etc.) are marked.
///
/// # Not idempotent
///
/// Same caveat as [`merge_with_padding`]: re-running on its own output
/// double-counts pad effects.
#[must_use]
pub fn merge_with_padding_spanned(directives: &[Spanned<Directive>]) -> Vec<Spanned<Directive>> {
    let plain: Vec<Directive> = directives.iter().map(|s| s.value.clone()).collect();
    debug_assert!(
        !plain
            .iter()
            .any(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t))),
        "merge_with_padding_spanned called on input that already contains synth pad transactions; \
         re-running would double-count pad effects",
    );

    let result = process_pads(&plain);

    // Placement via the shared [`pad_insertion_index`]. Marked synthesized so
    // they resolve to no source location.
    let mut merged: Vec<Spanned<Directive>> = directives.to_vec();
    merged.sort_by_key(|s| s.value.date());

    for txn in result.padding_transactions {
        let insert_at = pad_insertion_index(merged.iter().map(|s| &s.value), txn.date);
        merged.insert(insert_at, Spanned::synthesized(Directive::Transaction(txn)));
    }

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
    fn test_process_pads_sums_subaccounts_for_nonleaf_target() {
        // A pad targeting a NON-LEAF account must measure the current balance the
        // same way the balance assertion does — summing the account AND its
        // sub-accounts (beancount semantic, verified against bean-check). Here the
        // balance lives entirely in the sub-account `Assets:Bank:Checking`, so the
        // pad to `Assets:Bank` must be 100 - 50 = 50, NOT 100 (the old leaf-only
        // bug, which then tripped the sub-account-summing Late validator).
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Checking")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Deposit into sub-account")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank:Checking",
                        Amount::new(dec!(50.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-50.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(100.00), "USD"),
            )),
        ];

        let result = process_pads(&directives);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);
        // 100 target - 50 already held in the sub-account = 50.
        assert_eq!(
            result.padding_transactions[0].postings[0].amount(),
            Some(&Amount::new(dec!(50.00), "USD")),
            "pad on a non-leaf account must sum sub-accounts (was leaf-only)"
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

    #[test]
    fn test_is_synthesized_pad_recognizes_synth() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];
        let result = process_pads(&directives);
        let synth = result.padding_transactions.into_iter().next().unwrap();
        assert!(
            is_synthesized_pad(&synth),
            "synth pad transaction must be detected by is_synthesized_pad",
        );
    }

    #[test]
    fn test_is_synthesized_pad_rejects_user_p_flag() {
        // A user-written `P`-flag transaction with arbitrary narration
        // must NOT be classified as a synth pad. `P` is a valid user
        // flag in beancount; bare flag-checking would conflate them.
        let user_p = Transaction::new(date(2024, 1, 1), "user-authored P-flag txn")
            .with_flag('P')
            .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")));
        assert!(
            !is_synthesized_pad(&user_p),
            "user-written P-flag transaction must not be classified as synth",
        );
    }

    #[test]
    fn test_merge_with_padding_synth_does_not_displace_unrelated_same_date_entry() {
        // A pad whose balance lands on a LATER date must not jump ahead of an
        // unrelated transaction sharing the pad's date. Prepending synths to
        // the whole date group did exactly that, and every running balance
        // from that row on was off by the padding amount.
        //
        // This is the other half of the placement rule from
        // `test_merge_with_padding_same_date_pad_balance_synth_comes_first`:
        // with no same-date Balance to sit in front of, the synth belongs at
        // the END of its date group, which is where bean-query puts it.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Other")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            // Unrelated transaction, same date as the pad below.
            Directive::Transaction(
                Transaction::new(date(2024, 1, 2), "unrelated")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Other",
                        Amount::new(dec!(10), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            // Balance is on a LATER date, so there is no same-date Balance.
            Directive::Balance(Balance::new(
                date(2024, 1, 3),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives);

        let synth_idx = merged
            .iter()
            .position(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t)))
            .expect("synth present");
        let unrelated_idx = merged
            .iter()
            .position(
                |d| matches!(d, Directive::Transaction(t) if t.narration.as_ref() == "unrelated"),
            )
            .expect("unrelated txn present");
        assert!(
            unrelated_idx < synth_idx,
            "unrelated same-date txn (idx {unrelated_idx}) must precede the synth (idx {synth_idx})",
        );
    }

    #[test]
    fn test_merge_with_padding_same_date_pad_balance_synth_comes_first() {
        // Pad and balance share the same date. The synth (which carries
        // the pad's date) must appear BEFORE the Balance in the merged
        // view so any mid-stream balance-assertion check sees the
        // correct inventory.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives);

        // Find indices of the synth and the Balance.
        let synth_idx = merged
            .iter()
            .position(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t)))
            .expect("synth present");
        let balance_idx = merged
            .iter()
            .position(|d| matches!(d, Directive::Balance(_)))
            .expect("balance present");
        assert!(
            synth_idx < balance_idx,
            "synth pad (idx {synth_idx}) must appear before Balance (idx {balance_idx}) on same date",
        );
    }

    #[test]
    fn test_merge_with_padding_is_idempotent() {
        // Re-merging already-merged input must be a no-op, not a
        // double-count (and not an abort): embedders legitimately feed
        // load-full output — which is already merged — back into
        // query/window ops (rustledger#1712).
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];
        let merged_once = merge_with_padding(&directives);
        let merged_twice = merge_with_padding(&merged_once);
        assert_eq!(merged_once.len(), merged_twice.len());
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
