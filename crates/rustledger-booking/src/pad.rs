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
//! This generates a synthetic transaction:
//! ```beancount
//! 2024-01-01 P "(Padding inserted for balance assertion)"
//!   Assets:Bank             1000.00 USD
//!   Equity:Opening-Balances -1000.00 USD
//! ```

use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Directive, InternedStr, Inventory, NaiveDate, Pad, Position, Posting, Transaction,
};
use std::collections::HashMap;
use std::ops::Neg;

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
    pub account: Option<InternedStr>,
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
    pub fn with_account(mut self, account: impl Into<InternedStr>) -> Self {
        self.account = Some(account.into());
        self
    }
}

/// Pending pad information.
#[derive(Debug, Clone)]
struct PendingPad {
    /// The pad directive.
    pad: Pad,
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
    let mut inventories: HashMap<InternedStr, Inventory> = HashMap::new();
    let mut pending_pads: HashMap<InternedStr, PendingPad> = HashMap::new();
    let mut padding_transactions = Vec::new();
    let mut errors = Vec::new();

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
                    if let Some(units) = posting.amount() {
                        if let Some(inv) = inventories.get_mut(&posting.account) {
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
            }

            Directive::Pad(pad) => {
                // Store pending pad
                pending_pads.insert(pad.account.clone(), PendingPad { pad: pad.clone() });
            }

            Directive::Balance(bal) => {
                // Check if there's a pending pad for this account
                if let Some(pending) = pending_pads.remove(&bal.account) {
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
                } else {
                    // No padding - just update inventory from existing transactions
                    // (already done in transaction processing)
                }
            }

            _ => {}
        }
    }

    // Check for unused pads (pad without corresponding balance)
    for (account, pending) in pending_pads {
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

    PadResult {
        directives: directives.to_vec(),
        padding_transactions,
        errors,
    }
}

/// Create a synthetic padding transaction.
fn create_padding_transaction(
    date: NaiveDate,
    target_account: &str,
    source_account: &str,
    amount: Amount,
) -> Transaction {
    Transaction::new(date, "(Padding inserted for balance assertion)")
        .with_flag('P')
        .with_posting(Posting::new(target_account, amount.clone()))
        .with_posting(Posting::new(source_account, amount.neg()))
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

    // Create a map of pad dates to padding transactions
    let mut pad_txns_by_date: HashMap<NaiveDate, Vec<&Transaction>> = HashMap::new();
    for txn in &result.padding_transactions {
        pad_txns_by_date.entry(txn.date).or_default().push(txn);
    }

    // Track which pad transactions we've inserted
    let mut inserted_pads: HashMap<NaiveDate, usize> = HashMap::new();

    for directive in sorted_originals {
        match directive {
            Directive::Pad(pad) => {
                // Replace pad with synthetic transaction if one was generated
                if let Some(txns) = pad_txns_by_date.get(&pad.date) {
                    let idx = inserted_pads.entry(pad.date).or_insert(0);
                    if *idx < txns.len() {
                        // Find the matching transaction for this pad
                        for txn in txns {
                            if txn.postings.iter().any(|p| p.account == pad.account) {
                                expanded.push(Directive::Transaction((*txn).clone()));
                                break;
                            }
                        }
                        *idx += 1;
                    }
                }
                // If no transaction was generated (difference was zero), omit the pad
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
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(500.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(2000.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
        assert!(result.errors[0]
            .message
            .contains("no corresponding balance"));
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
}
