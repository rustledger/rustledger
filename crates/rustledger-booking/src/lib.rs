//! Beancount booking engine with interpolation.
//!
//! This crate provides:
//! - Transaction interpolation (filling in missing amounts)
//! - Transaction balancing verification
//! - Tolerance calculation
//!
//! # Interpolation
//!
//! When a transaction has exactly one posting per currency without an amount,
//! that amount can be calculated to make the transaction balance.
//!
//! ```ignore
//! use rustledger_booking::interpolate;
//!
//! // Transaction with one missing amount
//! // 2024-01-15 * "Groceries"
//! //   Expenses:Food  50.00 USD
//! //   Assets:Cash               <- amount inferred as -50.00 USD
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod interpolate;
mod pad;

pub use interpolate::{interpolate, InterpolationError, InterpolationResult};
pub use pad::{expand_pads, merge_with_padding, process_pads, PadError, PadResult};

use rust_decimal::prelude::Signed;
use rust_decimal::Decimal;
use rustledger_core::{Amount, IncompleteAmount, Transaction};
use std::collections::HashMap;

/// Calculate the tolerance for a set of amounts.
///
/// Tolerance is the maximum of all individual amount tolerances.
#[must_use]
pub fn calculate_tolerance(amounts: &[&Amount]) -> HashMap<String, Decimal> {
    let mut tolerances: HashMap<String, Decimal> = HashMap::new();

    for amount in amounts {
        let tol = amount.inferred_tolerance();
        tolerances
            .entry(amount.currency.clone())
            .and_modify(|t| *t = (*t).max(tol))
            .or_insert(tol);
    }

    tolerances
}

/// Calculate the residual (imbalance) of a transaction.
///
/// Returns a map of currency -> residual amount.
/// A balanced transaction has all residuals within tolerance.
#[must_use]
pub fn calculate_residual(transaction: &Transaction) -> HashMap<String, Decimal> {
    let mut residuals: HashMap<String, Decimal> = HashMap::new();

    for posting in &transaction.postings {
        // Only process complete amounts
        if let Some(IncompleteAmount::Complete(units)) = &posting.units {
            // Determine the "weight" of this posting for balance purposes.
            // - If there's a cost, the weight is in the cost currency (not units currency)
            // - If there's a price annotation, the weight is in the price currency (not units currency)
            // - Otherwise, the weight is just the units

            if let Some(cost_spec) = &posting.cost {
                // Cost-based posting: weight is in the cost currency
                if let (Some(per_unit), Some(cost_curr)) =
                    (&cost_spec.number_per, &cost_spec.currency)
                {
                    let cost_amount = units.number * per_unit;
                    *residuals.entry(cost_curr.clone()).or_default() += cost_amount;
                } else if let (Some(total), Some(cost_curr)) =
                    (&cost_spec.number_total, &cost_spec.currency)
                {
                    // For total cost, the sign depends on the units sign
                    *residuals.entry(cost_curr.clone()).or_default() +=
                        *total * units.number.signum();
                } else {
                    // Cost spec without amount/currency - fall back to units
                    *residuals.entry(units.currency.clone()).or_default() += units.number;
                }
            } else if let Some(price) = &posting.price {
                // Price annotation: converts units to price currency for balance purposes.
                // The weight is in the price currency, not the units currency.
                match price {
                    rustledger_core::PriceAnnotation::Unit(price_amt) => {
                        let converted = units.number.abs() * price_amt.number;
                        *residuals.entry(price_amt.currency.clone()).or_default() +=
                            converted * units.number.signum();
                    }
                    rustledger_core::PriceAnnotation::Total(price_amt) => {
                        *residuals.entry(price_amt.currency.clone()).or_default() +=
                            price_amt.number * units.number.signum();
                    }
                    // Incomplete price annotations - extract what we can
                    rustledger_core::PriceAnnotation::UnitIncomplete(inc) => {
                        if let Some(price_amt) = inc.as_amount() {
                            let converted = units.number.abs() * price_amt.number;
                            *residuals.entry(price_amt.currency.clone()).or_default() +=
                                converted * units.number.signum();
                        } else {
                            // Can't calculate price conversion, fall back to units
                            *residuals.entry(units.currency.clone()).or_default() += units.number;
                        }
                    }
                    rustledger_core::PriceAnnotation::TotalIncomplete(inc) => {
                        if let Some(price_amt) = inc.as_amount() {
                            *residuals.entry(price_amt.currency.clone()).or_default() +=
                                price_amt.number * units.number.signum();
                        } else {
                            // Can't calculate price conversion, fall back to units
                            *residuals.entry(units.currency.clone()).or_default() += units.number;
                        }
                    }
                    // Empty price annotations - fall back to units
                    rustledger_core::PriceAnnotation::UnitEmpty
                    | rustledger_core::PriceAnnotation::TotalEmpty => {
                        *residuals.entry(units.currency.clone()).or_default() += units.number;
                    }
                }
            } else {
                // Simple posting: weight is just the units
                *residuals.entry(units.currency.clone()).or_default() += units.number;
            }
        }
    }

    residuals
}

/// Check if a transaction is balanced within tolerance.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn is_balanced(transaction: &Transaction, tolerances: &HashMap<String, Decimal>) -> bool {
    let residuals = calculate_residual(transaction);

    for (currency, residual) in residuals {
        let tolerance = tolerances
            .get(&currency)
            .copied()
            .unwrap_or(Decimal::new(5, 3)); // Default 0.005

        if residual.abs() > tolerance {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{NaiveDate, Posting};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
    }

    #[test]
    fn test_calculate_residual_balanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    #[test]
    fn test_calculate_residual_unbalanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-45.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(5.00)));
    }

    #[test]
    fn test_is_balanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let tolerances = calculate_tolerance(&[
            &Amount::new(dec!(50.00), "USD"),
            &Amount::new(dec!(-50.00), "USD"),
        ]);

        assert!(is_balanced(&txn, &tolerances));
    }

    #[test]
    fn test_is_balanced_within_tolerance() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.004), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let tolerances = calculate_tolerance(&[
            &Amount::new(dec!(50.004), "USD"),
            &Amount::new(dec!(-50.00), "USD"),
        ]);

        // 0.004 is within tolerance of 0.005 (scale 2 -> 0.005)
        assert!(is_balanced(&txn, &tolerances));
    }

    #[test]
    fn test_calculate_tolerance() {
        let amounts = [
            Amount::new(dec!(100), "USD"),    // scale 0 -> tol 0.5
            Amount::new(dec!(50.00), "USD"),  // scale 2 -> tol 0.005
            Amount::new(dec!(25.000), "EUR"), // scale 3 -> tol 0.0005
        ];

        let refs: Vec<&Amount> = amounts.iter().collect();
        let tolerances = calculate_tolerance(&refs);

        // USD should use the max tolerance (0.5 from scale 0)
        assert_eq!(tolerances.get("USD"), Some(&dec!(0.5)));
        assert_eq!(tolerances.get("EUR"), Some(&dec!(0.0005)));
    }
}
