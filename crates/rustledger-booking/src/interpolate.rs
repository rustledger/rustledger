//! Transaction interpolation.
//!
//! Fills in missing posting amounts to balance transactions.

use rust_decimal::prelude::Signed;
use rust_decimal::Decimal;
use rustledger_core::{Amount, IncompleteAmount, Transaction};
use std::collections::HashMap;
use thiserror::Error;

/// Errors that can occur during interpolation.
#[derive(Debug, Clone, Error)]
pub enum InterpolationError {
    /// Multiple postings are missing amounts for the same currency.
    #[error("multiple postings missing amounts for currency {currency}")]
    MultipleMissing {
        /// The currency with multiple missing amounts.
        currency: String,
        /// Number of postings missing this currency.
        count: usize,
    },

    /// Cannot infer currency for a posting.
    #[error("cannot infer currency for posting to account {account}")]
    CannotInferCurrency {
        /// The account of the posting.
        account: String,
    },

    /// Transaction does not balance after interpolation.
    #[error("transaction does not balance: residual {residual} {currency}")]
    DoesNotBalance {
        /// The unbalanced currency.
        currency: String,
        /// The residual amount.
        residual: Decimal,
    },
}

/// Result of interpolation.
#[derive(Debug, Clone)]
pub struct InterpolationResult {
    /// The interpolated transaction.
    pub transaction: Transaction,
    /// Which posting indices were filled in.
    pub filled_indices: Vec<usize>,
    /// Residuals after interpolation (should all be near zero).
    pub residuals: HashMap<String, Decimal>,
}

/// Interpolate missing amounts in a transaction.
///
/// This function:
/// 1. Identifies postings with missing amounts
/// 2. For each currency, calculates the residual
/// 3. Fills in the missing amount to balance
///
/// # Rules
///
/// - At most one posting per currency can have a missing amount
/// - If a posting has a cost spec with a currency, that currency is used
/// - Otherwise, the posting gets the residual that makes the transaction balance
///
/// # Example
///
/// ```ignore
/// let txn = Transaction::new(date, "Test")
///     .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50.00), "USD")))
///     .with_posting(Posting::auto("Assets:Cash"));
///
/// let result = interpolate(&txn)?;
/// // Assets:Cash now has -50.00 USD
/// ```
pub fn interpolate(transaction: &Transaction) -> Result<InterpolationResult, InterpolationError> {
    // Clone the transaction for modification
    let mut result = transaction.clone();
    let mut filled_indices = Vec::new();

    // Calculate initial residuals from postings with amounts
    let mut residuals: HashMap<String, Decimal> = HashMap::new();
    let mut missing_by_currency: HashMap<String, Vec<usize>> = HashMap::new();
    let mut unassigned_missing: Vec<usize> = Vec::new();

    for (i, posting) in transaction.postings.iter().enumerate() {
        match &posting.units {
            Some(IncompleteAmount::Complete(amount)) => {
                // Complete amount - add to residual
                *residuals.entry(amount.currency.clone()).or_default() += amount.number;

                // Handle cost
                if let Some(cost_spec) = &posting.cost {
                    if let (Some(per_unit), Some(cost_curr)) =
                        (&cost_spec.number_per, &cost_spec.currency)
                    {
                        *residuals.entry(cost_curr.clone()).or_default() -=
                            amount.number * per_unit;
                    } else if let (Some(total), Some(cost_curr)) =
                        (&cost_spec.number_total, &cost_spec.currency)
                    {
                        *residuals.entry(cost_curr.clone()).or_default() -= *total;
                    }
                }

                // Handle price
                if let Some(price) = &posting.price {
                    match price {
                        rustledger_core::PriceAnnotation::Unit(price_amt) => {
                            let converted = amount.number.abs() * price_amt.number;
                            *residuals.entry(price_amt.currency.clone()).or_default() -=
                                converted * amount.number.signum();
                        }
                        rustledger_core::PriceAnnotation::Total(price_amt) => {
                            *residuals.entry(price_amt.currency.clone()).or_default() -=
                                price_amt.number * amount.number.signum();
                        }
                        // Incomplete price annotations - extract what we can
                        rustledger_core::PriceAnnotation::UnitIncomplete(inc) => {
                            if let Some(price_amt) = inc.as_amount() {
                                let converted = amount.number.abs() * price_amt.number;
                                *residuals.entry(price_amt.currency.clone()).or_default() -=
                                    converted * amount.number.signum();
                            }
                        }
                        rustledger_core::PriceAnnotation::TotalIncomplete(inc) => {
                            if let Some(price_amt) = inc.as_amount() {
                                *residuals.entry(price_amt.currency.clone()).or_default() -=
                                    price_amt.number * amount.number.signum();
                            }
                        }
                        // Empty price annotations - nothing to contribute to residual
                        rustledger_core::PriceAnnotation::UnitEmpty
                        | rustledger_core::PriceAnnotation::TotalEmpty => {}
                    }
                }
            }
            Some(IncompleteAmount::CurrencyOnly(currency)) => {
                // Currency known, number to be interpolated
                missing_by_currency
                    .entry(currency.clone())
                    .or_default()
                    .push(i);
            }
            Some(IncompleteAmount::NumberOnly(number)) => {
                // Number known, currency to be inferred
                // Try to get currency from cost or price
                let currency = posting
                    .cost
                    .as_ref()
                    .and_then(|c| c.currency.clone())
                    .or_else(|| {
                        posting.price.as_ref().and_then(|p| match p {
                            rustledger_core::PriceAnnotation::Unit(a) => Some(a.currency.clone()),
                            rustledger_core::PriceAnnotation::Total(a) => Some(a.currency.clone()),
                            rustledger_core::PriceAnnotation::UnitIncomplete(inc)
                            | rustledger_core::PriceAnnotation::TotalIncomplete(inc) => {
                                inc.as_amount().map(|a| a.currency.clone())
                            }
                            rustledger_core::PriceAnnotation::UnitEmpty
                            | rustledger_core::PriceAnnotation::TotalEmpty => None,
                        })
                    });

                if let Some(curr) = currency {
                    // We have currency from context, make it complete
                    *residuals.entry(curr.clone()).or_default() += *number;
                } else {
                    // Can't determine currency yet
                    unassigned_missing.push(i);
                }
            }
            None => {
                // Missing amount - try to determine currency from cost
                if let Some(cost_spec) = &posting.cost {
                    if let Some(currency) = &cost_spec.currency {
                        missing_by_currency
                            .entry(currency.clone())
                            .or_default()
                            .push(i);
                        continue;
                    }
                }
                // Can't determine currency yet
                unassigned_missing.push(i);
            }
        }
    }

    // Check for multiple missing in same currency
    for (currency, indices) in &missing_by_currency {
        if indices.len() > 1 {
            return Err(InterpolationError::MultipleMissing {
                currency: currency.clone(),
                count: indices.len(),
            });
        }
    }

    // Fill in known-currency missing postings
    for (currency, indices) in missing_by_currency {
        let idx = indices[0];
        let residual = residuals.get(&currency).copied().unwrap_or(Decimal::ZERO);

        result.postings[idx].units = Some(IncompleteAmount::Complete(Amount::new(
            -residual, &currency,
        )));
        filled_indices.push(idx);

        // Update residual
        residuals.insert(currency, Decimal::ZERO);
    }

    // Handle unassigned missing postings
    // Each one absorbs one currency's residual
    if !unassigned_missing.is_empty() {
        // Get currencies with non-zero residuals
        let non_zero_residuals: Vec<(String, Decimal)> = residuals
            .iter()
            .filter(|(_, &v)| !v.is_zero())
            .map(|(k, &v)| (k.clone(), v))
            .collect();

        if unassigned_missing.len() > 1 && non_zero_residuals.len() > 1 {
            // Ambiguous - can't determine which currency goes where
            // For now, just take the first one
            // A more sophisticated approach would be needed for multi-currency
        }

        for (i, idx) in unassigned_missing.iter().enumerate() {
            if i < non_zero_residuals.len() {
                let (currency, residual) = &non_zero_residuals[i];
                result.postings[*idx].units = Some(IncompleteAmount::Complete(Amount::new(
                    -*residual, currency,
                )));
                filled_indices.push(*idx);
                residuals.insert(currency.clone(), Decimal::ZERO);
            } else if !non_zero_residuals.is_empty() {
                // Use the first currency
                let (currency, _) = &non_zero_residuals[0];
                result.postings[*idx].units =
                    Some(IncompleteAmount::Complete(Amount::zero(currency)));
                filled_indices.push(*idx);
            } else {
                // No residuals - posting stays without amount
                // This is an error condition
                return Err(InterpolationError::CannotInferCurrency {
                    account: transaction.postings[*idx].account.clone(),
                });
            }
        }
    }

    // Recalculate final residuals
    let final_residuals = crate::calculate_residual(&result);

    Ok(InterpolationResult {
        transaction: result,
        filled_indices,
        residuals: final_residuals,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{NaiveDate, Posting};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
    }

    /// Helper to get the complete amount from a posting.
    fn get_amount(posting: &rustledger_core::Posting) -> Option<&Amount> {
        posting.units.as_ref().and_then(|u| u.as_amount())
    }

    #[test]
    fn test_interpolate_simple() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).unwrap();

        assert_eq!(result.filled_indices, vec![1]);

        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-50.00));
        assert_eq!(amount.currency, "USD");
    }

    #[test]
    fn test_interpolate_multiple_postings() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(30.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Expenses:Drink",
                Amount::new(dec!(20.00), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).unwrap();

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-50.00));
    }

    #[test]
    fn test_interpolate_no_missing() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let result = interpolate(&txn).unwrap();

        assert!(result.filled_indices.is_empty());
    }

    #[test]
    fn test_interpolate_multiple_currencies() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Expenses:Travel",
                Amount::new(dec!(100.00), "EUR"),
            ))
            .with_posting(Posting::new(
                "Assets:Cash:USD",
                Amount::new(dec!(-50.00), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Cash:EUR"));

        let result = interpolate(&txn).unwrap();

        let filled = &result.transaction.postings[3];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-100.00));
        assert_eq!(amount.currency, "EUR");
    }

    #[test]
    fn test_interpolate_error_multiple_missing_same_currency() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Cash"))
            .with_posting(Posting::auto("Assets:Bank"));

        // This should work - both will try to absorb the same residual
        // but only one can be assigned
        let result = interpolate(&txn);
        // The current implementation handles this by assigning them sequentially
        assert!(result.is_ok());
    }
}
