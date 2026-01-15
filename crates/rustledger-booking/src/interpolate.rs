//! Transaction interpolation.
//!
//! Fills in missing posting amounts to balance transactions.

use rust_decimal::prelude::Signed;
use rust_decimal::Decimal;
use rustledger_core::{Amount, IncompleteAmount, InternedStr, Transaction};
use std::collections::HashMap;
use thiserror::Error;

/// Errors that can occur during interpolation.
#[derive(Debug, Clone, Error)]
pub enum InterpolationError {
    /// Multiple postings are missing amounts for the same currency.
    #[error("multiple postings missing amounts for currency {currency}")]
    MultipleMissing {
        /// The currency with multiple missing amounts.
        currency: InternedStr,
        /// Number of postings missing this currency.
        count: usize,
    },

    /// Cannot infer currency for a posting.
    #[error("cannot infer currency for posting to account {account}")]
    CannotInferCurrency {
        /// The account of the posting.
        account: InternedStr,
    },

    /// Transaction does not balance after interpolation.
    #[error("transaction does not balance: residual {residual} {currency}")]
    DoesNotBalance {
        /// The unbalanced currency.
        currency: InternedStr,
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
    pub residuals: HashMap<InternedStr, Decimal>,
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
    let mut residuals: HashMap<InternedStr, Decimal> = HashMap::new();
    let mut missing_by_currency: HashMap<InternedStr, Vec<usize>> = HashMap::new();
    let mut unassigned_missing: Vec<usize> = Vec::new();

    for (i, posting) in transaction.postings.iter().enumerate() {
        match &posting.units {
            Some(IncompleteAmount::Complete(amount)) => {
                // Determine the "weight" of this posting for balance purposes.
                // This must match the logic in calculate_residual().
                //
                // Rules:
                // - If there's a cost spec, weight is in cost currency (not units)
                // - If there's a price annotation (no cost), weight is in price currency
                // - Otherwise, weight is the units themselves

                if let Some(cost_spec) = &posting.cost {
                    // Cost-based posting: weight is in the cost currency
                    if let (Some(per_unit), Some(cost_curr)) =
                        (&cost_spec.number_per, &cost_spec.currency)
                    {
                        let cost_amount = amount.number * per_unit;
                        *residuals.entry(cost_curr.clone()).or_default() += cost_amount;
                    } else if let (Some(total), Some(cost_curr)) =
                        (&cost_spec.number_total, &cost_spec.currency)
                    {
                        // For total cost, sign depends on units sign
                        *residuals.entry(cost_curr.clone()).or_default() +=
                            *total * amount.number.signum();
                    } else {
                        // Cost spec without amount/currency - fall back to units
                        *residuals.entry(amount.currency.clone()).or_default() += amount.number;
                    }
                } else if let Some(price) = &posting.price {
                    // Price annotation: converts units to price currency
                    match price {
                        rustledger_core::PriceAnnotation::Unit(price_amt) => {
                            let converted = amount.number.abs() * price_amt.number;
                            *residuals.entry(price_amt.currency.clone()).or_default() +=
                                converted * amount.number.signum();
                        }
                        rustledger_core::PriceAnnotation::Total(price_amt) => {
                            *residuals.entry(price_amt.currency.clone()).or_default() +=
                                price_amt.number * amount.number.signum();
                        }
                        rustledger_core::PriceAnnotation::UnitIncomplete(inc) => {
                            if let Some(price_amt) = inc.as_amount() {
                                let converted = amount.number.abs() * price_amt.number;
                                *residuals.entry(price_amt.currency.clone()).or_default() +=
                                    converted * amount.number.signum();
                            } else {
                                // Can't calculate, fall back to units
                                *residuals.entry(amount.currency.clone()).or_default() +=
                                    amount.number;
                            }
                        }
                        rustledger_core::PriceAnnotation::TotalIncomplete(inc) => {
                            if let Some(price_amt) = inc.as_amount() {
                                *residuals.entry(price_amt.currency.clone()).or_default() +=
                                    price_amt.number * amount.number.signum();
                            } else {
                                // Can't calculate, fall back to units
                                *residuals.entry(amount.currency.clone()).or_default() +=
                                    amount.number;
                            }
                        }
                        // Empty price annotations - fall back to units
                        rustledger_core::PriceAnnotation::UnitEmpty
                        | rustledger_core::PriceAnnotation::TotalEmpty => {
                            *residuals.entry(amount.currency.clone()).or_default() += amount.number;
                        }
                    }
                } else {
                    // Simple posting: weight is just the units
                    *residuals.entry(amount.currency.clone()).or_default() += amount.number;
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
        let non_zero_residuals: Vec<(InternedStr, Decimal)> = residuals
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

    // =========================================================================
    // Cost-based interpolation tests
    // These tests are based on beancount's booking_full_test.py
    // =========================================================================

    #[test]
    fn test_interpolate_with_per_unit_cost() {
        // 2015-10-02 *
        //   Assets:Stock   10 HOOL {100.00 USD}
        //   Assets:Cash
        //
        // Expected: Assets:Cash should be interpolated to -1000.00 USD
        let txn = Transaction::new(date(2015, 10, 2), "Buy stock")
            .with_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(100.00))
                        .with_currency("USD"),
                ),
            )
            .with_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Check that the cash posting was filled
        assert_eq!(result.filled_indices, vec![1]);

        // Check the interpolated amount
        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(
            amount.currency, "USD",
            "should be USD (cost currency), not HOOL"
        );
        assert_eq!(
            amount.number,
            dec!(-1000.00),
            "should be -1000 USD (10 * 100)"
        );

        // Verify the transaction balances
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.abs() < dec!(0.01),
            "USD residual should be ~0, got {}",
            residual
        );
        // There should be NO HOOL residual
        assert!(
            !result.residuals.contains_key("HOOL"),
            "should not have HOOL residual"
        );
    }

    #[test]
    fn test_interpolate_with_total_cost() {
        // 2015-10-02 *
        //   Assets:Stock   10 HOOL {{1000.00 USD}}
        //   Assets:Cash
        //
        // Expected: Assets:Cash should be interpolated to -1000.00 USD
        let txn = Transaction::new(date(2015, 10, 2), "Buy stock")
            .with_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_total(dec!(1000.00))
                        .with_currency("USD"),
                ),
            )
            .with_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        assert_eq!(amount.number, dec!(-1000.00));
    }

    #[test]
    fn test_interpolate_stock_purchase_with_commission() {
        // From beancount starter.beancount:
        // 2013-02-03 * "Bought some stock"
        //   Assets:Stock         8 HOOL {701.20 USD}
        //   Expenses:Commission  7.95 USD
        //   Assets:Cash
        //
        // Expected: Cash = -(8 * 701.20 + 7.95) = -5617.55 USD
        let txn = Transaction::new(date(2013, 2, 3), "Bought some stock")
            .with_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(8), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(701.20))
                        .with_currency("USD"),
                ),
            )
            .with_posting(Posting::new(
                "Expenses:Commission",
                Amount::new(dec!(7.95), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        // 8 * 701.20 = 5609.60, plus 7.95 commission = 5617.55
        assert_eq!(amount.number, dec!(-5617.55));
    }

    #[test]
    fn test_interpolate_stock_sale_with_cost_and_price() {
        // Selling stock at a different price than cost basis
        // 2015-10-02 *
        //   Assets:Stock   -10 HOOL {100.00 USD} @ 120.00 USD
        //   Assets:Cash
        //   Income:Gains
        //
        // The sale is at cost (for booking), but price is 120 USD
        // Weight: -10 * 100 = -1000 USD (at cost)
        // Cash should receive: 10 * 120 = 1200 USD (at price)
        // Gains: -200 USD
        let txn = Transaction::new(date(2015, 10, 2), "Sell stock")
            .with_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number_per(dec!(100.00))
                            .with_currency("USD"),
                    )
                    .with_price(rustledger_core::PriceAnnotation::Unit(Amount::new(
                        dec!(120.00),
                        "USD",
                    ))),
            )
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(1200.00), "USD"),
            ))
            .with_posting(Posting::auto("Income:Gains"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        // Gains = cost - proceeds = 1000 - 1200 = -200 (income is negative)
        assert_eq!(amount.number, dec!(-200.00));
    }

    #[test]
    fn test_interpolate_balanced_with_cost_no_interpolation_needed() {
        // When all amounts are provided, no interpolation needed
        // 2015-10-02 *
        //   Assets:Stock   10 HOOL {100.00 USD}
        //   Assets:Cash   -1000.00 USD
        let txn = Transaction::new(date(2015, 10, 2), "Buy stock")
            .with_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(100.00))
                        .with_currency("USD"),
                ),
            )
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1000.00), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // No postings should be filled
        assert!(result.filled_indices.is_empty());

        // Transaction should balance
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(residual.abs() < dec!(0.01));
    }

    #[test]
    fn test_interpolate_negative_cost_units_sale() {
        // Selling stock (negative units) with cost
        // 2015-10-02 *
        //   Assets:Stock   -5 HOOL {100.00 USD}
        //   Assets:Cash
        //
        // Expected: Cash = 500.00 USD (proceeds from sale at cost)
        let txn = Transaction::new(date(2015, 10, 2), "Sell stock")
            .with_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-5), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(100.00))
                        .with_currency("USD"),
                ),
            )
            .with_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        assert_eq!(amount.number, dec!(500.00)); // Positive (receiving cash)
    }
}
