//! Transaction interpolation.
//!
//! Fills in missing posting amounts to balance transactions.

use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;
use rustledger_core::{Amount, Currency, IncompleteAmount, Transaction};
use std::collections::HashMap;
use thiserror::Error;

/// Errors that can occur during interpolation.
#[derive(Debug, Clone, Error)]
pub enum InterpolationError {
    /// Multiple unknowns in the same currency group, where an unknown is
    /// either a posting with a missing amount or a posting with an empty
    /// cost spec (`{}`) whose cost-basis weight is deferred to booking-
    /// time lot matching. Bean-check enforces "at most one unknown per
    /// currency group" — see issue #1026 for the cost-spec extension.
    ///
    /// The variant name `MultipleMissing` is kept for API stability;
    /// "missing amounts" in the error message is a slight overgeneral
    /// (the count includes cost-unknowns, not just missing amounts), but
    /// the field semantics are correct.
    #[error(
        "multiple postings missing amounts or with unresolved cost specs for currency {currency} ({count} unknowns)"
    )]
    MultipleMissing {
        /// The currency group with too many unknowns.
        currency: Currency,
        /// Total count of unknowns: missing-amount postings plus
        /// empty-cost-spec postings whose weight is deferred to
        /// booking-time lot matching.
        count: usize,
    },

    /// Cannot infer currency for a posting.
    #[error("cannot infer currency for posting to account {account}")]
    CannotInferCurrency {
        /// The account of the posting.
        account: rustledger_core::Account,
    },

    /// Transaction does not balance after interpolation.
    #[error("transaction does not balance: residual {residual} {currency}")]
    DoesNotBalance {
        /// The unbalanced currency.
        currency: Currency,
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
    pub residuals: HashMap<Currency, Decimal>,
}

/// Round an interpolated amount to match existing scale, but never round
/// a non-zero residual to zero (that would leave the transaction unbalanced).
fn round_interpolated(residual: Decimal, existing_scale: Option<u32>) -> Decimal {
    let interpolated = -residual;
    if let Some(scale) = existing_scale {
        let rounded = interpolated.round_dp(scale);
        // If rounding would make non-zero residual into zero, preserve precision
        if rounded.is_zero() && !residual.is_zero() {
            interpolated
        } else {
            rounded
        }
    } else {
        interpolated
    }
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
/// # TLA+ Specification
///
/// Implements invariants from `Interpolation.tla` (post-#1030 redesign for
/// N postings + multi-currency + cost-unknowns):
/// - `AtMostOneUnknownPerCurrency`: For each currency group, at most one
///   posting may be "unknown" — either a missing amount (counts toward
///   the units currency) or an empty cost spec like `{}` (counts toward
///   the cost currency, since the cost-basis weight is unresolved until
///   booking-pass lot matching). Returns `MultipleMissing` if violated.
/// - `CompleteImpliesValidated`: Interpolation only completes the
///   transaction when the validation rule holds.
///
/// The spec models the structural validation rule, not the residual
/// arithmetic that produces filled amounts — see `Interpolation.tla`'s
/// header for the scope rationale.
///
/// See: `spec/tla/Interpolation.tla`
///
/// # Example
///
/// ```ignore
/// let txn = Transaction::new(date, "Test")
///     .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(50.00), "USD")))
///     .with_synthesized_posting(Posting::auto("Assets:Cash"));
///
/// let result = interpolate(&txn)?;
/// // Assets:Cash now has -50.00 USD
/// ```
pub fn interpolate(transaction: &Transaction) -> Result<InterpolationResult, InterpolationError> {
    // Clone the transaction for modification
    let mut result = transaction.clone();
    let mut filled_indices = Vec::new();

    // Lazily compute inferred currency only when needed (most transactions don't need it)
    let mut inferred_cost_currency: Option<Option<Currency>> = None;
    let get_inferred_currency = |cache: &mut Option<Option<Currency>>| -> Option<Currency> {
        cache
            .get_or_insert_with(|| crate::infer_cost_currency_from_postings(transaction))
            .clone()
    };

    // Calculate initial residuals from postings with amounts
    // Pre-allocate for typical case (1-2 currencies per transaction)
    let num_postings = transaction.postings.len();
    let mut residuals: HashMap<Currency, Decimal> = HashMap::with_capacity(num_postings.min(4));
    let mut missing_by_currency: HashMap<Currency, Vec<usize>> = HashMap::with_capacity(2);
    let mut unassigned_missing: Vec<usize> = Vec::with_capacity(2);

    // Track maximum scale (decimal places) per currency for rounding interpolated amounts.
    //
    // Matches Python beancount's `infer_tolerances` rule: only NON-INTEGER posting
    // units contribute to the per-currency tolerance/precision. Integer amounts
    // ("1 CAD" commission, "1 CSU" share count) do NOT contribute — they don't
    // tell us anything about that currency's display precision.
    //
    // Cost spec scales are deliberately NOT included. With Python's default
    // `infer_tolerance_from_cost = False`, cost annotations don't influence the
    // residual quantization either. The natural Decimal arithmetic that flows
    // through `cost_amount = units × per_unit` preserves whatever scale the
    // operands carry, so a transaction with no non-integer posting units in a
    // given currency simply doesn't get a quantization step (the residual is
    // rendered at its natural scale).
    //
    // - #333 (`1 CSU {2800.01 CAD}` + `1 CAD` commission + missing CAD):
    //   no non-integer CAD posting units in this transaction; residual
    //   passes through unrounded at its natural scale, which is 2dp from
    //   the explicit cost literal `{2800.01}` flowing through
    //   `cost_amount = units × per_unit`.
    // - #251 (`70.538 ABC {100 USD}` + missing posting): no non-integer
    //   USD posting units; residual = `70.538 × 100 = 7053.800` (scale 3
    //   from the rust_decimal multiplication), preserved naturally.
    // - #1107 (`-1.763 STOCK {}` lot-matched against high-precision per_unit):
    //   the cash side `336.73 USD` gives USD scale=2; the residual gets
    //   quantized to 2dp instead of inheriting the lot's derived 26-digit
    //   per_unit precision.
    let mut max_scale_by_currency: HashMap<Currency, u32> = HashMap::with_capacity(4);

    // Track per-currency count of postings whose weight contribution is unknown
    // because the cost spec is empty (e.g., `{}`) and resolution is deferred to
    // the booking pass (lot matching). Each such posting is one unknown for
    // interpolation accounting and gets added to the per-currency unknowns
    // total alongside missing-amount postings (issue #1026). Without this,
    // rledger would silently use a fallback weight (price annotation, if
    // present) and accept transactions with more unknowns than the
    // interpolation rule allows.
    let mut cost_unknowns_by_currency: HashMap<Currency, usize> = HashMap::with_capacity(2);

    for (i, posting) in transaction.postings.iter().enumerate() {
        match &posting.units {
            Some(IncompleteAmount::Complete(amount)) => {
                // Track scale (decimal places) for rounding interpolated amounts.
                // Skip integer (scale==0) amounts — matches Python's
                // `infer_tolerances`, which ignores integer posting.units
                // since they don't reflect intentional currency precision.
                let scale = amount.number.scale();
                if scale > 0 {
                    max_scale_by_currency
                        .entry(amount.currency.clone())
                        .and_modify(|s| *s = (*s).max(scale))
                        .or_insert(scale);
                }

                // Determine the "weight" of this posting for balance purposes.
                // This must match the logic in calculate_residual().
                //
                // Rules:
                // - If there's a cost spec, weight is in cost currency (not units)
                // - If there's a price annotation (no cost), weight is in price currency
                // - Otherwise, weight is the units themselves

                // Check if cost spec has determinable values.
                // If cost has number but no currency, try to infer currency from:
                // 1. Price annotation
                // 2. Other postings in the transaction
                let cost_contribution = posting.cost.as_ref().and_then(|cost_spec| {
                    // Try to get cost currency, falling back to price currency, then other postings
                    let inferred_currency = cost_spec
                        .currency
                        .clone()
                        .or_else(|| crate::price_currency_of(posting))
                        .or_else(|| get_inferred_currency(&mut inferred_cost_currency));

                    if let (Some(per_unit), Some(cost_curr)) =
                        (&cost_spec.number_per, &inferred_currency)
                    {
                        let cost_amount = amount.number * per_unit;
                        Some((cost_curr.clone(), cost_amount))
                    } else if let (Some(total), Some(cost_curr)) =
                        (&cost_spec.number_total, &inferred_currency)
                    {
                        // For total cost, sign depends on units sign
                        Some((cost_curr.clone(), *total * amount.number.signum()))
                    } else {
                        None // Cost spec without determinable amount (e.g., empty `{}`)
                    }
                });

                if let Some((currency, cost_amount)) = cost_contribution {
                    // Cost-based posting: weight is in the cost currency.
                    // Cost spec scales are intentionally NOT tracked in
                    // `max_scale_by_currency` — see its declaration for the
                    // rationale (Python beancount with default
                    // `infer_tolerance_from_cost = False`).
                    *residuals.entry(currency).or_default() += cost_amount;
                } else if posting.cost.is_some() {
                    // Cost spec exists but has no determinable cost number (e.g.,
                    // an empty `{}` spec where the lot's cost will be filled by
                    // booking-time lot matching). The WEIGHT of this posting is
                    // the cost basis × units, NOT the price × units — so we must
                    // not fall through to the price branch below and use price
                    // as a substitute (that's what happened pre-#1026 fix and
                    // produced silent acceptance of unsolvable transactions).
                    //
                    // Track this as one unknown for the cost currency. The
                    // post-loop check then enforces the "at most one unknown
                    // per currency group" rule that bean-check enforces.
                    let cost_currency = posting
                        .cost
                        .as_ref()
                        .and_then(|c| c.currency.clone())
                        .or_else(|| crate::price_currency_of(posting))
                        .or_else(|| get_inferred_currency(&mut inferred_cost_currency));
                    if let Some(curr) = cost_currency {
                        *cost_unknowns_by_currency.entry(curr).or_default() += 1;
                    }
                } else if let Some(price) = &posting.price {
                    // Price annotation: converts units to price currency.
                    // Scale tracking: per-unit prices are multipliers, so we
                    // do NOT track their scale. Total prices are explicit
                    // amounts, so we DO track theirs (non-integer scale
                    // only — an integer `@@ 1 USD` shouldn't quantize an
                    // elided same-currency residual to whole units).
                    if let Some(price_amt) =
                        price.amount.as_ref().and_then(IncompleteAmount::as_amount)
                    {
                        let (curr, signed) = match price.kind {
                            rustledger_core::PriceKind::Unit => (
                                price_amt.currency.clone(),
                                amount.number.abs() * price_amt.number * amount.number.signum(),
                            ),
                            rustledger_core::PriceKind::Total => {
                                let scale = price_amt.number.scale();
                                if scale > 0 {
                                    max_scale_by_currency
                                        .entry(price_amt.currency.clone())
                                        .and_modify(|s| *s = (*s).max(scale))
                                        .or_insert(scale);
                                }
                                (
                                    price_amt.currency.clone(),
                                    price_amt.number * amount.number.signum(),
                                )
                            }
                        };
                        *residuals.entry(curr).or_default() += signed;
                    } else {
                        // Incomplete/empty price annotation — fall back to units
                        *residuals.entry(amount.currency.clone()).or_default() += amount.number;
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
                        // Pull currency from the price's complete amount,
                        // regardless of kind. Incomplete/empty prices
                        // contribute nothing here.
                        posting
                            .price
                            .as_ref()
                            .and_then(|p| p.amount.as_ref())
                            .and_then(IncompleteAmount::as_amount)
                            .map(|a| a.currency.clone())
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
                if let Some(cost_spec) = &posting.cost
                    && let Some(currency) = &cost_spec.currency
                {
                    missing_by_currency
                        .entry(currency.clone())
                        .or_default()
                        .push(i);
                    continue;
                }
                // Can't determine currency yet
                unassigned_missing.push(i);
            }
        }
    }

    // Check for multiple unknowns in the same currency group. An "unknown"
    // is either a missing-amount posting or a posting with an empty cost
    // spec (whose cost-basis weight contribution is unknown until booking
    // resolves the lot match). Bean-check enforces "at most one unknown
    // per currency group" — see issue #1026.
    //
    // Iterate currencies in sorted order so the error message is
    // deterministic for the same input. HashMap iteration order is
    // unspecified, so picking "the first failing currency" without
    // sorting would produce non-reproducible test output.
    let mut currencies_with_unknowns: Vec<&Currency> = missing_by_currency
        .keys()
        .chain(cost_unknowns_by_currency.keys())
        .collect();
    currencies_with_unknowns.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    currencies_with_unknowns.dedup();
    for currency in currencies_with_unknowns {
        let missing_count = missing_by_currency
            .get(currency)
            .map_or(0, std::vec::Vec::len);
        let cost_unknown_count = cost_unknowns_by_currency
            .get(currency)
            .copied()
            .unwrap_or(0);
        let total = missing_count + cost_unknown_count;
        if total > 1 {
            return Err(InterpolationError::MultipleMissing {
                currency: currency.clone(),
                count: total,
            });
        }
    }

    // Same rule extended to "would-be" landing currencies for unassigned
    // missing postings: an unassigned-missing posting absorbs residuals
    // across all non-zero currencies at fill time, so it could land in
    // any currency including one with a cost-unknown.
    //
    // Empirically verified against bean-check (issue #1026): bean-check
    // rejects ANY combination of unassigned-missing + cost-unknown, even
    // when the unassigned would semantically prefer a different currency.
    // The reason is that an unassigned posting's currency assignment is
    // determined post-hoc from non-zero residuals, and cost-unknowns
    // contribute an unknown amount to their currency's residual — so the
    // landing currency could always be the cost-unknown's currency. To
    // require the user to make the absorber's currency explicit, reject.
    //
    // Pick the lexicographically-smallest cost-unknown currency for the
    // error so the message is reproducible across runs.
    if !unassigned_missing.is_empty() {
        let mut cost_unknown_keys: Vec<&Currency> = cost_unknowns_by_currency.keys().collect();
        cost_unknown_keys.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        if let Some(curr) = cost_unknown_keys.first() {
            let count = cost_unknowns_by_currency.get(*curr).copied().unwrap_or(0);
            return Err(InterpolationError::MultipleMissing {
                currency: (*curr).clone(),
                count: count + unassigned_missing.len(),
            });
        }
    }

    // Fill in known-currency missing postings
    for (currency, indices) in missing_by_currency {
        let idx = indices[0];
        let residual = residuals.get(&currency).copied().unwrap_or(Decimal::ZERO);

        let interpolated =
            round_interpolated(residual, max_scale_by_currency.get(&currency).copied());

        result.postings[idx].units = Some(IncompleteAmount::Complete(Amount::new(
            interpolated,
            &currency,
        )));
        filled_indices.push(idx);

        // Update residual to reflect actual interpolated amount (may have rounding difference)
        *residuals.entry(currency).or_default() += interpolated;
    }

    // Handle unassigned missing postings
    // Each one absorbs one or more currencies' residuals
    if !unassigned_missing.is_empty() {
        // Get currencies with non-zero residuals
        let non_zero_residuals: Vec<(Currency, Decimal)> = residuals
            .iter()
            .filter(|&(_, v)| !v.is_zero())
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        // Special case: single missing posting with multiple currencies
        // This is multi-currency interpolation - split into multiple postings
        if unassigned_missing.len() == 1 && non_zero_residuals.len() > 1 {
            let idx = unassigned_missing[0];
            let original_posting = &transaction.postings[idx];

            // Fill the first currency into the original posting
            let (first_currency, first_residual) = &non_zero_residuals[0];
            let interpolated = round_interpolated(
                *first_residual,
                max_scale_by_currency.get(first_currency).copied(),
            );
            result.postings[idx].units = Some(IncompleteAmount::Complete(Amount::new(
                interpolated,
                first_currency,
            )));
            filled_indices.push(idx);
            *residuals.entry(first_currency.clone()).or_default() += interpolated;

            // Add new postings for remaining currencies
            for (currency, residual) in non_zero_residuals.iter().skip(1) {
                let mut new_posting = original_posting.clone();
                let interpolated =
                    round_interpolated(*residual, max_scale_by_currency.get(currency).copied());
                new_posting.units = Some(IncompleteAmount::Complete(Amount::new(
                    interpolated,
                    currency,
                )));
                result.postings.push(new_posting);
                filled_indices.push(result.postings.len() - 1);
                *residuals.entry(currency.clone()).or_default() += interpolated;
            }
        } else {
            // Check for ambiguous elision: more unassigned missing postings than
            // available residual currencies means multiple postings would all be
            // assigned to the same currency, which is ambiguous and an error.
            if unassigned_missing.len() > non_zero_residuals.len() && !non_zero_residuals.is_empty()
            {
                let (currency, _) = &non_zero_residuals[0];
                return Err(InterpolationError::MultipleMissing {
                    currency: currency.clone(),
                    count: unassigned_missing.len(),
                });
            }

            // Standard case: assign one currency per missing posting
            for (i, idx) in unassigned_missing.iter().enumerate() {
                if i < non_zero_residuals.len() {
                    let (currency, residual) = &non_zero_residuals[i];
                    let interpolated =
                        round_interpolated(*residual, max_scale_by_currency.get(currency).copied());
                    result.postings[*idx].units = Some(IncompleteAmount::Complete(Amount::new(
                        interpolated,
                        currency,
                    )));
                    filled_indices.push(*idx);
                    *residuals.entry(currency.clone()).or_default() += interpolated;
                } else if !non_zero_residuals.is_empty() {
                    // Use the first currency
                    let (currency, _) = &non_zero_residuals[0];
                    result.postings[*idx].units =
                        Some(IncompleteAmount::Complete(Amount::zero(currency)));
                    filled_indices.push(*idx);
                } else if let Some(currency) = get_inferred_currency(&mut inferred_cost_currency) {
                    // No residuals but we can infer currency from cost basis
                    // This handles balanced cost-basis transactions like:
                    //   Assets:Crypto  100 USDC {1.0 USD}
                    //   Assets:Cash   -100 USD
                    //   Income:Trading  ; <- infer 0 USD from cost basis
                    result.postings[*idx].units =
                        Some(IncompleteAmount::Complete(Amount::zero(&currency)));
                    filled_indices.push(*idx);
                } else {
                    // No residuals and cannot infer currency
                    return Err(InterpolationError::CannotInferCurrency {
                        account: transaction.postings[*idx].account.clone(),
                    });
                }
            }
        }
    }

    // Prune postings that were filled with zero amounts. Python
    // beancount drops these from its rendered output too — they
    // contribute nothing to the transaction balance and would just
    // clutter BQL / JSON / format output.
    //
    // The historical concern (#877) was that pre-validation pruning
    // hid `E1001 Account X was never opened` errors on elided
    // postings to unopened accounts. The loader pipeline now runs an
    // EARLY validation phase before booking (see
    // `rustledger_validate::Phase::Early` and the "Python Compatibility
    // Policy" section in CLAUDE.md), so account-presence checks fire
    // BEFORE we reach this prune step. That's a deliberate divergence
    // from Python — Python silently accepts these references; rledger
    // catches them. Tested by `test_zero_interpolated_posting_keeps_e1001_*`
    // in `rustledger-loader`.
    //
    // Iterate in reverse so indices stay valid as we remove.
    let mut indices_to_remove: Vec<usize> = filled_indices
        .iter()
        .filter(|&&idx| {
            result.postings.get(idx).is_some_and(|p| {
                p.units
                    .as_ref()
                    .and_then(|u| u.as_amount())
                    .is_some_and(|a| a.number.is_zero())
            })
        })
        .copied()
        .collect();
    indices_to_remove.sort_unstable_by(|a, b| b.cmp(a));

    for idx in &indices_to_remove {
        result.postings.remove(*idx);
    }

    // Drop the removed indices from filled_indices and shift the
    // surviving ones down to reflect the new posting positions.
    let final_filled_indices: Vec<usize> = filled_indices
        .into_iter()
        .filter(|idx| !indices_to_remove.contains(idx))
        .map(|idx| {
            let adjustment = indices_to_remove.iter().filter(|&&r| r < idx).count();
            idx - adjustment
        })
        .collect();

    // Return the residuals we've been tracking incrementally
    // (no need to recalculate - we've updated residuals as we filled amounts)
    Ok(InterpolationResult {
        transaction: result,
        filled_indices: final_filled_indices,
        residuals,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{NaiveDate, Posting};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    /// Helper to get the complete amount from a posting.
    fn get_amount(posting: &rustledger_core::Posting) -> Option<&Amount> {
        posting.units.as_ref().and_then(|u| u.as_amount())
    }

    #[test]
    fn test_interpolate_simple() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

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
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(30.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Expenses:Drink",
                Amount::new(dec!(20.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).unwrap();

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-50.00));
    }

    #[test]
    fn test_interpolate_no_missing() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let result = interpolate(&txn).unwrap();

        assert!(result.filled_indices.is_empty());
    }

    #[test]
    fn test_interpolate_multiple_currencies() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Expenses:Travel",
                Amount::new(dec!(100.00), "EUR"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash:USD",
                Amount::new(dec!(-50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash:EUR"));

        let result = interpolate(&txn).unwrap();

        let filled = &result.transaction.postings[3];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-100.00));
        assert_eq!(amount.currency, "EUR");
    }

    #[test]
    fn test_interpolate_error_multiple_missing_same_currency() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"))
            .with_synthesized_posting(Posting::auto("Assets:Bank"));

        // Multiple unassigned missing postings with a single residual currency
        // is ambiguous and should return MultipleMissing error.
        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "expected MultipleMissing error, got: {result:?}"
        );
    }

    #[test]
    fn test_interpolate_multiple_missing_different_currencies_ok() {
        // Two elided postings but two residual currencies - each gets one
        let txn = Transaction::new(date(2024, 1, 15), "Multi-currency")
            .with_synthesized_posting(Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD")))
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")))
            .with_synthesized_posting(Posting::auto("Liabilities:CreditCard"))
            .with_synthesized_posting(Posting::auto("Equity:Exchange"));

        // Two unassigned missing, two non-zero residuals - this is unambiguous
        let result = interpolate(&txn);
        assert!(
            result.is_ok(),
            "expected success for different-currency elision, got: {result:?}"
        );
    }

    #[test]
    fn test_interpolate_with_per_unit_cost() {
        // 2015-10-02 *
        //   Assets:Stock   10 HOOL {100.00 USD}
        //   Assets:Cash
        //
        // Expected: Assets:Cash should be interpolated to -1000.00 USD
        let txn = Transaction::new(date(2015, 10, 2), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(100.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

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
            "USD residual should be ~0, got {residual}"
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
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_total(dec!(1000.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

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
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(8), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(701.20))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Commission",
                Amount::new(dec!(7.95), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

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
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number_per(dec!(100.00))
                            .with_currency("USD"),
                    )
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(120.00),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(1200.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Income:Gains"));

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
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(100.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
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
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-5), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(100.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        assert_eq!(amount.number, dec!(500.00)); // Positive (receiving cash)
    }

    // =========================================================================
    // Multi-currency interpolation tests
    // =========================================================================

    #[test]
    fn test_interpolate_multi_currency_single_elided() {
        // Test case from basic.beancount:
        // 2008-04-02 * "Gilbert paid back for iPhone"
        //   Assets:Cash                            440.00 CAD
        //   Assets:AccountsReceivable             -431.92 USD
        //   Assets:Cash
        //
        // Expected: The elided Assets:Cash becomes TWO postings:
        //   Assets:Cash: -440.00 CAD
        //   Assets:Cash: 431.92 USD
        let txn = Transaction::new(date(2008, 4, 2), "Gilbert paid back for iPhone")
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(440.00), "CAD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:AccountsReceivable",
                Amount::new(dec!(-431.92), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Should now have 4 postings (original 3 + 1 added for second currency)
        assert_eq!(
            result.transaction.postings.len(),
            4,
            "should split elided posting into 2"
        );

        // Check that all residuals are zero
        for (currency, residual) in &result.residuals {
            assert!(
                residual.abs() < dec!(0.01),
                "{currency} residual should be ~0, got {residual}"
            );
        }

        // Verify the amounts (order may vary based on HashMap iteration)
        let mut found_cad = false;
        let mut found_usd = false;
        for posting in &result.transaction.postings {
            if let Some(amount) = get_amount(posting)
                && posting.account.as_str() == "Assets:Cash"
            {
                if amount.currency == "CAD" && amount.number == dec!(-440.00) {
                    found_cad = true;
                } else if amount.currency == "USD" && amount.number == dec!(431.92) {
                    found_usd = true;
                }
            }
        }
        assert!(found_cad, "should have -440.00 CAD posting");
        assert!(found_usd, "should have 431.92 USD posting");
    }

    #[test]
    fn test_interpolate_multi_currency_three_currencies() {
        // Three currencies with one elided posting
        let txn = Transaction::new(date(2024, 1, 15), "Multi-currency test")
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(200), "EUR")))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(300), "GBP")))
            .with_synthesized_posting(Posting::auto("Equity:Opening"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Should now have 6 postings (original 4 + 2 added)
        assert_eq!(result.transaction.postings.len(), 6);

        // All residuals should be zero
        for (currency, residual) in &result.residuals {
            assert!(
                residual.abs() < dec!(0.01),
                "{currency} residual should be ~0, got {residual}"
            );
        }
    }

    // =========================================================================
    // Cost currency inference tests (issue #203)
    // =========================================================================

    /// Test interpolation with cost currency inferred from other postings.
    /// This is the exact case from issue #203.
    #[test]
    fn test_interpolate_cost_currency_inferred_from_other_posting() {
        // 2026-01-01 * "Opening balance"
        //   Assets:Vanguard:IRA:Trad:VFIFX  10 VFIFX {100}
        //   Equity:Opening-Balances
        //
        // The cost currency should be inferred, and the elided posting should
        // be filled with -1000 USD.
        let txn = Transaction::new(date(2026, 1, 1), "Opening balance")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Vanguard:IRA:Trad:VFIFX",
                    Amount::new(dec!(10), "VFIFX"),
                )
                .with_cost(rustledger_core::CostSpec::empty().with_number_per(dec!(100))),
            )
            .with_synthesized_posting(Posting::new(
                "Equity:Opening-Balances",
                Amount::new(dec!(-1000), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Transaction should balance
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.abs() < dec!(0.01),
            "USD residual should be ~0, got {residual}"
        );
    }

    /// Test interpolation where the cash posting is elided.
    #[test]
    fn test_interpolate_cost_currency_inferred_elided_cash() {
        // Like issue #203 but with elided cash posting:
        // 2026-01-01 * "Opening balance"
        //   Assets:Vanguard:IRA:Trad:VFIFX  10 VFIFX {100}
        //   Equity:Opening-Balances  -1000 USD
        //
        // Both postings are complete, should just balance.
        let txn = Transaction::new(date(2026, 1, 1), "Opening balance")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Vanguard:IRA:Trad:VFIFX",
                    Amount::new(dec!(10), "VFIFX"),
                )
                .with_cost(rustledger_core::CostSpec::empty().with_number_per(dec!(100))),
            )
            .with_synthesized_posting(Posting::new(
                "Equity:Opening-Balances",
                Amount::new(dec!(-1000), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // No postings filled since both are complete
        assert!(result.filled_indices.is_empty());

        // Should balance
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.abs() < dec!(0.01),
            "USD residual should be ~0, got {residual}"
        );
    }

    // =========================================================================
    // Interpolation rounding tests (issue #268)
    // =========================================================================

    /// Test that interpolated amounts are rounded to match the precision of other amounts.
    /// This matches Python beancount's behavior where interpolated amounts use the same
    /// quantum (decimal places) as other amounts in the same currency.
    ///
    /// Issue: <https://github.com/rustledger/rustledger/issues/268>
    #[test]
    fn test_interpolate_rounds_to_quantum() {
        // From issue #268:
        // 2026-01-02 * "..."
        //   Assets:Cash
        //   Assets:Abc                    12.3340 ABC {140.02 USD, 2025-01-01}
        //   Expenses:Abc                    -0.01 USD
        //
        // Cost: 12.3340 * 140.02 = 1727.006680 USD
        // Python rounds Cash to -1727.00 (2 decimal places from -0.01 USD)
        // Residual: 1727.006680 - 0.01 - 1727.00 = -0.003320 USD (within 0.005 tolerance)
        let txn = Transaction::new(date(2026, 1, 2), "Test")
            .with_synthesized_posting(Posting::auto("Assets:Cash"))
            .with_synthesized_posting(
                Posting::new("Assets:Abc", Amount::new(dec!(12.3340), "ABC")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(140.02))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Abc",
                Amount::new(dec!(-0.01), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Check that Cash was filled
        assert_eq!(result.filled_indices, vec![0]);

        // The interpolated amount should be rounded to 2 decimal places
        // (matching the -0.01 USD in Expenses:Abc)
        let filled = &result.transaction.postings[0];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        assert_eq!(
            amount.number,
            dec!(-1727.00),
            "should be -1727.00 USD (rounded to 2 decimal places)"
        );

        // The residual should be non-zero but small (within tolerance)
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert_eq!(
            residual,
            dec!(-0.003320),
            "residual should be -0.003320 USD"
        );
    }

    /// Test that interpolation uses the maximum scale when multiple amounts have different scales.
    #[test]
    fn test_interpolate_uses_max_scale() {
        // When we have amounts with different scales, use the maximum.
        // 0.1 USD (scale 1) and 0.001 USD (scale 3) -> interpolate to scale 3
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new("Expenses:A", Amount::new(dec!(0.1), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:B", Amount::new(dec!(0.001), "USD")))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");

        // The amount is exactly -0.101, which fits in 3 decimal places
        assert_eq!(amount.number, dec!(-0.101));
        // Scale should be 3 (the maximum of 1 and 3)
        assert_eq!(amount.number.scale(), 3);
    }

    /// Test that cost spec scale is used when other postings have lower scale.
    ///
    /// Issue: <https://github.com/rustledger/rustledger/issues/333>
    ///
    /// When a transaction has:
    /// - A cost spec with decimal places (e.g., {2800.01 CAD})
    /// - Other postings with fewer decimal places (e.g., 1 CAD)
    ///
    /// The interpolated amount should use the cost spec's scale, not the
    /// lower scale from other postings.
    #[test]
    fn test_interpolate_cost_scale_preserved() {
        // From issue #333:
        // 2026-01-19 * "Buy stock"
        //   Assets:Stock  1 CSU { 2800.01 CAD }
        //   Expenses:Commission  1 CAD
        //   Assets:Cash
        //
        // Cost: 1 * 2800.01 = 2800.01 CAD (scale 2)
        // Commission: 1 CAD (scale 0)
        // Without fix: Cash rounds to -2801.00 (scale 0), leaving 0.01 residual
        // With fix: Cash is -2801.01 (scale 2), transaction balances
        let txn = Transaction::new(date(2026, 1, 19), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(1), "CSU")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(2800.01))
                        .with_currency("CAD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Commission",
                Amount::new(dec!(1), "CAD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Check that Cash was filled
        assert_eq!(result.filled_indices, vec![2]);

        // The interpolated amount should be -2801.01 (scale 2 from cost spec)
        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "CAD");
        assert_eq!(
            amount.number,
            dec!(-2801.01),
            "should be -2801.01 CAD (preserving cost spec precision)"
        );

        // Transaction should balance (no residual)
        let residual = result
            .residuals
            .get("CAD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.is_zero(),
            "CAD residual should be 0, got {residual}"
        );
    }

    // =========================================================================
    // Currency inference from cost basis tests
    // =========================================================================

    /// Test that zero-amount postings are removed when transaction balances perfectly.
    /// Zero-amount interpolated postings are pruned by booking.
    ///
    /// When a transaction with cost basis balances to zero (cost equals
    /// cash), the elided counterpart fills with 0 and gets dropped from
    /// the booked output — matches Python beancount's display behavior.
    /// The #877 invariant (catching E1001 on the elided posting's
    /// account) is preserved by running the loader's early-phase
    /// account validator BEFORE booking; see `rustledger-validate`'s
    /// `Phase::Early` and `test_zero_interpolated_posting_keeps_e1001_on_unopened_account`
    /// in `rustledger-loader/tests/loader_test.rs` for the
    /// end-to-end coverage.
    ///
    /// Example:
    /// ```beancount
    /// Assets:Crypto    100 USDC {1.0 USD, 2022-04-16}
    /// Assets:Cash     -100 USD
    /// Income:Trading   ; <- fills to 0 USD, pruned
    /// ```
    #[test]
    fn test_interpolate_balanced_cost_prunes_zero_posting() {
        let txn = Transaction::new(date(2022, 4, 16), "Trade")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "USDC")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(1.0))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-100), "USD")))
            .with_synthesized_posting(Posting::auto("Income:Trading"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        assert!(
            result.filled_indices.is_empty(),
            "zero-amount filled posting should have been pruned"
        );
        assert_eq!(
            result.transaction.postings.len(),
            2,
            "Income:Trading filled to 0 USD should be pruned"
        );
        assert!(
            !result
                .transaction
                .postings
                .iter()
                .any(|p| p.account.as_str() == "Income:Trading"),
            "Income:Trading should not be in postings after pruning"
        );
    }

    /// Zero-cost basis: empty posting fills to 0 and is pruned.
    ///
    /// Example:
    /// ```beancount
    /// Assets:Crypto    100 TOKEN {0 USD}
    /// Income:Bonus     ; <- fills to 0 USD, pruned
    /// ```
    #[test]
    fn test_interpolate_zero_cost_prunes_zero_posting() {
        let txn = Transaction::new(date(2022, 4, 16), "Free tokens")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_per(dec!(0))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Bonus"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        assert!(
            result.filled_indices.is_empty(),
            "zero-amount filled posting should have been pruned"
        );
        assert_eq!(result.transaction.postings.len(), 1);
    }

    /// Zero total cost: empty posting fills to 0 and is pruned.
    ///
    /// Example:
    /// ```beancount
    /// Assets:Crypto    100 TOKEN {{0 USD}}
    /// Income:Bonus     ; <- fills to 0 USD, pruned
    /// ```
    #[test]
    fn test_interpolate_zero_total_cost_prunes_zero_posting() {
        let txn = Transaction::new(date(2022, 4, 16), "Free tokens")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number_total(dec!(0))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Bonus"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        assert!(
            result.filled_indices.is_empty(),
            "zero-amount filled posting should have been pruned"
        );
        assert_eq!(result.transaction.postings.len(), 1);
    }

    // ─── Issue #1026: empty cost spec + missing posting in same group ───
    //
    // bean-check rejects with "Too many missing numbers for currency
    // group 'CCY'" when a transaction has both:
    //   1. A posting with empty cost spec `{}` (cost-basis weight unknown
    //      until booking-pass lot matching).
    //   2. Another posting in the same currency group missing its amount.
    //
    // Pre-fix, rledger silently used the price annotation as the
    // posting's weight when cost was unknown, producing a balanced
    // residual and accepting the transaction.

    /// Minimal repro from #1026's body: position with `{} @ price` plus
    /// missing-amount Income:PnL must error.
    #[test]
    fn test_interpolate_empty_cost_spec_with_missing_amount_errors() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "sell what was never bought")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Htsec:Positions",
                    Amount::new(dec!(-13000.00), "SH513050"),
                )
                .with_cost(CostSpec::empty()) // empty `{}` — unknown cost
                .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                    dec!(1.300),
                    "CNY",
                ))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Htsec:Cash",
                Amount::new(dec!(16900.00), "CNY"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Htsec:Cash",
                Amount::new(dec!(-0.85), "CNY"),
            ))
            .with_synthesized_posting(Posting::new(
                "Expenses:Htsec:Commission",
                Amount::new(dec!(0.85), "CNY"),
            ))
            .with_synthesized_posting(Posting::auto("Income:Htsec:PnL"));

        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "expected MultipleMissing error from empty cost spec + missing posting; got {result:?}"
        );
        if let Err(InterpolationError::MultipleMissing { currency, count }) = result {
            assert_eq!(currency.as_str(), "CNY");
            assert!(
                count >= 2,
                "expected count >= 2 unknowns in CNY group, got {count}"
            );
        }
    }

    /// Empty cost spec by itself (no other missing posting) is OK — the
    /// booking pass will resolve the lot match. Pre- and post-fix should
    /// agree.
    #[test]
    fn test_interpolate_empty_cost_spec_alone_ok() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Sell HOOL")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let result = interpolate(&txn);
        assert!(
            result.is_ok(),
            "single empty cost spec with no missing postings should succeed; got {result:?}"
        );
    }

    /// Two empty cost specs in the same currency group: two cost-unknowns
    /// in one group, no missing-amount postings needed → still errors.
    #[test]
    fn test_interpolate_two_empty_cost_specs_same_currency_errors() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Two unknown-cost sells")
            .with_synthesized_posting(
                Posting::new("Assets:StockA", Amount::new(dec!(-10), "AAPL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(
                Posting::new("Assets:StockB", Amount::new(dec!(-5), "GOOG"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(2000),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(11500), "USD")));

        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "two empty cost specs in same currency should error; got {result:?}"
        );
    }

    /// Cost-unknown in one currency + missing-amount posting in a
    /// DIFFERENT currency: should succeed. The two unknowns belong to
    /// disjoint currency groups, so the rule is satisfied per-group.
    /// Verifies the rule check is per-currency, not global.
    #[test]
    fn test_interpolate_empty_cost_spec_with_missing_in_different_currency_ok() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Sale + currency-known absorber")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty()) // cost-unknown in USD
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:Fee", Amount::new(dec!(5), "EUR")))
            .with_synthesized_posting(Posting {
                // Missing amount, currency known via CurrencyOnly: lands in EUR.
                units: Some(IncompleteAmount::CurrencyOnly("EUR".into())),
                ..Posting::auto("Income:Misc")
            });

        let result = interpolate(&txn);
        assert!(
            result.is_ok(),
            "cost-unknown in USD + missing-amount in EUR should succeed (disjoint groups); \
             got {result:?}"
        );
    }

    /// Issue #1107: an interpolated residual must not inherit the high
    /// scale of a derived per-unit cost (which can be 26+ digits from
    /// `total / units` division). Python beancount quantizes the
    /// residual to currency precision derived from explicit posting
    /// units, not cost spec scales.
    ///
    /// Repro: a sell with explicit high-precision per-unit cost. Pre-fix,
    /// the cost scale (5) merged into `max_scale_by_currency[USD]`,
    /// rounding the residual to 5dp (`-36.72498`). Post-fix, only the
    /// `336.73 USD` cash side contributes to USD precision (scale=2), so
    /// the residual is `-36.72` (matches bean-query exactly).
    #[test]
    fn test_interpolate_residual_ignores_cost_spec_scale() {
        use rustledger_core::CostSpec;

        let cost_spec = CostSpec {
            number_per: Some(dec!(170.16734)),
            number_total: None,
            currency: Some(Currency::from("USD")),
            date: None,
            label: None,
            merge: false,
        };

        let txn = Transaction::new(date(2016, 2, 12), "Sell")
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(336.73), "USD"),
            ))
            .with_synthesized_posting(
                Posting::new("Assets:Brokerage", Amount::new(dec!(-1.763), "STOCK"))
                    .with_cost(cost_spec)
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(191.00),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::auto("Income:Capital-Gains"));

        let result = interpolate(&txn).expect("interpolation should succeed");
        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("Income should have amount");

        assert_eq!(
            amount.currency.as_str(),
            "USD",
            "residual currency should be USD"
        );
        assert_eq!(
            amount.number.scale(),
            2,
            "residual scale must be 2 (USD precision from `336.73 USD`), \
             not 5 (from cost spec). Pre-fix this was 5. (#1107)"
        );
        assert_eq!(
            amount.number,
            dec!(-36.72),
            "residual value should match bean-query exactly (#1107). \
             Was -36.72498 before fix."
        );
    }

    /// End-to-end #1107 repro through the booking pass — this is the
    /// path that actually surfaces in real ledgers, where the booking
    /// engine derives a 26+ digit per-unit cost from `{{total}} / units`
    /// (or lot-matches a `{}` sell against such a derived cost) and
    /// previously propagated that scale into the interpolated residual.
    ///
    /// Concretely models the healthequity fixture pattern: buy with
    /// `{{total}}` total cost, sell with `{}` lot-match. After booking,
    /// the sell's filled `CostSpec` carries the high-scale `per_unit` from
    /// the division — and interpolation must STILL round the missing
    /// Income residual to USD's 2dp (no posting-unit-scale cost-scale
    /// contamination).
    #[test]
    fn test_interpolate_residual_after_booking_total_cost_division() {
        use crate::book::BookingEngine;
        use rustledger_core::{Cost, CostSpec, IncompleteAmount, PriceAnnotation};

        // Buy: 1.763 STOCK {{300.00 USD}} → booking derives
        // per_unit = 300.00 / 1.763 = ~170.16449... at 26-digit scale.
        let buy = Transaction::new(date(2016, 1, 1), "Buy")
            .with_synthesized_posting(
                Posting::new("Assets:Brokerage", Amount::new(dec!(1.763), "STOCK")).with_cost(
                    CostSpec {
                        number_per: None,
                        number_total: Some(dec!(300.00)),
                        currency: Some(Currency::from("USD")),
                        date: None,
                        label: None,
                        merge: false,
                    },
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-300.00), "USD"),
            ));

        // Sell: -1.763 STOCK {} @ 191.00 USD — empty cost spec; booking
        // lot-matches against the previous buy, filling the high-scale
        // derived per_unit. Income is missing, must be interpolated.
        let sell = Transaction::new(date(2016, 2, 12), "Sell")
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(336.73), "USD"),
            ))
            .with_synthesized_posting(
                Posting::new("Assets:Brokerage", Amount::new(dec!(-1.763), "STOCK"))
                    .with_cost(CostSpec::empty())
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(191.00), "USD"))),
            )
            .with_synthesized_posting(Posting::auto("Income:Capital-Gains"));

        let mut engine = BookingEngine::new();
        engine.apply(&buy);

        // book_and_interpolate handles the empty `{}` lot match AND
        // runs interpolation on the booked transaction. The Income
        // residual must end up at USD's 2dp scale — pre-fix this
        // inherited the lot's derived 26-digit per_unit scale.
        let result = engine
            .book_and_interpolate(&sell)
            .expect("booking+interpolation should succeed");

        let income = &result.transaction.postings[2];
        let amount = get_amount(income).expect("Income should have an amount after interpolation");

        assert_eq!(amount.currency.as_str(), "USD");
        assert!(
            amount.number.scale() <= 2,
            "residual scale must be ≤ 2 (USD's tracked precision), \
             not inherited from the lot's high-scale derived per_unit. \
             Got scale={} number={}",
            amount.number.scale(),
            amount.number
        );

        // Use `_ = Cost::new` to keep the import live without an
        // unrelated unused-import warning if the test grows.
        let _ = Cost::new(dec!(1), "USD");
        let _: Option<IncompleteAmount> = None;
    }

    /// UNASSIGNED missing posting (no currency context) instead of a
    /// currency-known one. bean-check rejects this because the
    /// unassigned could absorb residuals across all currencies including
    /// the cost-unknown's; the rejection is conservative-by-design.
    /// Pins the empirically-verified bean-check parity (#1026 review).
    #[test]
    fn test_interpolate_empty_cost_spec_with_unassigned_in_different_currency_errors() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Sale + unassigned absorber")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:Fee", Amount::new(dec!(5), "EUR")))
            .with_synthesized_posting(Posting::auto("Income:Misc"));

        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "cost-unknown + unassigned-missing must error even when in different \
             currencies (bean-check parity); got {result:?}"
        );
    }
}
