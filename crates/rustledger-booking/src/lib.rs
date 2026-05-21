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

mod book;
mod interpolate;
mod pad;

pub use book::{BookedTransaction, BookingEngine, BookingError, CapitalGain, book_transactions};
pub use interpolate::{InterpolationError, InterpolationResult, interpolate};
pub use pad::{PadError, PadResult, expand_pads, merge_with_padding, process_pads};

use bigdecimal::BigDecimal;
use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;
use rustledger_core::{Amount, Currency, IncompleteAmount, Transaction};
use std::collections::HashMap;

/// Calculate the tolerance for a set of amounts.
///
/// Tolerance is the maximum of all individual amount tolerances.
#[must_use]
pub fn calculate_tolerance(amounts: &[&Amount]) -> HashMap<Currency, Decimal> {
    // Pre-allocate for typical case (1-3 currencies per transaction)
    let mut tolerances: HashMap<Currency, Decimal> = HashMap::with_capacity(amounts.len().min(4));

    for amount in amounts {
        let tol = amount.inferred_tolerance();
        tolerances
            .entry(amount.currency.clone())
            .and_modify(|t| *t = (*t).max(tol))
            .or_insert(tol);
    }

    tolerances
}

/// Extract the currency named in a posting's price annotation, if any.
///
/// Returns the currency on `IncompleteAmount::Complete`. `CurrencyOnly`,
/// `NumberOnly`, and the bare-sigil form (`amount: None`) all return
/// `None` — they're shapes where the currency is either missing or
/// supplied later by interpolation. `kind` (Unit vs Total) is irrelevant
/// at this layer.
#[must_use]
pub(crate) fn price_currency_of(posting: &rustledger_core::Posting) -> Option<Currency> {
    posting
        .price
        .as_ref()
        .and_then(|p| p.amount.as_ref())
        .and_then(IncompleteAmount::as_amount)
        .map(|a| a.currency.clone())
}

/// Compute the (currency, signed contribution) a price annotation
/// adds to a transaction's residual for the given units.
///
/// `kind = Unit` ⇒ contribution is `|units| * price * sign(units)`;
/// `kind = Total` ⇒ contribution is `price * sign(units)`.
///
/// Returns `None` for incomplete/empty price annotations where the
/// currency or number is missing — the caller falls back to weighing
/// the posting in its units currency. Used by both `calculate_residual`
/// and `calculate_residual_precise` so the Unit-vs-Total semantics
/// live in one place.
fn price_residual_contribution(
    price: &rustledger_core::PriceAnnotation,
    units: &rustledger_core::Amount,
) -> Option<(Currency, Decimal)> {
    let amt = price
        .amount
        .as_ref()
        .and_then(IncompleteAmount::as_amount)?;
    let signed = match price.kind {
        rustledger_core::PriceKind::Unit => units.number.abs() * amt.number * units.number.signum(),
        rustledger_core::PriceKind::Total => amt.number * units.number.signum(),
    };
    Some((amt.currency.clone(), signed))
}

/// Infer the cost currency from other postings in the transaction.
///
/// Python beancount infers cost currency from simple postings (those without
/// cost specs) when a cost is specified without a currency like `{100}`.
///
/// Currency inference follows this priority:
/// 1. An explicit currency in the cost specification itself (handled by the caller).
/// 2. A price annotation on a simple posting (the price currency takes precedence).
/// 3. The currency of other simple postings (units or currency-only amounts).
/// 4. The currency from a cost spec (e.g., `{0 USD}` for zero-cost items).
#[must_use]
pub(crate) fn infer_cost_currency_from_postings(transaction: &Transaction) -> Option<Currency> {
    // First pass: look for simple postings (no cost spec) - these take priority
    for posting in &transaction.postings {
        // Skip postings with cost specs in first pass
        if posting.cost.is_some() {
            continue;
        }

        // Get the currency from this posting's units
        if let Some(units) = &posting.units {
            match units {
                IncompleteAmount::Complete(amount) => {
                    // If this posting has a price annotation, the "real" currency
                    // is the price currency, not the units currency
                    if let Some(c) = price_currency_of(posting) {
                        return Some(c);
                    }
                    // Simple posting - use its currency
                    return Some(amount.currency.clone());
                }
                IncompleteAmount::CurrencyOnly(currency) => {
                    return Some(currency.clone());
                }
                IncompleteAmount::NumberOnly(_) => {}
            }
        }
    }

    // Second pass: look for cost spec currencies (e.g., `{0 USD}`)
    // This handles zero-cost postings where the cost currency should be used
    for posting in &transaction.postings {
        if let Some(cost) = &posting.cost
            && let Some(currency) = &cost.currency
        {
            return Some(currency.clone());
        }
    }

    None
}

/// Calculate the residual (imbalance) of a transaction.
///
/// Returns a map of currency -> residual amount.
/// A balanced transaction has all residuals within tolerance.
///
/// # TLA+ Specification
///
/// Implements balance checking from `DoubleEntry.tla`:
/// - Invariant: `TransactionsBalance` - For every transaction, `sum(postings) = 0`
/// - Each currency is checked independently
/// - A non-zero residual indicates a violation of double-entry bookkeeping
///
/// See: `spec/tla/DoubleEntry.tla`
#[must_use]
pub fn calculate_residual(transaction: &Transaction) -> HashMap<Currency, Decimal> {
    // Pre-allocate for typical case (1-2 currencies per transaction)
    let mut residuals: HashMap<Currency, Decimal> =
        HashMap::with_capacity(transaction.postings.len().min(4));

    // Lazily compute inferred currency only when needed (most transactions don't need it)
    let mut inferred_cost_currency: Option<Option<Currency>> = None;
    let get_inferred_currency = |cache: &mut Option<Option<Currency>>| -> Option<Currency> {
        cache
            .get_or_insert_with(|| infer_cost_currency_from_postings(transaction))
            .clone()
    };

    for posting in &transaction.postings {
        // Only process complete amounts
        if let Some(IncompleteAmount::Complete(units)) = &posting.units {
            // Determine the "weight" of this posting for balance purposes.
            // - If there's a cost, the weight is in the cost currency (not units currency)
            // - If there's a price annotation, the weight is in the price currency (not units currency)
            // - Otherwise, the weight is just the units

            // Check if cost spec has determinable values.
            // If cost has number but no currency, try to infer currency from:
            // 1. Price annotation
            // 2. Other postings in the transaction
            let cost_contribution = posting.cost.as_ref().and_then(|cost_spec| {
                // Try to get cost currency, falling back to price currency, then other postings
                let inferred_currency = cost_spec
                    .currency
                    .clone()
                    .or_else(|| price_currency_of(posting))
                    .or_else(|| get_inferred_currency(&mut inferred_cost_currency));

                // Check number_total first: when both per-unit and total are present
                // (booking preserves total), use the total directly for exact residual
                // calculation. Division-then-multiplication loses precision.
                if let (Some(total), Some(cost_curr)) =
                    (&cost_spec.number_total, &inferred_currency)
                {
                    Some((cost_curr.clone(), *total * units.number.signum()))
                } else if let (Some(per_unit), Some(cost_curr)) =
                    (&cost_spec.number_per, &inferred_currency)
                {
                    let cost_amount = units.number * per_unit;
                    Some((cost_curr.clone(), cost_amount))
                } else {
                    None // Cost spec without determinable amount (e.g., empty `{}`)
                }
            });

            if let Some((currency, amount)) = cost_contribution {
                // Cost-based posting: weight is in the cost currency
                *residuals.entry(currency).or_default() += amount;
            } else if posting.cost.is_some() {
                // Cost spec exists but has no determinable cost number
                // (e.g., empty `{}`). The CANONICAL weight of a cost-tracked
                // posting is `units × cost`, NOT `units × price` — even if a
                // price annotation is present. Falling through to the price
                // branch would silently produce a balanced residual using
                // the wrong weight (issue #1026). Skip contribution; the
                // booking pass will resolve via lot matching, and the
                // interpolation rule (in `interpolate.rs`) accounts for
                // this posting as one cost-unknown for its currency group.
            } else if let Some(price) = &posting.price {
                // Price annotation: converts units to price currency for balance purposes.
                // The weight is in the price currency, not the units currency.
                if let Some((curr, contribution)) = price_residual_contribution(price, units) {
                    *residuals.entry(curr).or_default() += contribution;
                } else {
                    // Incomplete or bare-sigil price annotation — can't
                    // calculate a price-currency conversion, fall back to units.
                    *residuals.entry(units.currency.clone()).or_default() += units.number;
                }
            } else {
                // Simple posting: weight is just the units
                *residuals.entry(units.currency.clone()).or_default() += units.number;
            }
        }
    }

    residuals
}

/// Convert a `rust_decimal::Decimal` to `BigDecimal` for arbitrary-precision arithmetic.
///
/// Individual `Decimal` values are representable exactly (≤28 significant digits).
/// The precision loss only occurs during arithmetic, so converting before operations
/// preserves full precision.
fn to_big(d: Decimal) -> BigDecimal {
    use std::str::FromStr;
    // rust_decimal Display is exact; BigDecimal FromStr handles any decimal string
    BigDecimal::from_str(&d.to_string()).expect("Decimal always produces valid decimal string")
}

/// Calculate the residual of a transaction using arbitrary-precision arithmetic.
///
/// This mirrors [`calculate_residual`] but uses `BigDecimal` to avoid precision loss
/// when amounts have near-28-digit precision. `rust_decimal` is limited to 28-29
/// significant digits; this function handles arbitrary precision correctly.
#[must_use]
pub fn calculate_residual_precise(transaction: &Transaction) -> HashMap<Currency, BigDecimal> {
    let mut residuals: HashMap<Currency, BigDecimal> =
        HashMap::with_capacity(transaction.postings.len().min(4));

    let mut inferred_cost_currency: Option<Option<Currency>> = None;
    let get_inferred_currency = |cache: &mut Option<Option<Currency>>| -> Option<Currency> {
        cache
            .get_or_insert_with(|| infer_cost_currency_from_postings(transaction))
            .clone()
    };

    for posting in &transaction.postings {
        if let Some(IncompleteAmount::Complete(units)) = &posting.units {
            let units_number = to_big(units.number);

            let cost_contribution = posting.cost.as_ref().and_then(|cost_spec| {
                let inferred_currency = cost_spec
                    .currency
                    .clone()
                    .or_else(|| price_currency_of(posting))
                    .or_else(|| get_inferred_currency(&mut inferred_cost_currency));

                // Check number_total first: when both per-unit and total are present
                // (booking preserves total), use the total directly for exact residual
                // calculation. Division-then-multiplication loses precision.
                if let (Some(total), Some(cost_curr)) =
                    (&cost_spec.number_total, &inferred_currency)
                {
                    Some((
                        cost_curr.clone(),
                        to_big(*total) * to_big(units.number.signum()),
                    ))
                } else if let (Some(per_unit), Some(cost_curr)) =
                    (&cost_spec.number_per, &inferred_currency)
                {
                    let cost_amount = &units_number * to_big(*per_unit);
                    Some((cost_curr.clone(), cost_amount))
                } else {
                    None
                }
            });

            if let Some((currency, amount)) = cost_contribution {
                *residuals.entry(currency).or_default() += amount;
            } else if posting.cost.is_some() {
                // Cost spec exists but has no determinable cost number
                // (e.g., empty `{}`). Same as `calculate_residual` —
                // cost beats price for posting weight; falling through
                // to the price branch produces a wrong-weight balanced
                // residual (issue #1026).
            } else if let Some(price) = &posting.price {
                // Same Unit/Total semantics as `calculate_residual`, but
                // running through BigDecimal to avoid 28-digit precision
                // loss. Inline because the `BigDecimal` math doesn't fit
                // the shared `price_residual_contribution` (which returns
                // `Decimal`).
                if let Some(amt) = price.amount.as_ref().and_then(IncompleteAmount::as_amount) {
                    let signed = match price.kind {
                        rustledger_core::PriceKind::Unit => {
                            units_number.abs() * to_big(amt.number) * to_big(units.number.signum())
                        }
                        rustledger_core::PriceKind::Total => {
                            to_big(amt.number) * to_big(units.number.signum())
                        }
                    };
                    *residuals.entry(amt.currency.clone()).or_default() += signed;
                } else {
                    *residuals.entry(units.currency.clone()).or_default() += units_number.clone();
                }
            } else {
                *residuals.entry(units.currency.clone()).or_default() += units_number;
            }
        }
    }

    residuals
}

/// Check if a transaction is balanced within tolerance.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn is_balanced(transaction: &Transaction, tolerances: &HashMap<Currency, Decimal>) -> bool {
    let residuals = calculate_residual(transaction);

    for (currency, residual) in residuals {
        let tolerance = tolerances.get(&currency).copied().unwrap_or(Decimal::ZERO); // Default 0 (exact balance for integer-only currencies)

        if residual.abs() > tolerance {
            return false;
        }
    }

    true
}

/// Normalize total prices (`@@`) to per-unit prices (`@`) on a transaction.
///
/// This converts `PriceAnnotation::Total` to `PriceAnnotation::Unit` by dividing
/// the total price by the number of units. This should be called AFTER validation
/// (balance checking) to preserve exact total prices for precise residual calculation.
///
/// Matches Python beancount behavior where `@@` is converted to `@`.
pub fn normalize_prices(txn: &mut Transaction) {
    use rustledger_core::{PriceAnnotation, PriceKind};

    for posting in &mut txn.postings {
        if let (Some(IncompleteAmount::Complete(units)), Some(price)) =
            (&posting.units, &posting.price)
            && price.kind == PriceKind::Total
        {
            let normalized = match price.amount.as_ref().and_then(IncompleteAmount::as_amount) {
                Some(total_amount) if !units.number.is_zero() => {
                    let per_unit = total_amount.number / units.number.abs();
                    Some(PriceAnnotation::unit(Amount::new(
                        per_unit,
                        &total_amount.currency,
                    )))
                }
                Some(_) => None, // units.number is zero — leave alone
                None => {
                    // Empty (`@@` with no amount) — Total → Unit sigil swap.
                    // `total_incomplete` with no complete amount cannot be
                    // normalized because we don't have a number to divide.
                    if price.amount.is_none() {
                        Some(PriceAnnotation::unit_empty())
                    } else {
                        None
                    }
                }
            };
            if let Some(normalized_price) = normalized {
                posting.price = Some(normalized_price);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{CostSpec, IncompleteAmount, NaiveDate, Posting, PriceAnnotation};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    // =========================================================================
    // Basic residual tests (existing)
    // =========================================================================

    #[test]
    fn test_calculate_residual_balanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    #[test]
    fn test_calculate_residual_unbalanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-45.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(5.00)));
    }

    #[test]
    fn test_is_balanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
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
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.004), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
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

    // =========================================================================
    // Cost-based residual tests
    // =========================================================================

    /// Test residual calculation with per-unit cost.
    /// Buy 10 AAPL at $150 each = $1500 total cost in USD.
    #[test]
    fn test_calculate_residual_with_per_unit_cost() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(150.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1500.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Cost posting contributes 10 * 150 = 1500 USD
        // Cash posting contributes -1500 USD
        // Residual should be 0
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
        // AAPL should not appear in residuals (cost converts to USD)
        assert_eq!(residual.get("AAPL"), None);
    }

    /// Test residual calculation with total cost.
    /// Buy 10 AAPL with total cost of $1500.
    #[test]
    fn test_calculate_residual_with_total_cost() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number_total(dec!(1500.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1500.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Total cost posting contributes 1500 * signum(10) = 1500 USD
        // Cash posting contributes -1500 USD
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test residual calculation with total cost and negative units (sell).
    #[test]
    fn test_calculate_residual_with_total_cost_negative_units() {
        let txn = Transaction::new(date(2024, 1, 15), "Sell stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number_total(dec!(1500.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(1500.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Total cost with negative units: 1500 * signum(-10) = -1500 USD
        // Cash posting contributes +1500 USD
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test cost spec without amount/currency falls back to units.
    #[test]
    fn test_calculate_residual_cost_without_amount_skips() {
        // When a posting has an empty cost spec (e.g., `{}`) and no price annotation,
        // it doesn't contribute to the residual because the cost will be determined
        // by lot matching during booking. This matches Python beancount behavior.
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                    .with_cost(CostSpec::empty()), // Empty cost spec - doesn't contribute
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "AAPL")));

        let residual = calculate_residual(&txn);
        // Empty cost spec posting doesn't contribute, only the second posting does
        assert_eq!(residual.get("AAPL"), Some(&dec!(-10)));
    }

    /// Issue #1026: when an empty cost spec is paired with a price
    /// annotation (`{} @ price`), the residual computation must NOT
    /// fall through to using the price as the posting's weight. The
    /// canonical weight of a cost-tracked posting is `units × cost`,
    /// not `units × price`. Pre-fix, this branch produced a balanced
    /// residual using the wrong weight; the htsec compat fixture (and
    /// the interpolate.rs caller chain) was the visible victim.
    ///
    /// Pinned here at the lib.rs level so a future revert of the
    /// branch reordering would fail this test directly, independent
    /// of the interpolate.rs end-to-end tests.
    #[test]
    fn test_calculate_residual_empty_cost_spec_with_price_skips_not_uses_price() {
        let txn = Transaction::new(date(2024, 1, 15), "Sale, empty cost + price")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let residual = calculate_residual(&txn);
        // Pre-fix: residual[USD] = 0 (price-as-weight contributed
        // -1500, cancelling cash's +1500).
        // Post-fix: residual[USD] = +1500 (cost-unknown skipped, only
        // cash contributes; the residual stays open for booking-pass
        // lot matching to resolve via cost basis).
        assert_eq!(residual.get("USD"), Some(&dec!(1500)));
    }

    /// Companion to the previous test for the `BigDecimal` variant.
    /// Same fix, same semantics.
    #[test]
    fn test_calculate_residual_precise_empty_cost_spec_with_price_skips_not_uses_price() {
        use bigdecimal::BigDecimal;
        use std::str::FromStr;

        let txn = Transaction::new(date(2024, 1, 15), "Sale, empty cost + price")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let residual = calculate_residual_precise(&txn);
        assert_eq!(
            residual.get("USD"),
            Some(&BigDecimal::from_str("1500").unwrap())
        );
    }

    // =========================================================================
    // Price annotation residual tests
    // =========================================================================

    /// Test residual with per-unit price annotation (@).
    /// -100 USD @ 0.85 EUR means we're converting 100 USD to EUR at 0.85 rate.
    #[test]
    fn test_calculate_residual_with_unit_price() {
        let txn = Transaction::new(date(2024, 1, 15), "Currency exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD"))
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(0.85), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn);
        // Price posting: |-100| * 0.85 * signum(-100) = -85 EUR
        // EUR posting: +85 EUR
        // Total: 0 EUR
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
        // USD should not appear (converted to EUR)
        assert_eq!(residual.get("USD"), None);
    }

    /// Test residual with total price annotation (@@).
    #[test]
    fn test_calculate_residual_with_total_price() {
        let txn = Transaction::new(date(2024, 1, 15), "Currency exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD"))
                    .with_price(PriceAnnotation::total(Amount::new(dec!(85.00), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn);
        // Total price: 85 * signum(-100) = -85 EUR
        // EUR posting: +85 EUR
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test residual with positive units and unit price.
    #[test]
    fn test_calculate_residual_with_unit_price_positive() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy EUR")
            .with_synthesized_posting(
                Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR"))
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(1.18), "USD"))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.30), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Price posting: |85| * 1.18 * signum(85) = 100.30 USD
        // USD posting: -100.30 USD
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `UnitIncomplete` price annotation with complete amount.
    #[test]
    fn test_calculate_residual_unit_incomplete_with_amount() {
        let txn = Transaction::new(date(2024, 1, 15), "Exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD")).with_price(
                    PriceAnnotation::unit_incomplete(IncompleteAmount::Complete(Amount::new(
                        dec!(0.85),
                        "EUR",
                    ))),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test `TotalIncomplete` price annotation with complete amount.
    #[test]
    fn test_calculate_residual_total_incomplete_with_amount() {
        let txn = Transaction::new(date(2024, 1, 15), "Exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD")).with_price(
                    PriceAnnotation::total_incomplete(IncompleteAmount::Complete(Amount::new(
                        dec!(85.00),
                        "EUR",
                    ))),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test `UnitIncomplete` without amount falls back to units.
    #[test]
    fn test_calculate_residual_unit_incomplete_no_amount_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD")).with_price(
                    PriceAnnotation::unit_incomplete(IncompleteAmount::NumberOnly(dec!(0.85))),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Falls back to units since no currency in incomplete amount
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `TotalIncomplete` without amount falls back to units.
    #[test]
    fn test_calculate_residual_total_incomplete_no_amount_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD")).with_price(
                    PriceAnnotation::total_incomplete(IncompleteAmount::NumberOnly(dec!(85.00))),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `UnitEmpty` price annotation falls back to units.
    #[test]
    fn test_calculate_residual_unit_empty_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD"))
                    .with_price(PriceAnnotation::unit_empty()),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Falls back to units
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `TotalEmpty` price annotation falls back to units.
    #[test]
    fn test_calculate_residual_total_empty_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD"))
                    .with_price(PriceAnnotation::total_empty()),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    // =========================================================================
    // Mixed and edge case tests
    // =========================================================================

    /// Test transaction with both cost and regular postings.
    #[test]
    fn test_calculate_residual_mixed_cost_and_simple() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy with fee")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(150.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Fees",
                Amount::new(dec!(10.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1510.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // 10 * 150 + 10 - 1510 = 0
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test sell with cost basis and capital gains.
    #[test]
    fn test_calculate_residual_sell_with_gains() {
        let txn = Transaction::new(date(2024, 6, 15), "Sell stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "AAPL"))
                    .with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150.00))
                            .with_currency("USD"),
                    )
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(175.00), "USD"))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(1750.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Income:CapitalGains",
                Amount::new(dec!(-250.00), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Stock posting with cost: -10 * 150 = -1500 USD (cost takes precedence)
        // Cash: +1750 USD
        // Gains: -250 USD
        // Total: -1500 + 1750 - 250 = 0
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test multi-currency transaction with costs.
    #[test]
    fn test_calculate_residual_multi_currency_with_cost() {
        let txn = Transaction::new(date(2024, 1, 15), "Multi-currency")
            .with_synthesized_posting(
                Posting::new("Assets:Stock:US", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(150.00))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(
                Posting::new("Assets:Stock:EU", Amount::new(dec!(5), "SAP")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(100.00))
                        .with_currency("EUR"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash:USD",
                Amount::new(dec!(-1500.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash:EUR",
                Amount::new(dec!(-500.00), "EUR"),
            ));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test that incomplete units (auto postings) are skipped.
    #[test]
    fn test_calculate_residual_skips_incomplete_units() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash")); // No units

        let residual = calculate_residual(&txn);
        // Only the complete posting is counted
        assert_eq!(residual.get("USD"), Some(&dec!(50.00)));
    }

    // =========================================================================
    // Cost currency inference tests (issue #203)
    // =========================================================================

    /// Test cost currency is inferred from other postings.
    /// This is the exact case from issue #203.
    #[test]
    fn test_calculate_residual_infers_cost_currency_from_other_posting() {
        // 2026-01-01 * "Opening balance"
        //   Assets:Vanguard:IRA:Trad:VFIFX  10 VFIFX {100}
        //   Equity:Opening-Balances      -1000 USD
        //
        // Python beancount infers the cost currency as USD from the second posting.
        let txn = Transaction::new(date(2026, 1, 1), "Opening balance")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Vanguard:IRA:Trad:VFIFX",
                    Amount::new(dec!(10), "VFIFX"),
                )
                .with_cost(CostSpec::empty().with_number_per(dec!(100))),
            )
            .with_synthesized_posting(Posting::new(
                "Equity:Opening-Balances",
                Amount::new(dec!(-1000), "USD"),
            ));

        let residual = calculate_residual(&txn);
        // Cost posting should contribute 10 * 100 = 1000 USD (inferred from other posting)
        // Equity posting contributes -1000 USD
        // Residual should be 0
        assert_eq!(
            residual.get("USD"),
            Some(&dec!(0)),
            "Should balance when cost currency is inferred from other posting"
        );
        // VFIFX should not appear in residuals
        assert_eq!(residual.get("VFIFX"), None);
    }

    /// Test cost currency inference with total cost.
    #[test]
    fn test_calculate_residual_infers_cost_currency_total_cost() {
        // 10 VFIFX {{1000}} with -1000 USD posting
        let txn = Transaction::new(date(2026, 1, 1), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "VFIFX"))
                    .with_cost(CostSpec::empty().with_number_total(dec!(1000))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD")));

        let residual = calculate_residual(&txn);
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test that explicit cost currency takes precedence over inference.
    #[test]
    fn test_calculate_residual_explicit_cost_currency_takes_precedence() {
        // If cost has explicit currency, don't infer from other postings
        let txn = Transaction::new(date(2026, 1, 1), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(100))
                        .with_currency("EUR"), // Explicit EUR
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1000), "USD"), // USD posting
            ));

        let residual = calculate_residual(&txn);
        // Should use EUR (explicit) not USD (from other posting)
        assert_eq!(residual.get("EUR"), Some(&dec!(1000)));
        assert_eq!(residual.get("USD"), Some(&dec!(-1000)));
    }

    /// Test that price annotation takes precedence over other posting inference.
    #[test]
    fn test_calculate_residual_price_annotation_takes_precedence() {
        // If cost has price annotation, use that currency
        let txn = Transaction::new(date(2026, 1, 1), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                    .with_cost(CostSpec::empty().with_number_per(dec!(100)))
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(105), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD")));

        let residual = calculate_residual(&txn);
        // Should use EUR (from price annotation) not USD (from other posting)
        assert_eq!(residual.get("EUR"), Some(&dec!(1000)));
        assert_eq!(residual.get("USD"), Some(&dec!(-1000)));
    }

    // =========================================================================
    // infer_cost_currency_from_postings tests
    // =========================================================================

    /// Test that cost spec currency is used as fallback when no simple postings exist.
    #[test]
    fn test_infer_cost_currency_from_cost_spec() {
        // Transaction with only cost-spec posting - should get currency from cost spec
        let txn = Transaction::new(date(2022, 4, 16), "Free tokens")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(0))
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Bonus"));

        let inferred = infer_cost_currency_from_postings(&txn);
        assert_eq!(inferred.as_deref(), Some("USD"));
    }

    /// Test that simple posting currency takes precedence over cost spec currency.
    #[test]
    fn test_infer_cost_currency_simple_takes_precedence() {
        // Transaction with both simple posting and cost spec - simple should win
        let txn = Transaction::new(date(2022, 4, 16), "Trade")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(10))
                        .with_currency("EUR"),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD")));

        let inferred = infer_cost_currency_from_postings(&txn);
        // Should get USD from the simple posting, not EUR from cost spec
        assert_eq!(inferred.as_deref(), Some("USD"));
    }

    /// Test that zero-cost spec currency is still used for inference.
    #[test]
    fn test_infer_cost_currency_zero_cost() {
        // Zero cost should still provide the currency
        let txn = Transaction::new(date(2022, 4, 16), "Airdrop")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(1000), "SHIB")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(0))
                        .with_currency("JPY"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Airdrop"));

        let inferred = infer_cost_currency_from_postings(&txn);
        assert_eq!(inferred.as_deref(), Some("JPY"));
    }
}
