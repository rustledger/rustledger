//! Position type representing units held at a cost.
//!
//! A [`Position`] represents a holding of some units of a currency or commodity,
//! optionally with an associated cost basis (lot). Positions with costs are used
//! for tracking investments and calculating capital gains.

use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::{Amount, Cost, CostSpec};

/// A position is units of a currency held at an optional cost.
///
/// For simple currencies (cash), positions typically have no cost.
/// For investments (stocks, crypto), positions track the cost basis
/// for capital gains calculations.
///
/// # Examples
///
/// ```
/// use rustledger_core::{Amount, Cost, Position};
/// use rust_decimal_macros::dec;
///
/// // Simple position (no cost)
/// let cash = Position::simple(Amount::new(dec!(1000.00), "USD"));
/// assert!(cash.cost.is_none());
///
/// // Position with cost (lot)
/// let cost = Cost::new(dec!(150.00), "USD")
///     .with_date(rustledger_core::naive_date(2024, 1, 15).unwrap());
/// let stock = Position::with_cost(
///     Amount::new(dec!(10), "AAPL"),
///     cost
/// );
/// assert!(stock.cost.is_some());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct Position {
    /// The units held (number + currency/commodity)
    pub units: Amount,
    /// The cost basis (if tracked)
    pub cost: Option<Cost>,
}

impl Position {
    /// Create a new position without cost tracking.
    ///
    /// Use this for simple currency positions like cash.
    #[must_use]
    pub const fn simple(units: Amount) -> Self {
        Self { units, cost: None }
    }

    /// Create a new position with cost tracking.
    ///
    /// Use this for investment positions (stocks, crypto, etc.)
    /// where cost basis matters.
    #[must_use]
    pub const fn with_cost(units: Amount, cost: Cost) -> Self {
        Self {
            units,
            cost: Some(cost),
        }
    }

    /// Build the booked position for a posting's `units` and optional cost
    /// spec: [`Self::with_cost`] when the cost spec resolves to a [`Cost`],
    /// otherwise [`Self::simple`].
    ///
    /// Single source for the validator's inventory-addition path and the pad
    /// engine, which had byte-identical copies (mirrors the cost-bearing add
    /// branch of `BookingEngine::apply`). [`CostSpec::resolve`] returns `None`
    /// for an empty `{}` spec or a zero-units `Total` cost, so those book as a
    /// simple (uncosted) position rather than panicking.
    #[must_use]
    pub fn from_posting(
        units: &Amount,
        cost_spec: Option<&CostSpec>,
        date: crate::NaiveDate,
    ) -> Self {
        match cost_spec.and_then(|cs| cs.resolve(units.number, date)) {
            Some(cost) => Self::with_cost(units.clone(), cost),
            None => Self::simple(units.clone()),
        }
    }

    /// Check if this position is empty (zero units).
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.units.is_zero()
    }

    /// Get the currency of this position's units.
    #[must_use]
    pub fn currency(&self) -> &str {
        &self.units.currency
    }

    /// Get the cost currency, if this position has a cost.
    #[must_use]
    pub fn cost_currency(&self) -> Option<&str> {
        self.cost.as_ref().map(|c| c.currency.as_str())
    }

    /// Calculate the book value (total cost) of this position.
    ///
    /// Returns `None` if there is no cost, or if `units × cost` leaves
    /// `rust_decimal`'s range (see [`Cost::total_cost`]).
    #[must_use]
    pub fn book_value(&self) -> Option<Amount> {
        self.cost
            .as_ref()
            .and_then(|c| c.total_cost(self.units.number))
    }

    /// Check if this position matches a cost specification.
    ///
    /// Returns `true` if:
    /// - Both have no cost, or
    /// - The position's cost matches the spec
    #[must_use]
    pub fn matches_cost_spec(&self, spec: &CostSpec) -> bool {
        match (&self.cost, spec.is_empty()) {
            (None, true) => true,
            (None, false) => false,
            // A spec that constrains nothing matches every lot, so skip the
            // field-by-field walk. `matches` returns `true` for an all-`None`
            // spec by construction, which makes this a short-circuit rather
            // than a second rule. Ordered selection calls this once per lot
            // per reduction, and the bare `{}` FIFO sell is the spec that
            // reaches it most (#2083).
            (Some(_), true) => true,
            (Some(cost), false) => spec.matches(cost),
        }
    }

    /// Negate this position (reverse the sign of units).
    #[must_use]
    pub fn neg(&self) -> Self {
        Self {
            units: -&self.units,
            cost: self.cost.clone(),
        }
    }

    /// Check if this position can be reduced by another amount.
    ///
    /// A position can be reduced if:
    /// - The currencies match
    /// - The reduction is in the opposite direction (selling what you have)
    #[must_use]
    pub fn can_reduce(&self, reduction: &Amount) -> bool {
        self.units.currency == reduction.currency
            && self.units.number.signum() != reduction.number.signum()
    }

    /// Reduce this position by some units.
    ///
    /// Returns `Some(remaining)` if the reduction is valid, `None` otherwise.
    /// The reduction must be in the opposite direction of the position.
    #[must_use]
    pub fn reduce(&self, reduction: Decimal) -> Option<Self> {
        if self.units.number.signum() == reduction.signum() {
            return None; // Can't reduce in same direction
        }

        let new_units = self.units.number + reduction;

        // Check if we're crossing zero (over-reducing)
        if new_units.signum() != self.units.number.signum() && !new_units.is_zero() {
            return None;
        }

        Some(Self {
            units: Amount::new(new_units, self.units.currency.clone()),
            cost: self.cost.clone(),
        })
    }

    /// Split this position, taking some units and leaving the rest.
    ///
    /// Returns `(taken, remaining)` where `taken` has the specified units
    /// and `remaining` has the rest. Both share the same cost.
    #[must_use]
    pub fn split(&self, take_units: Decimal) -> (Self, Self) {
        let taken = Self {
            units: Amount::new(take_units, self.units.currency.clone()),
            cost: self.cost.clone(),
        };
        let remaining = Self {
            units: Amount::new(self.units.number - take_units, self.units.currency.clone()),
            cost: self.cost.clone(),
        };
        (taken, remaining)
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.units)?;
        if let Some(cost) = &self.cost {
            write!(f, " {cost}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::NaiveDate;
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        crate::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_simple_position() {
        let pos = Position::simple(Amount::new(dec!(1000.00), "USD"));
        assert_eq!(pos.units.number, dec!(1000.00));
        assert_eq!(pos.currency(), "USD");
        assert!(pos.cost.is_none());
    }

    #[test]
    fn test_position_with_cost() {
        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 15));
        let pos = Position::with_cost(Amount::new(dec!(10), "AAPL"), cost);

        assert_eq!(pos.units.number, dec!(10));
        assert_eq!(pos.currency(), "AAPL");
        assert_eq!(pos.cost_currency(), Some("USD"));
    }

    #[test]
    fn test_from_posting_resolves_cost_or_simple() {
        use crate::{CostNumber, CostSpec};
        use rust_decimal::Decimal;

        let units = Amount::new(dec!(10), "AAPL");
        // Resolvable cost spec → with_cost.
        let spec = CostSpec::empty()
            .with_number(CostNumber::PerUnit { value: dec!(150) })
            .with_currency("USD");
        let pos = Position::from_posting(&units, Some(&spec), date(2024, 1, 15));
        assert_eq!(pos.cost_currency(), Some("USD"));
        // No cost spec → simple.
        let pos = Position::from_posting(&units, None, date(2024, 1, 15));
        assert!(pos.cost.is_none());
        // Zero-units Total cost → simple (no cost), NOT a divide-by-zero panic.
        let zero = Amount::new(Decimal::ZERO, "AAPL");
        let total = CostSpec::empty()
            .with_number(CostNumber::Total { value: dec!(100) })
            .with_currency("USD");
        let pos = Position::from_posting(&zero, Some(&total), date(2024, 1, 15));
        assert!(
            pos.cost.is_none(),
            "zero-units Total cost must book uncosted, not panic"
        );
    }

    #[test]
    fn test_book_value() {
        let cost = Cost::new(dec!(150.00), "USD");
        let pos = Position::with_cost(Amount::new(dec!(10), "AAPL"), cost);

        let book_value = pos.book_value().unwrap();
        assert_eq!(book_value.number, dec!(1500.00));
        assert_eq!(book_value.currency, "USD");
    }

    #[test]
    fn test_book_value_no_cost() {
        let pos = Position::simple(Amount::new(dec!(1000.00), "USD"));
        assert!(pos.book_value().is_none());
    }

    #[test]
    fn test_is_empty() {
        let empty = Position::simple(Amount::zero("USD"));
        assert!(empty.is_empty());

        let non_empty = Position::simple(Amount::new(dec!(100), "USD"));
        assert!(!non_empty.is_empty());
    }

    #[test]
    fn test_neg() {
        let pos = Position::simple(Amount::new(dec!(100), "USD"));
        let neg = pos.neg();
        assert_eq!(neg.units.number, dec!(-100));
    }

    #[test]
    fn test_reduce() {
        let pos = Position::simple(Amount::new(dec!(100), "USD"));

        // Valid reduction
        let reduced = pos.reduce(dec!(-30)).unwrap();
        assert_eq!(reduced.units.number, dec!(70));

        // Can't reduce in same direction
        assert!(pos.reduce(dec!(30)).is_none());

        // Can't over-reduce
        assert!(pos.reduce(dec!(-150)).is_none());

        // Can reduce to zero
        let zero = pos.reduce(dec!(-100)).unwrap();
        assert!(zero.is_empty());
    }

    #[test]
    fn test_split() {
        let cost = Cost::new(dec!(150.00), "USD");
        let pos = Position::with_cost(Amount::new(dec!(10), "AAPL"), cost);

        let (taken, remaining) = pos.split(dec!(3));
        assert_eq!(taken.units.number, dec!(3));
        assert_eq!(remaining.units.number, dec!(7));

        // Both share same cost
        assert_eq!(taken.cost, pos.cost);
        assert_eq!(remaining.cost, pos.cost);
    }

    #[test]
    fn test_matches_cost_spec() {
        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 15));
        let pos = Position::with_cost(Amount::new(dec!(10), "AAPL"), cost);

        // Empty spec matches
        assert!(pos.matches_cost_spec(&CostSpec::empty()));

        // Matching spec
        let spec = CostSpec::empty()
            .with_number(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            })
            .with_currency("USD");
        assert!(pos.matches_cost_spec(&spec));

        // Non-matching spec
        let spec = CostSpec::empty().with_number(crate::CostNumber::PerUnit {
            value: dec!(160.00),
        });
        assert!(!pos.matches_cost_spec(&spec));
    }

    #[test]
    fn test_display() {
        let cost = Cost::new(dec!(150.00), "USD");
        let pos = Position::with_cost(Amount::new(dec!(10), "AAPL"), cost);
        let s = format!("{pos}");
        assert!(s.contains("10 AAPL"));
        assert!(s.contains("150.00 USD"));
    }
}
