//! Amount type representing a decimal number with a currency.
//!
//! An [`Amount`] is the fundamental unit of value in Beancount, combining a decimal
//! number with a currency code. It supports arithmetic operations and tolerance-based
//! comparison for balance checking.

use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::{Add, AddAssign, Neg, Sub, SubAssign};

use crate::intern::InternedStr;

/// An amount is a quantity paired with a currency.
///
/// # Examples
///
/// ```
/// use rustledger_core::Amount;
/// use rust_decimal_macros::dec;
///
/// let amount = Amount::new(dec!(100.00), "USD");
/// assert_eq!(amount.number, dec!(100.00));
/// assert_eq!(amount.currency, "USD");
///
/// // Arithmetic operations
/// let other = Amount::new(dec!(50.00), "USD");
/// let sum = &amount + &other;
/// assert_eq!(sum.number, dec!(150.00));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Amount {
    /// The decimal quantity
    pub number: Decimal,
    /// The currency code (e.g., "USD", "EUR", "AAPL")
    pub currency: InternedStr,
}

impl Amount {
    /// Create a new amount.
    #[must_use]
    pub fn new(number: Decimal, currency: impl Into<InternedStr>) -> Self {
        Self {
            number,
            currency: currency.into(),
        }
    }

    /// Create a zero amount with the given currency.
    #[must_use]
    pub fn zero(currency: impl Into<InternedStr>) -> Self {
        Self {
            number: Decimal::ZERO,
            currency: currency.into(),
        }
    }

    /// Check if the amount is zero.
    #[must_use]
    pub const fn is_zero(&self) -> bool {
        self.number.is_zero()
    }

    /// Check if the amount is positive.
    #[must_use]
    pub const fn is_positive(&self) -> bool {
        self.number.is_sign_positive() && !self.number.is_zero()
    }

    /// Check if the amount is negative.
    #[must_use]
    pub const fn is_negative(&self) -> bool {
        self.number.is_sign_negative()
    }

    /// Get the absolute value of this amount.
    #[must_use]
    pub fn abs(&self) -> Self {
        Self {
            number: self.number.abs(),
            currency: self.currency.clone(),
        }
    }

    /// Get the scale (number of decimal places) of this amount.
    #[must_use]
    pub const fn scale(&self) -> u32 {
        self.number.scale()
    }

    /// Calculate the inferred tolerance for this amount.
    ///
    /// Tolerance is `0.5 * 10^(-scale)`, so:
    /// - scale 0 (integer) → tolerance 0.5
    /// - scale 1 → tolerance 0.05
    /// - scale 2 → tolerance 0.005
    #[must_use]
    pub fn inferred_tolerance(&self) -> Decimal {
        // tolerance = 5 * 10^(-(scale+1)) = 0.5 * 10^(-scale)
        Decimal::new(5, self.number.scale() + 1)
    }

    /// Check if this amount is near zero within tolerance.
    #[must_use]
    pub fn is_near_zero(&self, tolerance: Decimal) -> bool {
        self.number.abs() <= tolerance
    }

    /// Check if this amount is near another amount within tolerance.
    ///
    /// Returns `false` if currencies don't match.
    #[must_use]
    pub fn is_near(&self, other: &Self, tolerance: Decimal) -> bool {
        self.currency == other.currency && (self.number - other.number).abs() <= tolerance
    }

    /// Check if this amount equals another within the given tolerance.
    ///
    /// This is an alias for `is_near()` with a more explicit name for equality comparison.
    /// Returns `false` if currencies don't match.
    ///
    /// # Example
    ///
    /// ```
    /// use rustledger_core::Amount;
    /// use rust_decimal_macros::dec;
    ///
    /// let a = Amount::new(dec!(100.00), "USD");
    /// let b = Amount::new(dec!(100.004), "USD");
    ///
    /// // Within tolerance of 0.005
    /// assert!(a.eq_with_tolerance(&b, dec!(0.005)));
    ///
    /// // Outside tolerance of 0.003
    /// assert!(!a.eq_with_tolerance(&b, dec!(0.003)));
    /// ```
    #[must_use]
    pub fn eq_with_tolerance(&self, other: &Self, tolerance: Decimal) -> bool {
        self.is_near(other, tolerance)
    }

    /// Check if this amount equals another using auto-inferred tolerance.
    ///
    /// The tolerance is computed as the maximum of both amounts' inferred tolerances,
    /// which is based on their decimal precision (scale).
    ///
    /// # Example
    ///
    /// ```
    /// use rustledger_core::Amount;
    /// use rust_decimal_macros::dec;
    ///
    /// let a = Amount::new(dec!(100.00), "USD");  // scale 2 -> tolerance 0.005
    /// let b = Amount::new(dec!(100.004), "USD"); // scale 3 -> tolerance 0.0005
    ///
    /// // Uses max tolerance (0.005), so these are equal
    /// assert!(a.eq_auto_tolerance(&b));
    /// ```
    #[must_use]
    pub fn eq_auto_tolerance(&self, other: &Self) -> bool {
        if self.currency != other.currency {
            return false;
        }
        let tolerance = self.inferred_tolerance().max(other.inferred_tolerance());
        (self.number - other.number).abs() <= tolerance
    }

    /// Round this amount to the given number of decimal places.
    #[must_use]
    pub fn round_dp(&self, dp: u32) -> Self {
        Self {
            number: self.number.round_dp(dp),
            currency: self.currency.clone(),
        }
    }
}

impl fmt::Display for Amount {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.number, self.currency)
    }
}

// Arithmetic operations on references

impl Add for &Amount {
    type Output = Amount;

    fn add(self, other: &Amount) -> Amount {
        debug_assert_eq!(
            self.currency, other.currency,
            "Cannot add amounts with different currencies"
        );
        Amount {
            number: self.number + other.number,
            currency: self.currency.clone(),
        }
    }
}

impl Sub for &Amount {
    type Output = Amount;

    fn sub(self, other: &Amount) -> Amount {
        debug_assert_eq!(
            self.currency, other.currency,
            "Cannot subtract amounts with different currencies"
        );
        Amount {
            number: self.number - other.number,
            currency: self.currency.clone(),
        }
    }
}

impl Neg for &Amount {
    type Output = Amount;

    fn neg(self) -> Amount {
        Amount {
            number: -self.number,
            currency: self.currency.clone(),
        }
    }
}

// Arithmetic operations on owned values

impl Add for Amount {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        &self + &other
    }
}

impl Sub for Amount {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        &self - &other
    }
}

impl Neg for Amount {
    type Output = Self;

    fn neg(self) -> Self {
        -&self
    }
}

impl AddAssign<&Self> for Amount {
    fn add_assign(&mut self, other: &Self) {
        debug_assert_eq!(
            self.currency, other.currency,
            "Cannot add amounts with different currencies"
        );
        self.number += other.number;
    }
}

impl SubAssign<&Self> for Amount {
    fn sub_assign(&mut self, other: &Self) {
        debug_assert_eq!(
            self.currency, other.currency,
            "Cannot subtract amounts with different currencies"
        );
        self.number -= other.number;
    }
}

/// An incomplete amount specification used in postings before interpolation.
///
/// In Beancount, postings can have incomplete amount specifications that
/// will be filled in by the interpolation algorithm:
///
/// - `100.00 USD` - Complete amount
/// - `USD` - Currency only, number to be interpolated
/// - `100.00` - Number only, currency to be inferred
/// - (nothing) - Entire amount to be interpolated
///
/// This type represents all these cases before the interpolation phase.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum IncompleteAmount {
    /// Complete amount with both number and currency
    Complete(Amount),
    /// Only number specified, currency to be inferred from context (cost, price, or other postings)
    NumberOnly(Decimal),
    /// Only currency specified, number to be interpolated to balance the transaction
    CurrencyOnly(InternedStr),
}

impl IncompleteAmount {
    /// Create a complete amount.
    #[must_use]
    pub fn complete(number: Decimal, currency: impl Into<InternedStr>) -> Self {
        Self::Complete(Amount::new(number, currency))
    }

    /// Create a number-only incomplete amount.
    #[must_use]
    pub const fn number_only(number: Decimal) -> Self {
        Self::NumberOnly(number)
    }

    /// Create a currency-only incomplete amount.
    #[must_use]
    pub fn currency_only(currency: impl Into<InternedStr>) -> Self {
        Self::CurrencyOnly(currency.into())
    }

    /// Get the number if present.
    #[must_use]
    pub const fn number(&self) -> Option<Decimal> {
        match self {
            Self::Complete(a) => Some(a.number),
            Self::NumberOnly(n) => Some(*n),
            Self::CurrencyOnly(_) => None,
        }
    }

    /// Get the currency if present.
    #[must_use]
    pub fn currency(&self) -> Option<&str> {
        match self {
            Self::Complete(a) => Some(&a.currency),
            Self::NumberOnly(_) => None,
            Self::CurrencyOnly(c) => Some(c),
        }
    }

    /// Check if this is a complete amount.
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        matches!(self, Self::Complete(_))
    }

    /// Get as a complete Amount if possible.
    #[must_use]
    pub const fn as_amount(&self) -> Option<&Amount> {
        match self {
            Self::Complete(a) => Some(a),
            _ => None,
        }
    }

    /// Convert to a complete Amount, consuming self.
    #[must_use]
    pub fn into_amount(self) -> Option<Amount> {
        match self {
            Self::Complete(a) => Some(a),
            _ => None,
        }
    }
}

impl From<Amount> for IncompleteAmount {
    fn from(amount: Amount) -> Self {
        Self::Complete(amount)
    }
}

impl fmt::Display for IncompleteAmount {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Complete(a) => write!(f, "{a}"),
            Self::NumberOnly(n) => write!(f, "{n}"),
            Self::CurrencyOnly(c) => write!(f, "{c}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_new() {
        let amount = Amount::new(dec!(100.00), "USD");
        assert_eq!(amount.number, dec!(100.00));
        assert_eq!(amount.currency, "USD");
    }

    #[test]
    fn test_zero() {
        let amount = Amount::zero("EUR");
        assert!(amount.is_zero());
        assert_eq!(amount.currency, "EUR");
    }

    #[test]
    fn test_is_positive_negative() {
        let pos = Amount::new(dec!(100), "USD");
        let neg = Amount::new(dec!(-100), "USD");
        let zero = Amount::zero("USD");

        assert!(pos.is_positive());
        assert!(!pos.is_negative());

        assert!(!neg.is_positive());
        assert!(neg.is_negative());

        assert!(!zero.is_positive());
        assert!(!zero.is_negative());
    }

    #[test]
    fn test_add() {
        let a = Amount::new(dec!(100.00), "USD");
        let b = Amount::new(dec!(50.00), "USD");
        let sum = &a + &b;
        assert_eq!(sum.number, dec!(150.00));
        assert_eq!(sum.currency, "USD");
    }

    #[test]
    fn test_sub() {
        let a = Amount::new(dec!(100.00), "USD");
        let b = Amount::new(dec!(50.00), "USD");
        let diff = &a - &b;
        assert_eq!(diff.number, dec!(50.00));
    }

    #[test]
    fn test_neg() {
        let a = Amount::new(dec!(100.00), "USD");
        let neg_a = -&a;
        assert_eq!(neg_a.number, dec!(-100.00));
    }

    #[test]
    fn test_add_assign() {
        let mut a = Amount::new(dec!(100.00), "USD");
        let b = Amount::new(dec!(50.00), "USD");
        a += &b;
        assert_eq!(a.number, dec!(150.00));
    }

    #[test]
    fn test_inferred_tolerance() {
        // scale 0 -> 0.5
        let a = Amount::new(dec!(100), "USD");
        assert_eq!(a.inferred_tolerance(), dec!(0.5));

        // scale 2 -> 0.005
        let b = Amount::new(dec!(100.00), "USD");
        assert_eq!(b.inferred_tolerance(), dec!(0.005));

        // scale 3 -> 0.0005
        let c = Amount::new(dec!(100.000), "USD");
        assert_eq!(c.inferred_tolerance(), dec!(0.0005));
    }

    #[test]
    fn test_is_near_zero() {
        let a = Amount::new(dec!(0.004), "USD");
        assert!(a.is_near_zero(dec!(0.005)));
        assert!(!a.is_near_zero(dec!(0.003)));
    }

    #[test]
    fn test_is_near() {
        let a = Amount::new(dec!(100.00), "USD");
        let b = Amount::new(dec!(100.004), "USD");
        assert!(a.is_near(&b, dec!(0.005)));
        assert!(!a.is_near(&b, dec!(0.003)));

        // Different currencies
        let c = Amount::new(dec!(100.00), "EUR");
        assert!(!a.is_near(&c, dec!(1.0)));
    }

    #[test]
    fn test_display() {
        let a = Amount::new(dec!(1234.56), "USD");
        assert_eq!(format!("{a}"), "1234.56 USD");
    }

    #[test]
    fn test_abs() {
        let neg = Amount::new(dec!(-100.00), "USD");
        let abs = neg.abs();
        assert_eq!(abs.number, dec!(100.00));
    }

    #[test]
    fn test_eq_with_tolerance() {
        let a = Amount::new(dec!(100.00), "USD");
        let b = Amount::new(dec!(100.004), "USD");

        // Within tolerance
        assert!(a.eq_with_tolerance(&b, dec!(0.005)));
        assert!(b.eq_with_tolerance(&a, dec!(0.005)));

        // Outside tolerance
        assert!(!a.eq_with_tolerance(&b, dec!(0.003)));

        // Different currencies
        let c = Amount::new(dec!(100.00), "EUR");
        assert!(!a.eq_with_tolerance(&c, dec!(1.0)));

        // Exact match
        let d = Amount::new(dec!(100.00), "USD");
        assert!(a.eq_with_tolerance(&d, dec!(0.0)));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn test_eq_auto_tolerance() {
        // scale 2 (0.005 tolerance) vs scale 3 (0.0005 tolerance)
        let a = Amount::new(dec!(100.00), "USD");
        let b = Amount::new(dec!(100.004), "USD");

        // Uses max tolerance (0.005), difference is 0.004, so equal
        assert!(a.eq_auto_tolerance(&b));

        // scale 3 vs scale 3 -> tolerance 0.0005
        let c = Amount::new(dec!(100.000), "USD");
        let d = Amount::new(dec!(100.001), "USD");

        // Difference 0.001 > tolerance 0.0005, not equal
        assert!(!c.eq_auto_tolerance(&d));

        // scale 3 vs scale 3, small difference
        let e = Amount::new(dec!(100.0004), "USD");
        assert!(c.eq_auto_tolerance(&e)); // 0.0004 <= 0.0005

        // Different currencies
        let f = Amount::new(dec!(100.00), "EUR");
        assert!(!a.eq_auto_tolerance(&f));
    }
}
