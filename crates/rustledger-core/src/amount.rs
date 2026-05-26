//! Amount type representing a decimal number with a currency.
//!
//! An [`Amount`] is the fundamental unit of value in Beancount, combining a decimal
//! number with a currency code. It supports arithmetic operations and tolerance-based
//! comparison for balance checking.

use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::{Add, AddAssign, Neg, Sub, SubAssign};

use crate::Currency;
#[cfg(feature = "rkyv")]
use crate::intern::AsDecimal;

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
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct Amount {
    /// The decimal quantity
    #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
    pub number: Decimal,
    /// The currency code (e.g., "USD", "EUR", "AAPL")
    pub currency: Currency,
}

impl Amount {
    /// Create a new amount.
    #[must_use]
    pub fn new(number: Decimal, currency: impl Into<Currency>) -> Self {
        Self {
            number,
            currency: currency.into(),
        }
    }

    /// Create a zero amount with the given currency.
    #[must_use]
    pub fn zero(currency: impl Into<Currency>) -> Self {
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

/// Error produced by the [`FromStr`](std::str::FromStr) impl on
/// [`Amount`] when the input doesn't match the `<number> <currency>`
/// shape that [`fmt::Display`] emits.
///
/// Carries the offending input so callers can surface an actionable
/// message ("you wrote X, expected Y") rather than a generic parse
/// failure. The wire format is strict on purpose: see the `FromStr`
/// docstring for the supported shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AmountParseError {
    /// The original input string the caller passed.
    pub input: String,
    /// Why the parse failed (caller-displayable, no internal jargon).
    pub reason: AmountParseErrorReason,
}

/// Distinguishes the failure modes of [`Amount`]'s
/// [`FromStr`](std::str::FromStr) impl.
///
/// Separate from [`AmountParseError`] so callers can match on the
/// category (e.g. for distinct error codes) without parsing the
/// message string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AmountParseErrorReason {
    /// Input had fewer or more than 2 whitespace-separated tokens.
    NotTwoTokens,
    /// The number token didn't parse as a [`Decimal`] (carries the
    /// offending token, not the full input).
    InvalidNumber(String),
    /// The currency token isn't a valid beancount commodity (must be
    /// uppercase ASCII letters, digits, `'`, `.`, `_`, `-`, starting
    /// with an uppercase letter; max 24 chars).
    InvalidCurrency(String),
}

impl fmt::Display for AmountParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.reason {
            AmountParseErrorReason::NotTwoTokens => write!(
                f,
                "invalid amount literal {:?}: expected `<number> <currency>` (e.g. \"100 USD\")",
                self.input,
            ),
            AmountParseErrorReason::InvalidNumber(tok) => write!(
                f,
                "invalid amount literal {:?}: {:?} doesn't parse as a decimal number",
                self.input, tok,
            ),
            AmountParseErrorReason::InvalidCurrency(tok) => write!(
                f,
                "invalid amount literal {:?}: {:?} isn't a valid commodity \
                 (uppercase ASCII, may contain digits/'./_/-, max 24 chars)",
                self.input, tok,
            ),
        }
    }
}

impl std::error::Error for AmountParseError {}

impl std::str::FromStr for Amount {
    type Err = AmountParseError;

    /// Parse `<number> <currency>` — the exact shape produced by
    /// [`fmt::Display`]. Round-trip is lossless:
    /// `Amount::from_str(&amt.to_string()) == Ok(amt)`.
    ///
    /// Strict by design — there is intentionally no Python beancount
    /// equivalent of this parser, so we set the wire contract. Accepts:
    /// - Any whitespace (one or more spaces/tabs) between the number
    ///   and currency.
    /// - Leading or trailing whitespace around the whole string.
    /// - Negative numbers (`-100 USD`).
    /// - Fractional decimals (`100.50 USD`).
    ///
    /// Rejects (typed error rather than silent fallback):
    /// - Currency-first form (`"USD 100"`).
    /// - Number-only (`"100"`) or currency-only (`"USD"`).
    /// - Scientific notation (`"1e2 USD"`).
    /// - Thousands separators (`"1,000 USD"`).
    /// - Lowercase commodity (`"100 usd"`).
    /// - Empty / whitespace-only strings.
    ///
    /// # Errors
    ///
    /// Returns [`AmountParseError`] describing which axis of the
    /// expected shape was violated; see [`AmountParseErrorReason`].
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut iter = s.split_whitespace();
        let (Some(num_tok), Some(cur_tok), None) = (iter.next(), iter.next(), iter.next()) else {
            return Err(AmountParseError {
                input: s.to_string(),
                reason: AmountParseErrorReason::NotTwoTokens,
            });
        };

        // `from_str_exact` rejects scientific notation, thousands
        // separators, embedded whitespace — exactly what we want for
        // strict parsing.
        let number = Decimal::from_str_exact(num_tok).map_err(|_| AmountParseError {
            input: s.to_string(),
            reason: AmountParseErrorReason::InvalidNumber(num_tok.to_string()),
        })?;

        if !is_valid_commodity(cur_tok) {
            return Err(AmountParseError {
                input: s.to_string(),
                reason: AmountParseErrorReason::InvalidCurrency(cur_tok.to_string()),
            });
        }

        Ok(Self::new(number, cur_tok))
    }
}

/// Beancount commodity validation: uppercase letter first, then
/// uppercase letters, digits, `'`, `.`, `_`, or `-`. 1–24 chars.
///
/// Matches the parser's commodity-token rule (see
/// `rustledger-parser::lexer`). Kept inline here rather than reaching
/// into the parser to avoid a `rustledger-core → rustledger-parser`
/// dep cycle (parser already depends on core).
fn is_valid_commodity(s: &str) -> bool {
    if s.is_empty() || s.len() > 24 {
        return false;
    }
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !first.is_ascii_uppercase() {
        return false;
    }
    chars.all(|c| {
        c.is_ascii_uppercase() || c.is_ascii_digit() || matches!(c, '\'' | '.' | '_' | '-')
    })
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
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub enum IncompleteAmount {
    /// Complete amount with both number and currency
    Complete(Amount),
    /// Only number specified, currency to be inferred from context (cost, price, or other postings)
    NumberOnly(#[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))] Decimal),
    /// Only currency specified, number to be interpolated to balance the transaction
    CurrencyOnly(Currency),
}

impl IncompleteAmount {
    /// Create a complete amount.
    #[must_use]
    pub fn complete(number: Decimal, currency: impl Into<Currency>) -> Self {
        Self::Complete(Amount::new(number, currency))
    }

    /// Create a number-only incomplete amount.
    #[must_use]
    pub const fn number_only(number: Decimal) -> Self {
        Self::NumberOnly(number)
    }

    /// Create a currency-only incomplete amount.
    #[must_use]
    pub fn currency_only(currency: impl Into<Currency>) -> Self {
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

    // ===== FromStr tests (#1179) =====

    use std::str::FromStr;

    #[test]
    fn amount_from_str_round_trips_display() {
        // Load-bearing invariant: `from_str(&amt.to_string()) == Ok(amt)`.
        // If `Display` or `FromStr` ever drifts apart, this catches it
        // before silent breakage. Cover positive, negative, fractional,
        // zero, and large magnitudes.
        for amt in [
            Amount::new(dec!(100), "USD"),
            Amount::new(dec!(-50.25), "EUR"),
            Amount::new(dec!(0), "GBP"),
            Amount::new(dec!(1234567.89), "JPY"),
            Amount::new(dec!(0.0001), "USD"),
        ] {
            let displayed = amt.to_string();
            assert_eq!(
                Amount::from_str(&displayed),
                Ok(amt.clone()),
                "round-trip lost data: Display produced {displayed:?}"
            );
        }
    }

    #[test]
    fn amount_from_str_accepts_canonical_forms() {
        assert_eq!(
            Amount::from_str("100 USD"),
            Ok(Amount::new(dec!(100), "USD"))
        );
        assert_eq!(
            Amount::from_str("-50.25 EUR"),
            Ok(Amount::new(dec!(-50.25), "EUR"))
        );
        // Extra whitespace around tokens is fine — we use
        // split_whitespace, which collapses runs of spaces/tabs.
        assert_eq!(
            Amount::from_str("  100   USD  "),
            Ok(Amount::new(dec!(100), "USD"))
        );
        // Single character commodity is legal.
        assert_eq!(Amount::from_str("1 X"), Ok(Amount::new(dec!(1), "X")));
        // Commodity with allowed special chars (`'`, `.`, `_`, `-`,
        // digits after the first character).
        assert_eq!(
            Amount::from_str("100 RY-2024"),
            Ok(Amount::new(dec!(100), "RY-2024"))
        );
    }

    #[test]
    fn amount_from_str_rejects_currency_first() {
        // `"USD 100"` looks like a unit-only form to humans but isn't
        // what Display emits. Reject so users don't get silent wrong
        // results — `USD` would parse as the number token and fail at
        // `Decimal::from_str_exact`.
        let err = Amount::from_str("USD 100").expect_err("currency-first must reject");
        assert!(matches!(
            err.reason,
            AmountParseErrorReason::InvalidNumber(_)
        ));
    }

    #[test]
    fn amount_from_str_rejects_single_token() {
        for s in ["", "  ", "100", "USD"] {
            let err = Amount::from_str(s).expect_err("single token must reject");
            assert!(
                matches!(err.reason, AmountParseErrorReason::NotTwoTokens),
                "expected NotTwoTokens for {s:?}, got {:?}",
                err.reason
            );
        }
    }

    #[test]
    fn amount_from_str_rejects_extra_tokens() {
        let err = Amount::from_str("100 USD extra").expect_err("trailing token must reject");
        assert!(matches!(err.reason, AmountParseErrorReason::NotTwoTokens));
    }

    #[test]
    fn amount_from_str_rejects_scientific_notation() {
        // `Decimal::from_str_exact` rejects `1e2` — we want that strict
        // behavior here so `CONVERT('1e2 USD', 'EUR')` fails loudly
        // rather than parsing incorrectly or coercing.
        let err = Amount::from_str("1e2 USD").expect_err("scientific must reject");
        assert!(matches!(
            err.reason,
            AmountParseErrorReason::InvalidNumber(_)
        ));
    }

    #[test]
    fn amount_from_str_rejects_thousands_separator() {
        let err = Amount::from_str("1,000 USD").expect_err("thousands sep must reject");
        assert!(matches!(
            err.reason,
            AmountParseErrorReason::InvalidNumber(_)
        ));
    }

    #[test]
    fn amount_from_str_rejects_lowercase_currency() {
        let err = Amount::from_str("100 usd").expect_err("lowercase commodity must reject");
        assert!(matches!(
            err.reason,
            AmountParseErrorReason::InvalidCurrency(_)
        ));
    }

    #[test]
    fn amount_from_str_rejects_currency_starting_with_digit() {
        // Beancount commodities must start with an uppercase letter.
        let err = Amount::from_str("100 1USD").expect_err("digit-first commodity must reject");
        assert!(matches!(
            err.reason,
            AmountParseErrorReason::InvalidCurrency(_)
        ));
    }

    #[test]
    fn amount_from_str_error_message_names_input() {
        // Plugin/BQL callers surface this Display to users; it must
        // name what they wrote so they can fix it without guessing.
        let err = Amount::from_str("oopsie daisy").unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("oopsie daisy"), "error must echo input: {msg}");
        assert!(msg.contains("doesn't parse"), "error must explain: {msg}");
    }
}
