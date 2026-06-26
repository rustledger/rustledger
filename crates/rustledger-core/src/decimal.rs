//! Arbitrary-(large-)precision decimal, backing the whole ledger's numbers.
//!
//! A thin newtype over [`fastnum::D512`] (a stack-allocated, `Copy`, 512-bit /
//! ~154-significant-digit decimal) that mirrors the slice of the
//! `crate::Decimal` API the codebase used, so the migration off
//! `rust_decimal` (issue #1240) is a drop-in for call sites. The point of the
//! switch is precision: `rust_decimal` capped at ~28 digits and rounded away
//! residuals Python's unbounded `Decimal` caught; `D512` does not.
//!
//! Differences from `rust_decimal` that callers must not rely on:
//! - fastnum has `NaN`/`±Infinity`; a valid ledger value never is one. The
//!   constructors/parsers here reject them, and `checked_*` returns `None`.
//! - `scale()` is clamped to `u32` (fastnum's is `i16` and can be negative).

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};
use core::str::FromStr;

use fastnum::D512;
use fastnum::decimal::{Context, RoundingMode};

/// Re-export so the [`crate::dec`] macro can reach fastnum's compile-time macro.
#[doc(hidden)]
pub use fastnum::dec512 as __dec512;

/// Context used for parsing/arithmetic: full D512 precision, no traps (so a bad
/// op yields a non-finite value we can detect rather than panicking). Rounding
/// only kicks in past 512-bit precision, far beyond any ledger value.
const CTX: Context = Context::default().without_traps();

/// Arbitrary-large-precision decimal. See module docs.
#[derive(Clone, Copy)]
pub struct Decimal(D512);

impl Decimal {
    pub const ZERO: Self = Self(D512::ZERO);
    pub const ONE: Self = Self(D512::ONE);
    pub const TWO: Self = Self(D512::TWO);
    pub const TEN: Self = Self(D512::TEN);
    pub const NEGATIVE_ONE: Self = Self(fastnum::dec512!(-1));
    pub const MAX: Self = Self(D512::MAX);
    pub const MIN: Self = Self(D512::MIN);

    /// Wrap a raw `D512` (used by the `dec!` macro). `const` so `dec!` works in
    /// const contexts like `rust_decimal`'s did.
    #[doc(hidden)]
    #[must_use]
    pub const fn from_d512(d: D512) -> Self {
        Self(d)
    }

    /// The raw backing value (escape hatch for fastnum-native math).
    #[must_use]
    pub const fn into_inner(self) -> D512 {
        self.0
    }

    /// `crate::Decimal::new(num, scale)` — `num * 10^-scale`.
    #[must_use]
    pub fn new(num: i64, scale: u32) -> Self {
        // Exact: build the scientific-notation string and parse it.
        Self::from_str(&format!("{num}e-{scale}")).unwrap_or(Self::ZERO)
    }

    /// Parse a decimal string (lenient — accepts scientific notation, like
    /// rust_decimal's inherent `from_str`). Inherent so `Decimal::from_str(s)`
    /// works without importing the `FromStr` trait.
    pub fn from_str(s: &str) -> Result<Self, DecimalParseError> {
        match D512::from_str(s, CTX) {
            Ok(d) if d.is_finite() => Ok(wrap(d)),
            _ => Err(DecimalParseError(s.to_string())),
        }
    }

    /// Smallest integer `>= self` (`rust_decimal::MathematicalOps::ceil`).
    #[must_use]
    pub fn ceil(self) -> Self {
        self.round_dp_with_mode(0, RoundingMode::Ceiling)
    }

    /// Largest integer `<= self` (`rust_decimal::MathematicalOps::floor`).
    #[must_use]
    pub fn floor(self) -> Self {
        self.round_dp_with_mode(0, RoundingMode::Floor)
    }

    /// `crate::Decimal::from_str_exact` — strict parse: plain decimals only,
    /// no scientific notation (matching rust_decimal, so ledger amount literals
    /// like `1e2` are rejected). `new()` uses the lenient `from_str` internally.
    pub fn from_str_exact(s: &str) -> Result<Self, DecimalParseError> {
        if s.contains(['e', 'E']) {
            return Err(DecimalParseError(s.to_string()));
        }
        Self::from_str(s)
    }

    /// 0 if non-finite (NaN/Inf never occur for valid ledger values).
    #[must_use]
    pub const fn scale(self) -> u32 {
        let f = self.0.fractional_digits_count();
        if f < 0 { 0 } else { f as u32 }
    }

    #[must_use]
    pub const fn is_zero(self) -> bool {
        self.0.is_zero()
    }

    #[must_use]
    pub const fn is_sign_negative(self) -> bool {
        self.0.is_sign_negative()
    }

    #[must_use]
    pub const fn is_sign_positive(self) -> bool {
        self.0.is_sign_positive()
    }

    /// `num_traits::Signed::is_positive` — strictly greater than zero (unlike
    /// `is_sign_positive`, which is also true for `+0`).
    #[must_use]
    pub fn is_positive(self) -> bool {
        !self.0.is_zero() && self.0.is_sign_positive()
    }

    /// `num_traits::Signed::is_negative` — strictly less than zero.
    #[must_use]
    pub fn is_negative(self) -> bool {
        !self.0.is_zero() && self.0.is_sign_negative()
    }

    /// Round to `dp` places with a rust_decimal-compatible strategy.
    #[must_use]
    pub fn round_dp_with_strategy(self, dp: u32, strategy: RoundingStrategy) -> Self {
        self.round_dp_with_mode(dp, strategy.mode())
    }

    /// Number of significant digits in the coefficient (0 for zero). Replaces
    /// counting `mantissa()` digits, which `i128` can't hold at high precision.
    #[must_use]
    pub fn significant_digits(self) -> u32 {
        if self.0.is_zero() {
            0
        } else {
            u32::try_from(self.0.digits_count()).unwrap_or(u32::MAX)
        }
    }

    /// `crate::Decimal::rescale` — set the scale in place to exactly
    /// `scale` fractional digits (pad or banker's-round).
    pub fn rescale(&mut self, scale: u32) {
        let s = i16::try_from(scale).unwrap_or(i16::MAX);
        *self = wrap(self.0.with_rounding_mode(RoundingMode::HalfEven).rescale(s));
    }

    /// `self^exp` for an unsigned integer exponent; `None` on overflow
    /// (`rust_decimal::MathematicalOps::checked_powu`).
    #[must_use]
    pub fn checked_powu(self, exp: u64) -> Option<Self> {
        let mut result = Self::ONE;
        for _ in 0..exp {
            result = result.checked_mul(self)?;
        }
        Some(result)
    }

    /// `self^exp` for a signed integer exponent (negative → reciprocal).
    /// `rust_decimal::MathematicalOps::powi`.
    #[must_use]
    pub fn powi(self, exp: i64) -> Self {
        if exp == 0 {
            return Self::ONE;
        }
        let mag = self.checked_powu(exp.unsigned_abs()).unwrap_or(Self::ZERO);
        if exp < 0 {
            Self::ONE.checked_div(mag).unwrap_or(Self::ZERO)
        } else {
            mag
        }
    }

    #[must_use]
    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    #[must_use]
    pub fn signum(self) -> Self {
        if self.0.is_zero() {
            Self::ZERO
        } else if self.0.is_sign_negative() {
            Self::NEGATIVE_ONE
        } else {
            Self::ONE
        }
    }

    /// Remove trailing zeros (`1.500` → `1.5`).
    #[must_use]
    pub fn normalize(self) -> Self {
        Self(self.0.reduce())
    }

    #[must_use]
    pub fn trunc(self) -> Self {
        Self(self.0.trunc())
    }

    #[must_use]
    pub fn fract(self) -> Self {
        Self(self.0 - self.0.trunc())
    }

    /// Round to `dp` decimal places, banker's rounding (matches
    /// `rust_decimal`'s default `round_dp`).
    #[must_use]
    pub fn round_dp(self, dp: u32) -> Self {
        self.round_dp_with_mode(dp, RoundingMode::HalfEven)
    }

    #[must_use]
    pub fn round_dp_with_mode(self, dp: u32, mode: RoundingMode) -> Self {
        // Match rust_decimal: round *down* to `dp` places but never pad. A value
        // already within `dp` fractional digits is returned unchanged (so 2.5
        // round_dp(2) stays "2.5", not "2.50"); only over-precise values are
        // rescaled. `rescale`'s rounding mode comes from the attached context.
        if self.scale() <= dp {
            return self;
        }
        let scaled = self.0.with_rounding_mode(mode);
        wrap(scaled.rescale(i16::try_from(dp).unwrap_or(i16::MAX)))
    }

    /// Round to a whole number, banker's rounding (`rust_decimal::round`).
    #[must_use]
    pub fn round(self) -> Self {
        self.round_dp(0)
    }

    #[must_use]
    pub fn checked_add(self, other: Self) -> Option<Self> {
        finite(self.0.add(other.0))
    }

    #[must_use]
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        finite(self.0.sub(other.0))
    }

    #[must_use]
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        finite(self.0.mul(other.0))
    }

    #[must_use]
    pub fn checked_div(self, other: Self) -> Option<Self> {
        if other.0.is_zero() {
            return None;
        }
        finite(self.0.div(other.0))
    }

    #[must_use]
    pub fn to_i64(self) -> Option<i64> {
        self.0.trunc().to_i64().ok()
    }

    #[must_use]
    pub fn to_u32(self) -> Option<u32> {
        self.0.trunc().to_u32().ok()
    }

    #[must_use]
    pub fn to_i128(self) -> Option<i128> {
        self.0.trunc().to_i128().ok()
    }

    /// `rust_decimal::Decimal::from_i128_with_scale` — `num * 10^-scale`.
    #[must_use]
    pub fn from_i128_with_scale(num: i128, scale: u32) -> Self {
        Self::from_str(&format!("{num}e-{scale}")).unwrap_or(Self::ZERO)
    }

    /// `self % other`; `None` when `other` is zero.
    #[must_use]
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        if other.0.is_zero() {
            return None;
        }
        finite(self.0.rem(other.0))
    }

    /// Truncate toward zero and convert to `i32` (`None` if out of range).
    #[must_use]
    pub fn to_i32(self) -> Option<i32> {
        self.to_i128().and_then(|v| i32::try_from(v).ok())
    }
    /// Truncate toward zero and convert to `i16`.
    #[must_use]
    pub fn to_i16(self) -> Option<i16> {
        self.to_i128().and_then(|v| i16::try_from(v).ok())
    }
    /// Truncate toward zero and convert to `i8`.
    #[must_use]
    pub fn to_i8(self) -> Option<i8> {
        self.to_i128().and_then(|v| i8::try_from(v).ok())
    }
    /// Truncate toward zero and convert to `isize`.
    #[must_use]
    pub fn to_isize(self) -> Option<isize> {
        self.to_i128().and_then(|v| isize::try_from(v).ok())
    }
    /// Truncate toward zero and convert to `u64`.
    #[must_use]
    pub fn to_u64(self) -> Option<u64> {
        self.to_i128().and_then(|v| u64::try_from(v).ok())
    }
    /// Truncate toward zero and convert to `u16`.
    #[must_use]
    pub fn to_u16(self) -> Option<u16> {
        self.to_i128().and_then(|v| u16::try_from(v).ok())
    }
    /// Truncate toward zero and convert to `u8`.
    #[must_use]
    pub fn to_u8(self) -> Option<u8> {
        self.to_i128().and_then(|v| u8::try_from(v).ok())
    }
    /// Truncate toward zero and convert to `usize`.
    #[must_use]
    pub fn to_usize(self) -> Option<usize> {
        self.to_i128().and_then(|v| usize::try_from(v).ok())
    }

    #[must_use]
    pub fn to_f64(self) -> Option<f64> {
        let f = self.0.to_f64();
        f.is_finite().then_some(f)
    }

    /// `crate::Decimal::from_f64` — exact-ish from a float, `None` on
    /// non-finite input.
    #[must_use]
    pub fn from_f64(f: f64) -> Option<Self> {
        if !f.is_finite() {
            return None;
        }
        // Route through the shortest round-trippable decimal string.
        Self::from_str(&format!("{f}")).ok()
    }
}

/// `Some` iff the value is finite (not NaN / ±Inf), wrapped.
fn finite(d: D512) -> Option<Decimal> {
    d.is_finite().then_some(wrap(d))
}

/// Canonicalize a raw result. fastnum can yield `-0` (e.g. `0 * -1` or
/// `-0.0`); `rust_decimal` has no signed zero, so map `-0` → `+0` (preserving
/// scale via `abs`).
#[inline]
fn wrap(d: D512) -> Decimal {
    Decimal(if d.is_zero() { d.abs() } else { d })
}

/// rust_decimal-compatible rounding strategies (mapped to fastnum modes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundingStrategy {
    MidpointNearestEven,
    MidpointAwayFromZero,
    MidpointTowardZero,
    ToZero,
    AwayFromZero,
    ToNegativeInfinity,
    ToPositiveInfinity,
}

impl RoundingStrategy {
    const fn mode(self) -> RoundingMode {
        match self {
            Self::MidpointNearestEven => RoundingMode::HalfEven,
            Self::MidpointAwayFromZero => RoundingMode::HalfUp,
            Self::MidpointTowardZero => RoundingMode::HalfDown,
            Self::ToZero => RoundingMode::Down,
            Self::AwayFromZero => RoundingMode::Up,
            Self::ToNegativeInfinity => RoundingMode::Floor,
            Self::ToPositiveInfinity => RoundingMode::Ceiling,
        }
    }
}

// ---- equality / ordering / hashing (delegate to D512) ----------------------

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for Decimal {}

impl PartialOrd for Decimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Decimal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl Hash for Decimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the normalized form so 1.0 and 1.00 (equal) hash equal.
        self.0.reduce().hash(state);
    }
}

impl Default for Decimal {
    fn default() -> Self {
        Self::ZERO
    }
}

// ---- formatting / parsing --------------------------------------------------

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Canonicalize signed zero on the way out (`dec!(-0.0)` is built via the
        // const `from_d512`, which can't run the `wrap` check) — display `-0` as
        // `0`, preserving scale. rust_decimal has no signed zero.
        if self.0.is_zero() {
            fmt::Display::fmt(&self.0.abs(), f)
        } else {
            fmt::Display::fmt(&self.0, f)
        }
    }
}
impl fmt::Debug for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Match rust_decimal's Debug, which prints the value plainly.
        fmt::Display::fmt(&self.0, f)
    }
}
impl fmt::LowerExp for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerExp::fmt(&self.0, f)
    }
}
impl fmt::UpperExp for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperExp::fmt(&self.0, f)
    }
}

/// Parse error — opaque, mirrors how callers used `rust_decimal::Error`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecimalParseError(String);

impl fmt::Display for DecimalParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid decimal: {}", self.0)
    }
}
impl std::error::Error for DecimalParseError {}

impl FromStr for Decimal {
    type Err = DecimalParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Decimal::from_str(s)
    }
}

// ---- integer conversions ---------------------------------------------------

macro_rules! from_int {
    ($($t:ty),*) => {$(
        impl From<$t> for Decimal {
            fn from(v: $t) -> Self {
                wrap(D512::from(v))
            }
        }
    )*};
}
from_int!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);

// ---- arithmetic (delegate to D512) -----------------------------------------

macro_rules! bin_op {
    ($trait:ident, $method:ident, $assign:ident, $assign_method:ident) => {
        impl $trait for Decimal {
            type Output = Self;
            fn $method(self, rhs: Self) -> Self {
                wrap(self.0.$method(rhs.0))
            }
        }
        impl $assign for Decimal {
            fn $assign_method(&mut self, rhs: Self) {
                *self = wrap(self.0.$method(rhs.0));
            }
        }
        // Reference operands (rust_decimal had these; `Decimal` is `Copy`).
        impl $trait<&Decimal> for Decimal {
            type Output = Self;
            fn $method(self, rhs: &Self) -> Self {
                self.$method(*rhs)
            }
        }
        impl $trait<Decimal> for &Decimal {
            type Output = Decimal;
            fn $method(self, rhs: Decimal) -> Decimal {
                (*self).$method(rhs)
            }
        }
        impl $trait<&Decimal> for &Decimal {
            type Output = Decimal;
            fn $method(self, rhs: &Decimal) -> Decimal {
                (*self).$method(*rhs)
            }
        }
        impl $assign<&Decimal> for Decimal {
            fn $assign_method(&mut self, rhs: &Self) {
                *self = wrap(self.0.$method(rhs.0));
            }
        }
    };
}
bin_op!(Add, add, AddAssign, add_assign);
bin_op!(Sub, sub, SubAssign, sub_assign);
bin_op!(Mul, mul, MulAssign, mul_assign);
bin_op!(Div, div, DivAssign, div_assign);

impl Rem for Decimal {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        wrap(self.0.rem(rhs.0))
    }
}
impl Neg for Decimal {
    type Output = Self;
    fn neg(self) -> Self {
        wrap(self.0.neg())
    }
}
impl Neg for &Decimal {
    type Output = Decimal;
    fn neg(self) -> Decimal {
        wrap(self.0.neg())
    }
}

impl Sum for Decimal {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |a, b| a + b)
    }
}
impl<'a> Sum<&'a Decimal> for Decimal {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |a, b| a + *b)
    }
}
impl Product for Decimal {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |a, b| a * b)
    }
}

// ---- serde: always a decimal string, matching the prior wire format --------

impl serde::Serialize for Decimal {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.0.to_string())
    }
}
impl<'de> serde::Deserialize<'de> for Decimal {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        Self::from_str(&s).map_err(serde::de::Error::custom)
    }
}

/// `dec!(...)` — compile-time decimal literal, like `crate::dec!`.
#[macro_export]
macro_rules! dec {
    ($($t:tt)*) => {
        $crate::Decimal::from_d512($crate::decimal::__dec512!($($t)*))
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Decimal as Rd;
    use std::str::FromStr as _;

    /// Cross-check a value+op against rust_decimal for parity.
    fn rd(s: &str) -> Rd {
        Rd::from_str(s).unwrap()
    }
    fn fd(s: &str) -> Decimal {
        Decimal::from_str(s).unwrap()
    }

    #[test]
    fn parity_with_rust_decimal() {
        // Exact ops (add/sub/mul) on values well within rust_decimal's range
        // must agree digit-for-digit after normalization.
        let cases = [
            "0",
            "1",
            "-1",
            "123.45",
            "0.1",
            "1000.000001",
            "-99.9",
            "2.5",
            "3.14159",
        ];
        for a in cases {
            for b in cases {
                assert_eq!(
                    (fd(a) + fd(b)).normalize().to_string(),
                    (rd(a) + rd(b)).normalize().to_string(),
                    "add {a}+{b}"
                );
                assert_eq!(
                    (fd(a) - fd(b)).normalize().to_string(),
                    (rd(a) - rd(b)).normalize().to_string(),
                    "sub {a}-{b}"
                );
                assert_eq!(
                    (fd(a) * fd(b)).normalize().to_string(),
                    (rd(a) * rd(b)).normalize().to_string(),
                    "mul {a}*{b}"
                );
            }
        }
    }

    #[test]
    fn new_and_scale() {
        assert_eq!(Decimal::new(12345, 2).to_string(), "123.45");
        assert_eq!(Decimal::new(5, 3).to_string(), "0.005");
        assert_eq!(fd("123.45").scale(), 2);
        assert_eq!(fd("100").scale(), 0);
    }

    #[test]
    fn round_dp_banker() {
        // half-even: 2.5 -> 2, 3.5 -> 4, 1.235 -> 1.24, 1.245 -> 1.24
        assert_eq!(fd("2.5").round().to_string(), "2");
        assert_eq!(fd("3.5").round().to_string(), "4");
        assert_eq!(fd("1.23456").round_dp(2).to_string(), "1.23");
        assert_eq!(fd("1.235").round_dp(2).to_string(), "1.24");
        // cross-check vs rust_decimal round_dp default (banker's); both pad to
        // exactly 2 dp, so compare un-normalized.
        for s in ["1.23456", "2.5", "0.005", "9.999", "-1.235"] {
            assert_eq!(
                fd(s).round_dp(2).to_string(),
                rd(s).round_dp(2).to_string(),
                "round_dp {s}"
            );
        }
    }

    #[test]
    fn normalize_and_misc() {
        assert_eq!(fd("1.500").normalize().to_string(), "1.5");
        assert_eq!(fd("-5").abs(), fd("5"));
        assert!(Decimal::ZERO.is_zero());
        assert!(fd("-1").is_sign_negative());
        assert_eq!(fd("7.9").trunc().to_string(), "7");
        assert_eq!(Decimal::from(42i64).to_i64(), Some(42));
        assert_eq!(fd("3.5").to_i64(), Some(3)); // truncates toward zero, like rust_decimal
    }

    #[test]
    fn precision_beats_rust_decimal() {
        // the #1240 fixture's failure mode: a residual below 28 digits.
        let one = Decimal::ONE;
        let tiny = fd("0.0000000000000000000000002"); // 2e-25
        assert_ne!(one + tiny, one, "must keep a 2e-25 residual");
        assert!(tiny > Decimal::ZERO);
    }

    #[test]
    fn checked_and_serde() {
        assert_eq!(fd("1").checked_div(Decimal::ZERO), None);
        assert_eq!(fd("6").checked_div(fd("3")), Some(fd("2")));
        // serde round-trips as a string
        let v = fd("12345.6789");
        let j = serde_json::to_string(&v).unwrap();
        assert_eq!(j, "\"12345.6789\"");
        assert_eq!(serde_json::from_str::<Decimal>(&j).unwrap(), v);
    }

    #[test]
    fn ord_and_eq() {
        assert!(fd("1.5") < fd("1.50001"));
        assert_eq!(fd("1.0"), fd("1.00")); // value equality regardless of scale
        let mut v = [fd("3"), fd("-1"), fd("2.5")];
        v.sort();
        assert_eq!(v, [fd("-1"), fd("2.5"), fd("3")]);
    }
}
