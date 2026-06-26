//! Hybrid decimal: fast 28-digit path with an arbitrary-precision fallback.
//!
//! `Decimal` is a `Copy` newtype over an enum:
//! - `Small(rust_decimal::Decimal)` — 16 bytes, the fast common case (money at a
//!   handful of decimal places). All hot arithmetic stays here.
//! - `Big(fastnum::D256)` — ~77 significant digits, used only when an operation
//!   would exceed `rust_decimal`'s 28-digit precision (the residual case #1240
//!   needs: Python keeps digits `rust_decimal` rounds away).
//!
//! This preserves `rust_decimal`'s speed for everyday ledgers while matching
//! Python's unbounded precision where it actually matters. The numeric results
//! are identical to a pure-`D256` implementation: add/sub/mul take the
//! `rust_decimal` path *only when the exact result fits in 28 digits* (so no
//! rounding happens either way), and fall back to `D256` otherwise.
//!
//! Invariant: `Big` never holds a value representable exactly in `rust_decimal`
//! — every `Big`-producing path runs [`demote`]. So a given numeric value has
//! exactly one representation, which keeps `Eq`/`Ord`/`Hash` consistent and lets
//! same-variant `Small` comparisons use the fast path.
//!
//! Differences from `rust_decimal` callers must not rely on: `Big` values carry
//! more than 28 digits; `D256` has `NaN`/`±Inf` (constructors reject them,
//! `checked_*` returns `None`); `scale()` is clamped to `u32`.

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};
use core::str::FromStr;

use fastnum::D256;
use fastnum::decimal::{Context, RoundingMode};
use rust_decimal::Decimal as Rd;
use rust_decimal::prelude::ToPrimitive;

/// Re-export so the [`crate::dec`] macro can reach fastnum's compile-time macro.
#[doc(hidden)]
pub use fastnum::dec256 as __dec256;
/// `dec!` literals always fit rust_decimal (≤28 digits), so they go through its
/// compile-time macro — `const`, `Small`, zero runtime cost (no demote).
#[doc(hidden)]
pub use rust_decimal_macros::dec as __rd_dec;

/// Wrap a compile-time rust_decimal literal as a `Small` decimal (`const`).
#[doc(hidden)]
#[must_use]
pub const fn from_small_const(rd: Rd) -> Decimal {
    small(rd)
}

/// Context for `D256` parse/arithmetic: full precision, no traps (a bad op
/// yields a detectable non-finite value rather than panicking).
const CTX: Context = Context::default().without_traps();

/// `rust_decimal`'s maximum significant digits. Above this it rounds, so any
/// exact result needing more must use the `Big` path.
const RD_MAX_DIGITS: u32 = 28;

/// Hybrid decimal. See module docs.
#[derive(Clone, Copy)]
pub struct Decimal(Repr);

#[derive(Clone, Copy)]
enum Repr {
    Small(Rd),
    Big(D256),
}

// ---- representation helpers ------------------------------------------------

/// Significant-digit count of a `rust_decimal` mantissa.
#[inline]
fn sig_digits(mantissa: i128) -> u32 {
    if mantissa == 0 {
        0
    } else {
        mantissa.unsigned_abs().ilog10() + 1
    }
}

/// Integer-side digit count of a small value (0 for `|x| < 1`).
#[inline]
fn int_digits(x: Rd) -> u32 {
    sig_digits(x.mantissa()).saturating_sub(x.scale())
}

/// Widen any representation to `D256` (exact). Cheap for `Big`; a string parse
/// for `Small` (only hit on the rare fallback path or cross-variant compare).
#[inline]
fn to_big(r: Repr) -> D256 {
    match r {
        Repr::Small(rd) => D256::from_str(&rd.to_string(), CTX).unwrap_or(D256::ZERO),
        Repr::Big(d) => d,
    }
}

/// Build a `Decimal` from a `D256`, demoting to `Small` when it fits in
/// `rust_decimal` exactly. Canonicalizes signed zero (`-0` → `+0`). This is the
/// single choke point that maintains the `Big`-never-holds-a-small invariant.
#[inline]
fn demote(d: D256) -> Decimal {
    if !d.is_finite() {
        return Decimal(Repr::Big(d));
    }
    let d = if d.is_zero() { d.abs() } else { d }; // drop signed zero
    // Quick reject: clearly beyond rust_decimal (too many digits or a scale it
    // can't hold). Avoids the string round-trip for genuinely-big values.
    let frac = d.fractional_digits_count();
    if (0..=RD_MAX_DIGITS as i16).contains(&frac) && d.digits_count() <= RD_MAX_DIGITS as usize {
        // Candidate fits; confirm the conversion is lossless via a numeric
        // round-trip (guards magnitude / formatting corner cases).
        if let Ok(rd) = Rd::from_str(&d.to_string()) {
            if D256::from_str(&rd.to_string(), CTX).is_ok_and(|b| b == d) {
                return Decimal(Repr::Small(rd));
            }
        }
    }
    Decimal(Repr::Big(d))
}

/// Construct directly from a known-small value (no demote needed).
#[inline]
const fn small(rd: Rd) -> Decimal {
    Decimal(Repr::Small(rd))
}

// ---- core arithmetic (fast path + fallback) --------------------------------

/// `a + b`. Fast path when the exact sum fits in 28 digits.
#[inline]
fn add_core(a: Repr, b: Repr) -> Decimal {
    if let (Repr::Small(x), Repr::Small(y)) = (a, b) {
        // Exact iff result digits ≤ 28: scale stays max(sx,sy); integer side
        // grows by at most one (carry).
        if x.scale().max(y.scale()) + int_digits(x).max(int_digits(y)) + 1 <= RD_MAX_DIGITS {
            if let Some(r) = x.checked_add(y) {
                return small(r);
            }
        }
    }
    demote(to_big(a) + to_big(b))
}

#[inline]
fn sub_core(a: Repr, b: Repr) -> Decimal {
    if let (Repr::Small(x), Repr::Small(y)) = (a, b) {
        if x.scale().max(y.scale()) + int_digits(x).max(int_digits(y)) + 1 <= RD_MAX_DIGITS {
            if let Some(r) = x.checked_sub(y) {
                return small(r);
            }
        }
    }
    demote(to_big(a) - to_big(b))
}

#[inline]
fn mul_core(a: Repr, b: Repr) -> Decimal {
    if let (Repr::Small(x), Repr::Small(y)) = (a, b) {
        // Exact iff the product's digit count (≈ dx+dy) and scale (sx+sy) both
        // stay within rust_decimal.
        if sig_digits(x.mantissa()) + sig_digits(y.mantissa()) <= RD_MAX_DIGITS
            && x.scale() + y.scale() <= RD_MAX_DIGITS
        {
            if let Some(r) = x.checked_mul(y) {
                return small(r);
            }
        }
    }
    demote(to_big(a) * to_big(b))
}

/// Division always uses `D256` so the result is identical to the
/// arbitrary-precision implementation (rust_decimal and D256 round
/// non-terminating quotients differently). Division is rare on ledger hot paths.
#[inline]
fn div_core(a: Repr, b: Repr) -> Decimal {
    demote(to_big(a) / to_big(b))
}

#[inline]
fn rem_core(a: Repr, b: Repr) -> Decimal {
    demote(to_big(a) % to_big(b))
}

impl Decimal {
    pub const ZERO: Self = small(Rd::ZERO);
    pub const ONE: Self = small(Rd::ONE);
    pub const TWO: Self = small(Rd::TWO);
    pub const TEN: Self = small(Rd::TEN);
    pub const NEGATIVE_ONE: Self = small(Rd::NEGATIVE_ONE);
    // Genuinely beyond rust_decimal's range, so they live in `Big`.
    pub const MAX: Self = Decimal(Repr::Big(D256::MAX));
    pub const MIN: Self = Decimal(Repr::Big(D256::MIN));

    /// Wrap a raw `D256` (used by the `dec!` macro), demoting to `Small` when it
    /// fits. Not `const` (demotion runs a fits check) — no const callers exist.
    #[doc(hidden)]
    #[must_use]
    pub fn from_d512(d: D256) -> Self {
        demote(d)
    }

    /// The value as a `D256` (escape hatch / wire + cache encoding).
    #[must_use]
    pub fn into_inner(self) -> D256 {
        to_big(self.0)
    }

    /// `crate::Decimal::new(num, scale)` — `num * 10^-scale`.
    #[must_use]
    pub fn new(num: i64, scale: u32) -> Self {
        Self::from_i128_with_scale(i128::from(num), scale)
    }

    /// Parse a decimal string (lenient — accepts scientific notation, like
    /// rust_decimal's inherent `from_str`).
    pub fn from_str(s: &str) -> Result<Self, DecimalParseError> {
        // Try rust_decimal first (fast, covers the common case exactly). Fall
        // back to D256 for inputs it can't hold without rounding.
        match D256::from_str(s, CTX) {
            Ok(d) if d.is_finite() => Ok(demote(d)),
            _ => Err(DecimalParseError(s.to_string())),
        }
    }

    /// `crate::Decimal::from_str_exact` — strict: rejects scientific notation.
    pub fn from_str_exact(s: &str) -> Result<Self, DecimalParseError> {
        if s.contains(['e', 'E']) {
            return Err(DecimalParseError(s.to_string()));
        }
        Self::from_str(s)
    }

    /// Smallest integer `>= self`.
    #[must_use]
    pub fn ceil(self) -> Self {
        self.round_dp_with_mode(0, RoundingMode::Ceiling)
    }

    /// Largest integer `<= self`.
    #[must_use]
    pub fn floor(self) -> Self {
        self.round_dp_with_mode(0, RoundingMode::Floor)
    }

    /// Fractional digit count (0 if non-finite).
    #[must_use]
    pub fn scale(self) -> u32 {
        match self.0 {
            Repr::Small(rd) => rd.scale(),
            Repr::Big(d) => {
                let f = d.fractional_digits_count();
                if f < 0 { 0 } else { f as u32 }
            }
        }
    }

    #[must_use]
    pub fn is_zero(self) -> bool {
        match self.0 {
            Repr::Small(rd) => rd.is_zero(),
            Repr::Big(d) => d.is_zero(),
        }
    }

    #[must_use]
    pub fn is_sign_negative(self) -> bool {
        match self.0 {
            Repr::Small(rd) => rd.is_sign_negative(),
            Repr::Big(d) => d.is_sign_negative(),
        }
    }

    #[must_use]
    pub fn is_sign_positive(self) -> bool {
        match self.0 {
            Repr::Small(rd) => rd.is_sign_positive(),
            Repr::Big(d) => d.is_sign_positive(),
        }
    }

    /// Strictly greater than zero (`num_traits::Signed::is_positive`).
    #[must_use]
    pub fn is_positive(self) -> bool {
        !self.is_zero() && self.is_sign_positive()
    }

    /// Strictly less than zero.
    #[must_use]
    pub fn is_negative(self) -> bool {
        !self.is_zero() && self.is_sign_negative()
    }

    /// Round to `dp` places with a rust_decimal-compatible strategy.
    #[must_use]
    pub fn round_dp_with_strategy(self, dp: u32, strategy: RoundingStrategy) -> Self {
        self.round_dp_with_mode(dp, strategy.mode())
    }

    /// Number of significant digits in the coefficient (0 for zero).
    #[must_use]
    pub fn significant_digits(self) -> u32 {
        match self.0 {
            Repr::Small(rd) => sig_digits(rd.mantissa()),
            Repr::Big(d) => {
                if d.is_zero() {
                    0
                } else {
                    u32::try_from(d.digits_count()).unwrap_or(u32::MAX)
                }
            }
        }
    }

    /// Set the scale in place to exactly `scale` fractional digits (pad or
    /// banker's-round).
    pub fn rescale(&mut self, scale: u32) {
        let s = i16::try_from(scale).unwrap_or(i16::MAX);
        *self = demote(
            to_big(self.0)
                .with_rounding_mode(RoundingMode::HalfEven)
                .rescale(s),
        );
    }

    /// `self^exp` (unsigned); `None` on overflow.
    #[must_use]
    pub fn checked_powu(self, exp: u64) -> Option<Self> {
        let mut result = Self::ONE;
        for _ in 0..exp {
            result = result.checked_mul(self)?;
        }
        Some(result)
    }

    /// `self^exp` (signed; negative → reciprocal).
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
        match self.0 {
            Repr::Small(rd) => small(rd.abs()),
            Repr::Big(d) => Decimal(Repr::Big(d.abs())),
        }
    }

    #[must_use]
    pub fn signum(self) -> Self {
        if self.is_zero() {
            Self::ZERO
        } else if self.is_sign_negative() {
            Self::NEGATIVE_ONE
        } else {
            Self::ONE
        }
    }

    /// Remove trailing zeros (`1.500` → `1.5`).
    #[must_use]
    pub fn normalize(self) -> Self {
        match self.0 {
            Repr::Small(rd) => small(rd.normalize()),
            Repr::Big(d) => demote(d.reduce()),
        }
    }

    #[must_use]
    pub fn trunc(self) -> Self {
        match self.0 {
            Repr::Small(rd) => small(rd.trunc()),
            Repr::Big(d) => demote(d.trunc()),
        }
    }

    #[must_use]
    pub fn fract(self) -> Self {
        match self.0 {
            Repr::Small(rd) => small(rd.fract()),
            Repr::Big(d) => demote(d - d.trunc()),
        }
    }

    /// Round to `dp` decimal places, banker's rounding (matches
    /// `rust_decimal`'s default `round_dp`).
    #[must_use]
    pub fn round_dp(self, dp: u32) -> Self {
        self.round_dp_with_mode(dp, RoundingMode::HalfEven)
    }

    #[must_use]
    pub fn round_dp_with_mode(self, dp: u32, mode: RoundingMode) -> Self {
        // Match rust_decimal: round *down* to `dp` places but never pad.
        if self.scale() <= dp {
            return self;
        }
        // fastnum 0.7's HalfEven is buggy (treats "5 followed by nonzero" as a
        // tie: 1234.56 → 1234), so do banker's ourselves via Decimal ops (which
        // take the fast path). Other modes use D256's rescale.
        if matches!(mode, RoundingMode::HalfEven) {
            return self.round_half_even(dp);
        }
        let scaled = to_big(self.0).with_rounding_mode(mode);
        demote(scaled.rescale(i16::try_from(dp).unwrap_or(i16::MAX)))
    }

    /// Correct round-half-to-even to `dp` places (works around fastnum's buggy
    /// `HalfEven`). Operates on `Decimal` ops, so small values stay fast.
    #[must_use]
    fn round_half_even(self, dp: u32) -> Self {
        let factor = Self::TEN.checked_powu(u64::from(dp)).unwrap_or(Self::ONE);
        let scaled = self * factor; // shift the point right by dp
        let floor = scaled.trunc(); // toward zero
        let frac = (scaled - floor).abs(); // |fractional part| in [0, 1)
        let half = small(Rd::from_i128_with_scale(5, 1)); // 0.5
        let step = if scaled.is_sign_negative() {
            Self::NEGATIVE_ONE
        } else {
            Self::ONE
        };
        let rounded = match frac.cmp(&half) {
            Ordering::Less => floor,
            Ordering::Greater => floor + step,
            // exact tie → round to even
            Ordering::Equal => {
                let even = floor.checked_rem(Self::TWO).unwrap_or(Self::ZERO).is_zero();
                if even { floor } else { floor + step }
            }
        };
        // `rounded / factor` is exact; rescale only pads to `dp`.
        let val = rounded / factor;
        demote(to_big(val.0).rescale(i16::try_from(dp).unwrap_or(i16::MAX)))
    }

    /// Round to a whole number, banker's rounding.
    #[must_use]
    pub fn round(self) -> Self {
        self.round_dp(0)
    }

    #[must_use]
    pub fn checked_add(self, other: Self) -> Option<Self> {
        finite(add_core(self.0, other.0))
    }

    #[must_use]
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        finite(sub_core(self.0, other.0))
    }

    #[must_use]
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        finite(mul_core(self.0, other.0))
    }

    #[must_use]
    pub fn checked_div(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            return None;
        }
        finite(div_core(self.0, other.0))
    }

    /// `self % other`; `None` when `other` is zero.
    #[must_use]
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            return None;
        }
        finite(rem_core(self.0, other.0))
    }

    /// `rust_decimal::Decimal::from_i128_with_scale` — `num * 10^-scale`.
    /// Falls back to `Big` when `num` exceeds 96 bits or `scale` exceeds 28.
    #[must_use]
    pub fn from_i128_with_scale(num: i128, scale: u32) -> Self {
        match Rd::try_from_i128_with_scale(num, scale) {
            Ok(rd) => small(rd),
            Err(_) => demote(D256::from_str(&format!("{num}e-{scale}"), CTX).unwrap_or(D256::ZERO)),
        }
    }

    #[must_use]
    pub fn to_i64(self) -> Option<i64> {
        self.to_i128().and_then(|v| i64::try_from(v).ok())
    }
    #[must_use]
    pub fn to_u32(self) -> Option<u32> {
        self.to_i128().and_then(|v| u32::try_from(v).ok())
    }
    #[must_use]
    pub fn to_i128(self) -> Option<i128> {
        match self.0 {
            Repr::Small(rd) => rd.trunc().to_i128(),
            Repr::Big(d) => d.trunc().to_i128().ok(),
        }
    }
    #[must_use]
    pub fn to_i32(self) -> Option<i32> {
        self.to_i128().and_then(|v| i32::try_from(v).ok())
    }
    #[must_use]
    pub fn to_i16(self) -> Option<i16> {
        self.to_i128().and_then(|v| i16::try_from(v).ok())
    }
    #[must_use]
    pub fn to_i8(self) -> Option<i8> {
        self.to_i128().and_then(|v| i8::try_from(v).ok())
    }
    #[must_use]
    pub fn to_isize(self) -> Option<isize> {
        self.to_i128().and_then(|v| isize::try_from(v).ok())
    }
    #[must_use]
    pub fn to_u64(self) -> Option<u64> {
        self.to_i128().and_then(|v| u64::try_from(v).ok())
    }
    #[must_use]
    pub fn to_u16(self) -> Option<u16> {
        self.to_i128().and_then(|v| u16::try_from(v).ok())
    }
    #[must_use]
    pub fn to_u8(self) -> Option<u8> {
        self.to_i128().and_then(|v| u8::try_from(v).ok())
    }
    #[must_use]
    pub fn to_usize(self) -> Option<usize> {
        self.to_i128().and_then(|v| usize::try_from(v).ok())
    }

    #[must_use]
    pub fn to_f64(self) -> Option<f64> {
        match self.0 {
            Repr::Small(rd) => rd.to_f64().filter(|f| f.is_finite()),
            Repr::Big(d) => {
                let f = d.to_f64();
                f.is_finite().then_some(f)
            }
        }
    }

    /// From a float (exact-ish), `None` on non-finite input.
    #[must_use]
    pub fn from_f64(f: f64) -> Option<Self> {
        if !f.is_finite() {
            return None;
        }
        Self::from_str(&format!("{f}")).ok()
    }
}

/// `Some` iff finite (not NaN / ±Inf).
fn finite(d: Decimal) -> Option<Decimal> {
    match d.0 {
        Repr::Big(b) if !b.is_finite() => None,
        _ => Some(d),
    }
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

// ---- equality / ordering / hashing -----------------------------------------

impl Decimal {
    /// Compare numerically. Same-variant `Small` uses rust_decimal directly
    /// (fast); any `Big` involvement widens to `D256`.
    #[inline]
    fn cmp_value(&self, other: &Self) -> Ordering {
        match (self.0, other.0) {
            (Repr::Small(a), Repr::Small(b)) => a.cmp(&b),
            (a, b) => to_big(a).cmp(&to_big(b)),
        }
    }
}

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        self.cmp_value(other) == Ordering::Equal
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
        self.cmp_value(other)
    }
}

impl Hash for Decimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the value-normalized form so 1.0 and 1.00 hash equal, and so a
        // `Small` and a (hypothetical) `Big` of the same value would agree. The
        // `Big`-never-holds-a-small invariant keeps this cheap in practice.
        match self.0 {
            Repr::Small(rd) => rd.normalize().hash(state),
            Repr::Big(d) => d.reduce().hash(state),
        }
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
        match self.0 {
            Repr::Small(rd) => fmt::Display::fmt(&rd, f),
            // Canonicalize signed zero on the way out (rust_decimal has none).
            Repr::Big(d) if d.is_zero() => fmt::Display::fmt(&d.abs(), f),
            Repr::Big(d) => fmt::Display::fmt(&d, f),
        }
    }
}
impl fmt::Debug for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
impl fmt::LowerExp for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerExp::fmt(&to_big(self.0), f)
    }
}
impl fmt::UpperExp for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::UpperExp::fmt(&to_big(self.0), f)
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
                small(Rd::from(v))
            }
        }
    )*};
}
from_int!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);

// ---- arithmetic ------------------------------------------------------------

macro_rules! bin_op {
    ($trait:ident, $method:ident, $assign:ident, $assign_method:ident, $core:ident) => {
        impl $trait for Decimal {
            type Output = Self;
            fn $method(self, rhs: Self) -> Self {
                $core(self.0, rhs.0)
            }
        }
        impl $assign for Decimal {
            fn $assign_method(&mut self, rhs: Self) {
                *self = $core(self.0, rhs.0);
            }
        }
        impl $trait<&Decimal> for Decimal {
            type Output = Self;
            fn $method(self, rhs: &Self) -> Self {
                $core(self.0, rhs.0)
            }
        }
        impl $trait<Decimal> for &Decimal {
            type Output = Decimal;
            fn $method(self, rhs: Decimal) -> Decimal {
                $core(self.0, rhs.0)
            }
        }
        impl $trait<&Decimal> for &Decimal {
            type Output = Decimal;
            fn $method(self, rhs: &Decimal) -> Decimal {
                $core(self.0, rhs.0)
            }
        }
        impl $assign<&Decimal> for Decimal {
            fn $assign_method(&mut self, rhs: &Self) {
                *self = $core(self.0, rhs.0);
            }
        }
    };
}
bin_op!(Add, add, AddAssign, add_assign, add_core);
bin_op!(Sub, sub, SubAssign, sub_assign, sub_core);
bin_op!(Mul, mul, MulAssign, mul_assign, mul_core);
bin_op!(Div, div, DivAssign, div_assign, div_core);

impl Rem for Decimal {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        rem_core(self.0, rhs.0)
    }
}
impl Neg for Decimal {
    type Output = Self;
    fn neg(self) -> Self {
        match self.0 {
            Repr::Small(rd) => small(-rd),
            Repr::Big(d) => demote(d.neg()),
        }
    }
}
impl Neg for &Decimal {
    type Output = Decimal;
    fn neg(self) -> Decimal {
        -(*self)
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
        s.serialize_str(&self.to_string())
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
        $crate::decimal::from_small_const($crate::decimal::__rd_dec!($($t)*))
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr as _;

    fn fd(s: &str) -> Decimal {
        Decimal::from_str(s).unwrap()
    }
    /// rust_decimal reference value.
    fn rd(s: &str) -> Rd {
        Rd::from_str(s).unwrap()
    }
    /// Is this value stored in the fast `Small` representation?
    fn is_small(d: Decimal) -> bool {
        matches!(d.0, Repr::Small(_))
    }

    #[test]
    fn common_values_stay_small() {
        for s in [
            "0",
            "1",
            "-1",
            "123.45",
            "0.01",
            "1000000.999999",
            "1.123456789012345678",
        ] {
            assert!(is_small(fd(s)), "{s} should be Small");
        }
        // arithmetic on small values stays small
        assert!(is_small(fd("12345.67") + fd("89.99")));
        assert!(is_small(fd("19.99") * fd("3")));
        assert!(is_small(fd("100") - fd("0.01")));
    }

    #[test]
    fn high_precision_promotes_to_big() {
        // 28-digit operands whose exact sum needs 29+ digits → Big.
        let a = fd("0.7142857142857142857142857143"); // 28 dp
        assert!(!is_small(a + a), "28dp + 28dp should promote to Big");
        // A residual beyond rust_decimal's 28 digits must survive (the #1240
        // case): 1 + 1e-28 needs 29 digits, so rust_decimal would round it away.
        let one = Decimal::ONE;
        let tiny = fd("0.0000000000000000000000000001"); // 1e-28
        let sum = one + tiny;
        assert_ne!(sum, one, "must keep a 1e-28 residual rust_decimal loses");
        assert!(!is_small(sum), "29-digit residual must live in Big");
        assert!(tiny > Decimal::ZERO);
        // A smaller-magnitude residual that still fits 28 digits stays fast.
        assert!(is_small(one + fd("0.0000000000000000000000002"))); // 2e-25, 26 digits
    }

    #[test]
    fn parity_with_rust_decimal() {
        // Exact ops on in-range values agree digit-for-digit after normalizing.
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
    fn bankers_rounding_workaround_for_fastnum_bug() {
        assert_eq!(fd("1234.56").round().to_string(), "1235");
        assert_eq!(fd("1234.44").round().to_string(), "1234");
        assert_eq!(fd("0.56").round_dp(1).to_string(), "0.6");
        assert_eq!(fd("2.5").round().to_string(), "2"); // tie -> even
        assert_eq!(fd("3.5").round().to_string(), "4"); // tie -> even
        assert_eq!(fd("-1234.56").round().to_string(), "-1235");
    }

    #[test]
    fn round_dp_banker() {
        assert_eq!(fd("2.5").round().to_string(), "2");
        assert_eq!(fd("3.5").round().to_string(), "4");
        assert_eq!(fd("1.23456").round_dp(2).to_string(), "1.23");
        assert_eq!(fd("1.235").round_dp(2).to_string(), "1.24");
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
        assert_eq!(fd("3.5").to_i64(), Some(3)); // truncates toward zero
    }

    #[test]
    fn checked_and_serde() {
        assert_eq!(fd("1").checked_div(Decimal::ZERO), None);
        assert_eq!(fd("6").checked_div(fd("3")), Some(fd("2")));
        let v = fd("12345.6789");
        let j = serde_json::to_string(&v).unwrap();
        assert_eq!(j, "\"12345.6789\"");
        assert_eq!(serde_json::from_str::<Decimal>(&j).unwrap(), v);
    }

    #[test]
    fn ord_and_eq_across_variants() {
        assert!(fd("1.5") < fd("1.50001"));
        assert_eq!(fd("1.0"), fd("1.00")); // value equality regardless of scale
        let mut v = [fd("3"), fd("-1"), fd("2.5")];
        v.sort();
        assert_eq!(v, [fd("-1"), fd("2.5"), fd("3")]);
        // a Big value compares correctly against Small neighbours
        let big = fd("0.7142857142857142857142857143") + fd("0.7142857142857142857142857143");
        assert!(!is_small(big));
        assert!(big > Decimal::ONE && big < fd("2"));
    }

    #[test]
    fn hash_consistent_value_equality() {
        use std::collections::hash_map::DefaultHasher;
        let h = |d: Decimal| {
            let mut s = DefaultHasher::new();
            d.hash(&mut s);
            s.finish()
        };
        assert_eq!(h(fd("1.0")), h(fd("1.00")));
        assert_eq!(h(fd("2.50")), h(fd("2.5")));
    }
}
