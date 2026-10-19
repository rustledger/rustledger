//! Decimal arithmetic with Python `decimal` scale semantics.
//!
//! `rust_decimal` and Python's `decimal` agree on the VALUE of a sum but not
//! always on its SCALE, and BQL renders a naked decimal at its intrinsic scale
//! (bean-query's `DecimalRenderer` pads for alignment only — it never
//! quantizes). So a scale difference is a visible output difference.
//!
//! Python's rule for `+`/`-` is that an exact result carries
//! `max(scale(a), scale(b))`:
//!
//! ```text
//!   Decimal("0.00") + Decimal("1")  ==  Decimal("1.00")
//! ```
//!
//! `rust_decimal` matches that for ordinary operands (`2.00 + 1 == 3.00`) but
//! not when one side is ZERO: its addition returns the other operand
//! unchanged, so the zero's scale is discarded and `0.00 + 1 == 1`.
//!
//! That makes an accumulation order-dependent, which is how it surfaced. A
//! `SUM` over `-1, 1, -111.11, 111.11, -2, 2` passes through `0.00` at the
//! fourth term; the `-2` that follows then resets the running total to scale
//! 0 and the query prints `0` where bean-query prints `0.00`. Move the
//! fractional pair last and the same multiset prints `0.00` — same value,
//! same inputs, different rendering.

use rust_decimal::Decimal;

/// Add two decimals with Python `decimal`'s scale rule.
///
/// The value is `a + b` either way; this only restores the scale
/// `rust_decimal` drops when an operand is zero (see the module docs). The
/// result is padded UP to `max(scale(a), scale(b))` and never truncated, so
/// it cannot lose significant digits.
///
/// Rescaling is best-effort: `Decimal::rescale` is a no-op when the target
/// scale would overflow the 96-bit mantissa (a value near `Decimal::MAX` at
/// high scale). Such a value cannot be represented at that scale at all, so
/// there is nothing to restore and the unrescaled sum is the best available
/// answer — the same one we returned before this function existed.
#[must_use]
pub fn add_python_scale(a: Decimal, b: Decimal) -> Decimal {
    let mut sum = a + b;
    let target = a.scale().max(b.scale());
    if sum.scale() < target {
        sum.rescale(target);
    }
    sum
}

/// Subtract with Python `decimal`'s scale rule — see [`add_python_scale`].
#[must_use]
pub fn sub_python_scale(a: Decimal, b: Decimal) -> Decimal {
    let mut diff = a - b;
    let target = a.scale().max(b.scale());
    if diff.scale() < target {
        diff.rescale(target);
    }
    diff
}

/// Overflow-checked [`add_python_scale`].
///
/// `None` on value-range overflow, matching `Decimal::checked_add` — BQL maps
/// that to NULL rather than panicking, so the checked form is what the
/// expression evaluator needs.
#[must_use]
pub fn checked_add_python_scale(a: Decimal, b: Decimal) -> Option<Decimal> {
    let mut sum = a.checked_add(b)?;
    let target = a.scale().max(b.scale());
    if sum.scale() < target {
        sum.rescale(target);
    }
    Some(sum)
}

/// Sum `values` exactly and round ONCE, with [`add_python_scale`]'s scale rule:
/// the result's scale is at least the largest operand scale.
///
/// A left fold of [`checked_add_python_scale`] is order-DEPENDENT at the edge
/// of the range: a partial sum can overflow even though the total fits
/// (`[MAX - k, MAX, -MAX]` fails at its first step, while `[MAX, -MAX,
/// MAX - k]` succeeds). This answers what the total IS, whatever the order.
/// `None` only when the exact total itself cannot be held in a `Decimal`.
///
/// Slower than the fold, since every operand goes through `BigDecimal`, so it
/// is for the fold's failure path, not a replacement for it (#2404).
#[must_use]
pub fn checked_exact_sum_python_scale<I>(values: I) -> Option<Decimal>
where
    I: IntoIterator<Item = Decimal>,
{
    let mut target = 0;
    let mut exact = bigdecimal::BigDecimal::from(0);
    for value in values {
        target = target.max(value.scale());
        exact += to_bigdecimal(value);
    }
    // `to_plain_string`, not `Display`, as in the AVERAGE escalation (#2353):
    // `Display` switches to exponent form. Parsing rounds to what a `Decimal`
    // can hold and fails only when the magnitude cannot fit at all.
    let mut sum = <Decimal as core::str::FromStr>::from_str(&exact.to_plain_string()).ok()?;
    if sum.scale() < target {
        sum.rescale(target);
    }
    Some(sum)
}

/// `a - b`, or `None` when no `Decimal` holds the difference EXACTLY.
///
/// `checked_sub` fails only past `Decimal::MAX`. Where the exact difference
/// needs more than the 96-bit mantissa at the operands' scale it ROUNDS and
/// still answers `Some`: `MAX - 0.48` comes back as `MAX`. A quantity that
/// keeps shrinking through such a subtraction (a reduction's units still to
/// find, #2554) then never shrinks, and more is taken than was asked for.
///
/// An exact difference keeps the wider operand scale, so a narrower one is
/// the cheap signal -- the fast path costs one comparison. It is only a
/// signal: an exact result whose dropped digits were zeros, and
/// `rust_decimal`'s shortcut for a zero operand, narrow the scale as well, so
/// a narrower result is confirmed in `BigDecimal` before it is refused.
#[must_use]
pub fn checked_sub_exact(a: Decimal, b: Decimal) -> Option<Decimal> {
    let diff = a.checked_sub(b)?;
    if diff.scale() >= a.scale().max(b.scale()) {
        return Some(diff);
    }
    (to_bigdecimal(a) - to_bigdecimal(b) == to_bigdecimal(diff)).then_some(diff)
}

/// `a + b`, or `None` when no `Decimal` holds the sum EXACTLY -- see
/// [`checked_sub_exact`]. `checked_add(MAX, 0.48)` is `Some(MAX)`.
#[must_use]
pub fn checked_add_exact(a: Decimal, b: Decimal) -> Option<Decimal> {
    let sum = a.checked_add(b)?;
    if sum.scale() >= a.scale().max(b.scale()) {
        return Some(sum);
    }
    (to_bigdecimal(a) + to_bigdecimal(b) == to_bigdecimal(sum)).then_some(sum)
}

/// `a × b`, or `None` when no `Decimal` holds the product EXACTLY -- see
/// [`checked_sub_exact`].
///
/// `checked_mul` fails only past `Decimal::MAX`. A product needing more than
/// 28 fractional digits, or more than the mantissa at its scale, is ROUNDED to
/// nearest and still answers `Some`: `0.005 × 1.23456789012345678901234567`
/// comes back a unit in the 28th place too large (#2582), and `1e-15 × 1e-15`
/// comes back `0`. An exact product carries `scale(a) + scale(b)`, so a
/// narrower one is the cheap signal, confirmed in `BigDecimal` because a
/// product whose dropped digits were zeros narrows too.
#[must_use]
pub fn checked_mul_exact(a: Decimal, b: Decimal) -> Option<Decimal> {
    let product = a.checked_mul(b)?;
    if product.scale() >= a.scale() + b.scale() {
        return Some(product);
    }
    (to_bigdecimal(a) * to_bigdecimal(b) == to_bigdecimal(product)).then_some(product)
}

/// [`checked_add_python_scale`] that also refuses a sum it would have to ROUND.
///
/// For what a lot holds once a reduction is taken from it, where a rounded
/// sum keeps units the lot sold (`MAX` less `0.48` is still `MAX`, #2554).
///
/// Stricter than Python, deliberately: beancount subtracts in a 28-digit
/// context and rounds the same lot without a word. A lot is a count, and a
/// count that changes by a rounding step is a wrong number.
#[must_use]
pub fn checked_add_exact_python_scale(a: Decimal, b: Decimal) -> Option<Decimal> {
    let mut sum = checked_add_exact(a, b)?;
    let target = a.scale().max(b.scale());
    if sum.scale() < target {
        sum.rescale(target);
    }
    Some(sum)
}

/// The `Decimal` equal to `exact`, or `None` when there is none: the value is
/// out of range, or needs more digits than the mantissa holds.
///
/// Parsing alone is not enough -- `Decimal`'s parser ROUNDS excess digits --
/// so the parsed value is compared back against `exact`.
#[must_use]
pub fn decimal_from_big_exact(exact: &bigdecimal::BigDecimal) -> Option<Decimal> {
    // `to_plain_string`, as in `checked_exact_sum_python_scale`: `Display`
    // switches to exponent form, which the parser rejects.
    let parsed = <Decimal as core::str::FromStr>::from_str(&exact.to_plain_string()).ok()?;
    (to_bigdecimal(parsed) == *exact).then_some(parsed)
}

/// Overflow-checked [`sub_python_scale`] — see [`checked_add_python_scale`].
#[must_use]
pub fn checked_sub_python_scale(a: Decimal, b: Decimal) -> Option<Decimal> {
    let mut diff = a.checked_sub(b)?;
    let target = a.scale().max(b.scale());
    if diff.scale() < target {
        diff.rescale(target);
    }
    Some(diff)
}

/// Divide with Python `decimal`'s scale rule.
///
/// Python defines an *ideal exponent* for division: `exp(a) - exp(b)`, i.e.
/// an ideal SCALE of `scale(a) - scale(b)`. An exact quotient is reduced
/// toward that scale but never below the scale exactness requires:
///
/// ```text
///   0.00 / 4     ->  0.00     ideal 2, exact needs 0  -> 2
///   7    / 2     ->  3.5      ideal 0, exact needs 1  -> 1
///   1.00 / 2     ->  0.50     ideal 2, exact needs 1  -> 2
///   1.000 / 8    ->  0.125    ideal 3, exact needs 3  -> 3
/// ```
///
/// `rust_decimal` misses this in BOTH directions, so a pad-only fix would be
/// half a fix:
///
/// * **Under**, on a zero dividend — the same zero shortcut behind
///   [`add_python_scale`]. `0.00 / 4` gives `0`, dropping the scale.
/// * **Over**, on an exact quotient — `7 / 2` gives `3.50`, one trailing
///   zero more than the ideal exponent allows.
///
/// So the quotient is stripped to its minimal form and then padded up to the
/// ideal scale; the two steps together land on Python's answer from either
/// side. An inexact quotient (`1 / 3`) has no trailing zeros to strip and a
/// scale far past the ideal, so both steps are no-ops and it is returned as
/// `rust_decimal` computed it.
///
/// Returns `None` on divide-by-zero or overflow, matching
/// `Decimal::checked_div` — BQL maps that to NULL rather than panicking.
#[must_use]
pub fn checked_div_python_scale(a: Decimal, b: Decimal) -> Option<Decimal> {
    let quotient = a.checked_div(b)?;
    // `scale()` is u32; the ideal can be negative (a coarser dividend than
    // divisor), which simply means "no padding required".
    let ideal_scale = i64::from(a.scale()) - i64::from(b.scale());
    Some(with_ideal_scale(quotient, ideal_scale))
}

/// Convert to `BigDecimal` for arithmetic `Decimal` cannot do exactly.
///
/// Built from the parts, not a `to_string` / `from_str` round trip: a `Decimal`
/// IS `mantissa * 10^-scale` and `BigDecimal::new` takes exactly that, so this
/// is the same value AND the same scale, measured identical on 500,010 decimals
/// including `MAX`, `MIN`, `-0.00` and trailing-zero-padded 18-place values.
///
/// The ONE conversion: `rustledger_booking`'s precise residual (#1240) and this
/// crate's weighted-average escalation (#2353) both go through it.
#[must_use]
pub fn to_bigdecimal(d: Decimal) -> bigdecimal::BigDecimal {
    bigdecimal::BigDecimal::new(
        bigdecimal::num_bigint::BigInt::from(d.mantissa()),
        i64::from(d.scale()),
    )
}

/// Give a quotient Python's ideal-exponent scale: strip the trailing zeros the
/// division invented, then pad back up to `ideal_scale`.
///
/// The second half of [`checked_div_python_scale`], split out for a caller that
/// computed its quotient some other way: the exact `BigDecimal` path of
/// `rustledger_booking::prorate`, whose product does not fit in a `Decimal` and
/// so cannot be handed to the division above. One implementation, so the two
/// cannot drift on what "ideal" means.
///
/// ONLY for an exact quotient. Normalizing an inexact one can strip a trailing
/// zero that is a significant rounded digit, which Python keeps; the division
/// above never meets that case because `rust_decimal` does not emit a trailing
/// zero on an inexact quotient, so a caller with its own quotient must check
/// exactness first.
///
/// `ideal_scale` is `dividend.scale() - divisor.scale()` for a plain division,
/// or `a.scale() + b.scale() - c.scale()` for `a * b / c`, and may be negative
/// (a coarser dividend than divisor), which means no padding. Never changes the
/// value.
#[must_use]
pub fn with_ideal_scale(quotient: Decimal, ideal_scale: i64) -> Decimal {
    // Minimal form first: this is what removes the EXTRA trailing zero in
    // `7 / 2 -> 3.50`. `normalize` never loses value.
    let mut result = quotient.normalize();
    // Capped at `Decimal::MAX_SCALE`. `rescale` clamps only a ZERO to it; a
    // nonzero value scales up until its 96-bit mantissa is full, straight past
    // 28. `0.5` rescaled to 36 comes back with scale 29 — a `Decimal` that
    // `rust_decimal`'s own `from_parts` panics on, and that a `serialize` /
    // `deserialize` round trip silently turns into scale 28. `checked_div_
    // python_scale` cannot ask for more than 28 (its ideal is a difference of
    // two scales), but `prorate`'s `a * b / c` can ask for up to 56.
    let target = ideal_scale
        .max(i64::from(result.scale()))
        .min(i64::from(Decimal::MAX_SCALE));

    // `rescale` takes u32 and is a no-op past the mantissa's capacity; the
    // clamp keeps a pathological ideal from wrapping on the cast.
    if let Ok(target) = u32::try_from(target)
        && result.scale() < target
    {
        result.rescale(target);
    }
    result
}

/// Negate with Python `decimal`'s sign rule for zero.
///
/// Python defines unary minus as `0 - x`, so negating ANY zero yields a
/// POSITIVE zero:
///
/// ```text
///   -Decimal("0.00")   ==  0.00
///   -Decimal("-0.00")  ==  0.00
/// ```
///
/// `rust_decimal`'s `Neg` flips the sign bit unconditionally, so `-dec!(0.00)`
/// is a signed zero that renders `-0.00`. beancount normalizes it away — a
/// ledger posting written `-0.00 CNY` loads as `Decimal('0.00')` there, and
/// bean-query prints `0.00` — while rledger's parser applies the sign with a
/// bare `-n` and kept the `-0.00` all the way to the output.
///
/// A zero has no sign in bookkeeping; this is the canonical negation for any
/// site that flips a parsed or computed amount.
#[must_use]
pub fn negate_python(number: Decimal) -> Decimal {
    if number.is_zero() {
        // `abs` clears the sign bit and keeps the scale — `normalize` would
        // strip the scale too, and `+ ZERO` collapses it to `0`.
        number.abs()
    } else {
        -number
    }
}

/// Round to `dp` decimal places with Python `decimal`'s sign rule for zero.
///
/// Python's `quantize` keeps the sign when a small negative rounds away:
///
/// ```text
///   Decimal("-0.00495").quantize(Decimal("0.01"))  ==  -0.00
///   Decimal("-0.0000001").quantize(Decimal("0.01")) == -0.00
/// ```
///
/// `rust_decimal`'s `round_dp` returns an UNSIGNED zero there, which loses
/// the only information the cell still carries — that the underlying balance
/// is negative rather than exactly zero. bean-query renders `-0.00 USD` for a
/// `-0.00495 USD` position; rledger rendered `0.00 USD` and read as flat.
///
/// The result is padded to exactly `dp` (see the caller's note on `round_dp`
/// only ever reducing the scale).
#[must_use]
pub fn round_dp_python(number: Decimal, dp: u32) -> Decimal {
    let mut rounded = number.round_dp(dp);
    rounded.rescale(dp);
    if rounded.is_zero() && number.is_sign_negative() {
        // Re-apply the sign the rounding dropped. Negating a positive zero is
        // exactly how a signed zero is constructed in `rust_decimal`.
        return -rounded;
    }
    rounded
}

/// The precision of the `decimal` context beancount computes in.
///
/// beancount never installs a context of its own for booking — the only
/// `localcontext` calls in beancount 3.2.3 are in `display_context` and the
/// example generator — so every division booking does runs under Python's
/// default: `prec=28`, `rounding=ROUND_HALF_EVEN`, `Emin=-999999`,
/// `Emax=999999`. beanquery does not change it either.
const PY_PREC: usize = 28;

/// A finite Python `decimal` number: `(-1)^neg × coeff × 10^exp`.
///
/// Python's representation, not `rust_decimal`'s: the exponent is unbounded in
/// both directions (`Emin`/`Emax` are ±999999, which nothing here reaches), so
/// an intermediate like `1e-11 × 1e-18 = 1E-29` is held exactly where a
/// `Decimal` would round it to zero (#2351).
#[derive(Debug, Clone)]
struct PyNum {
    neg: bool,
    coeff: bigdecimal::num_bigint::BigUint,
    exp: i64,
}

impl PyNum {
    fn from_decimal(d: Decimal) -> Self {
        Self {
            neg: d.is_sign_negative(),
            coeff: bigdecimal::num_bigint::BigUint::from(d.mantissa().unsigned_abs()),
            exp: -i64::from(d.scale()),
        }
    }

    fn is_zero(&self) -> bool {
        self.coeff == bigdecimal::num_bigint::BigUint::ZERO
    }
}

fn pow10(n: u64) -> bigdecimal::num_bigint::BigUint {
    use bigdecimal::num_traits::Pow;
    bigdecimal::num_bigint::BigUint::from(10u32).pow(n)
}

fn digit_count(n: &bigdecimal::num_bigint::BigUint) -> usize {
    if *n == bigdecimal::num_bigint::BigUint::ZERO {
        1
    } else {
        n.to_str_radix(10).len()
    }
}

/// Python's `Decimal._fix` for this context: round `coeff` to [`PY_PREC`]
/// significant digits, half to even, moving the exponent up by the digits
/// dropped. A carry that grows the coefficient to `PY_PREC + 1` digits
/// (`9.99…95` → `10.00…0`) drops one more, exactly as `_fix` does.
fn py_fix(mut n: PyNum) -> PyNum {
    let digits = digit_count(&n.coeff);
    if n.is_zero() || digits <= PY_PREC {
        return n;
    }
    let drop = (digits - PY_PREC) as u64;
    let unit = pow10(drop);
    let mut kept = &n.coeff / &unit;
    let rest = &n.coeff % &unit;
    let half = &unit / 2u32;
    let kept_is_odd = (&kept % 2u32) == bigdecimal::num_bigint::BigUint::from(1u32);
    if rest > half || (rest == half && kept_is_odd) {
        kept += 1u32;
    }
    n.exp += i64::try_from(drop).unwrap_or(i64::MAX);
    if digit_count(&kept) > PY_PREC {
        kept /= 10u32;
        n.exp += 1;
    }
    n.coeff = kept;
    n
}

/// `a × b` as Python computes it: exact, then rounded to the context.
fn py_mul(a: &PyNum, b: &PyNum) -> PyNum {
    py_fix(PyNum {
        neg: a.neg != b.neg,
        coeff: &a.coeff * &b.coeff,
        exp: a.exp + b.exp,
    })
}

/// `a + b` as Python computes it: exact at the smaller exponent, then rounded
/// to the context. (Python's zero-operand shortcut pads the other operand to
/// at most `prec + 1` extra digits before rounding; the rounded result is the
/// same, so it needs no case of its own.)
fn py_add(a: &PyNum, b: &PyNum) -> PyNum {
    use bigdecimal::num_bigint::{BigInt, Sign};
    let exp = a.exp.min(b.exp);
    let scaled = |n: &PyNum| {
        let magnitude = &n.coeff * pow10(u64::try_from(n.exp - exp).unwrap_or(0));
        BigInt::from_biguint(if n.neg { Sign::Minus } else { Sign::Plus }, magnitude)
    };
    let sum = scaled(a) + scaled(b);
    py_fix(PyNum {
        neg: sum.sign() == Sign::Minus,
        coeff: sum.magnitude().clone(),
        exp,
    })
}

/// `a / b` as Python computes it — `Decimal.__truediv__`, line for line.
///
/// `None` when `b` is zero (Python raises: `DivisionByZero`, or
/// `InvalidOperation` for `0 / 0`, both trapped by the default context).
fn py_div_num(a: &PyNum, b: &PyNum) -> Option<PyNum> {
    if b.is_zero() {
        return None;
    }
    let neg = a.neg != b.neg;
    let ideal_exp = a.exp - b.exp;
    if a.is_zero() {
        // `exp = self._exp - other._exp`, coefficient 0.
        return Some(PyNum {
            neg,
            coeff: bigdecimal::num_bigint::BigUint::ZERO,
            exp: ideal_exp,
        });
    }
    // Scale the dividend so the integer quotient has PY_PREC + 1 or + 2
    // digits: enough to round from.
    let shift = digit_count(&b.coeff) as i64 - digit_count(&a.coeff) as i64 + PY_PREC as i64 + 1;
    let mut exp = ideal_exp - shift;
    let (mut coeff, remainder) = if shift >= 0 {
        let num = &a.coeff * pow10(shift.unsigned_abs());
        (&num / &b.coeff, &num % &b.coeff)
    } else {
        let den = &b.coeff * pow10(shift.unsigned_abs());
        (&a.coeff / &den, &a.coeff % &den)
    };
    if remainder == bigdecimal::num_bigint::BigUint::ZERO {
        // Exact: strip the zeros the shift invented, but only down to the
        // ideal exponent. `10.00 / 4` stops at `2.50`; `10 / 4` at `2.5`.
        while exp < ideal_exp && (&coeff % 10u32) == bigdecimal::num_bigint::BigUint::ZERO {
            coeff /= 10u32;
            exp += 1;
        }
    } else if (&coeff % 5u32) == bigdecimal::num_bigint::BigUint::ZERO {
        // Inexact: a sticky digit, so a quotient just above a tie (or just
        // above an exact truncation) cannot round as if it were one.
        coeff += 1u32;
    }
    Some(py_fix(PyNum { neg, coeff, exp }))
}

/// `round(a / b)` to `Decimal::MAX_SCALE` places, half to even, exactly.
///
/// The fallback for a quotient Python carries further down than a `Decimal`
/// can: the EXACT quotient rounded once, never Python's already-rounded
/// result rounded a second time.
fn quotient_at_max_scale(a: &PyNum, b: &PyNum) -> Option<Decimal> {
    let k = a.exp - b.exp + i64::from(Decimal::MAX_SCALE);
    let (num, den) = if k >= 0 {
        (&a.coeff * pow10(k.unsigned_abs()), b.coeff.clone())
    } else {
        (a.coeff.clone(), &b.coeff * pow10(k.unsigned_abs()))
    };
    let mut q = &num / &den;
    let twice_rest = (&num % &den) * 2u32;
    let q_is_odd = (&q % 2u32) == bigdecimal::num_bigint::BigUint::from(1u32);
    if twice_rest > den || (twice_rest == den && q_is_odd) {
        q += 1u32;
    }
    if q == bigdecimal::num_bigint::BigUint::ZERO {
        // A nonzero quotient below half of `1e-28`: the only `Decimal` it
        // rounds to is zero, a number nobody wrote. Refuse it.
        return None;
    }
    to_decimal_parts(a.neg != b.neg, &q, Decimal::MAX_SCALE)
}

fn to_decimal_parts(
    neg: bool,
    magnitude: &bigdecimal::num_bigint::BigUint,
    scale: u32,
) -> Option<Decimal> {
    let m = i128::try_from(magnitude).ok()?;
    let d = Decimal::try_from_i128_with_scale(if neg { -m } else { m }, scale).ok()?;
    // A zero has no sign in bookkeeping (see `negate_python`).
    Some(if d.is_zero() { d.abs() } else { d })
}

/// Turn a Python result into the `Decimal` with the same value and digits.
///
/// Exact for every result whose exponent is in `-28..=0` — the
/// `to_string()` of the `Decimal` is then Python's `format(q, "f")`. Two
/// shapes have no such `Decimal`, and are documented on [`py_div`].
fn py_to_decimal(q: &PyNum, a: &PyNum, b: &PyNum) -> Option<Decimal> {
    if q.exp > 0 {
        // Python writes `2E+1`; `rust_decimal` has no negative scale, so the
        // same value is the integer `20`. `None` past `Decimal::MAX`.
        let value = &q.coeff * pow10(q.exp.unsigned_abs());
        return to_decimal_parts(q.neg, &value, 0);
    }
    let scale = u32::try_from(q.exp.unsigned_abs()).unwrap_or(u32::MAX);
    if scale <= Decimal::MAX_SCALE {
        return to_decimal_parts(q.neg, &q.coeff, scale);
    }
    if q.is_zero() {
        return Some(Decimal::new(0, Decimal::MAX_SCALE));
    }
    quotient_at_max_scale(a, b)
}

/// Divide exactly as Python's `decimal` does under beancount's context.
///
/// beancount derives every per-unit number it books from a total with a bare
/// `Decimal` division in Python's default context (`prec=28`,
/// `ROUND_HALF_EVEN`): `{{T}}` and `{a # b}` in
/// `booking_full.convert_costspec_to_cost`, `@@` in the parser's
/// `Builder.posting`, an interpolated `{}` cost or `@` price in
/// `booking_full.interpolate_group`. The General Decimal Arithmetic rule it
/// follows:
///
/// * **Exact quotient:** the exponent closest to the ideal exponent
///   `exp(a) − exp(b)` — trailing zeros are kept down to it, never past it.
///   `10 / 4` is `2.5`, `10.00 / 4` is `2.50`, `7.5 / 3` is `2.5`.
/// * **Inexact quotient:** rounded half-even to 28 SIGNIFICANT digits.
///   `10 / 3` is `3.333333333333333333333333333` (27 places), where
///   `rust_decimal`'s own division keeps 28 places and lands on a different
///   value in the last digit (#2652).
///
/// # Where a `Decimal` cannot hold Python's answer
///
/// * **A positive exponent** (`10 / 0.5` is `2E+1`): returned as the
///   same value at scale 0 (`20`). `rust_decimal` has no negative scale;
///   the value is identical and only the notation differs. `None` past
///   `Decimal::MAX`, as `checked_div` does.
/// * **An exponent below −28** (`1 / 30000000000` is
///   `3.333333333333333333333333333E-11`): Python keeps 28 significant
///   digits that need 38 places. The exact quotient is rounded ONCE,
///   half-even, to 28 places (`0.0000000000333333333333333333`) — the
///   nearest `Decimal`, which is what `checked_div` returned before this
///   helper. When that nearest `Decimal` is zero for a nonzero quotient the
///   result is `None`, not a zero nobody wrote (the underflow class of
///   #2344).
/// * **A negative zero** (`0.00 / -4` is `-0.00` in Python) comes back
///   unsigned, the crate's rule for zero (see [`negate_python`]).
///
/// `None` on division by zero.
#[must_use]
pub fn py_div(a: Decimal, b: Decimal) -> Option<Decimal> {
    let (a, b) = (PyNum::from_decimal(a), PyNum::from_decimal(b));
    let q = py_div_num(&a, &b)?;
    py_to_decimal(&q, &a, &b)
}

/// The per-unit number of a compound cost `{per # total}` over `units`, as
/// beancount computes it.
///
/// That is `(total + per × |units|) / |units|`, each step rounded to Python's
/// 28-digit context in turn (`booking_full.convert_costspec_to_cost`).
///
/// The intermediates are held as Python holds them, with an unbounded
/// exponent, so a product too small for a `Decimal` (`1e-11 × 1e-18`) is
/// carried exactly instead of rounding to zero (#2351). The final quotient
/// leaves through the same conversion as [`py_div`], with the same `None`
/// cases; zero `units` is `None`.
#[must_use]
pub fn py_compound_per_unit(per_unit: Decimal, total: Decimal, units: Decimal) -> Option<Decimal> {
    let n = PyNum::from_decimal(units.abs());
    let product = py_mul(&PyNum::from_decimal(per_unit), &n);
    let cost_total = py_add(&PyNum::from_decimal(total), &product);
    let q = py_div_num(&cost_total, &n)?;
    py_to_decimal(&q, &cost_total, &n)
}

#[cfg(test)]
mod tests {
    /// `with_ideal_scale` must never produce a `Decimal` above
    /// `Decimal::MAX_SCALE`, however large the ideal it is asked for.
    ///
    /// `rescale` does not enforce the limit for a nonzero value: `0.5` rescaled
    /// to 36 comes back at scale 29, and `from_parts` rebuilding that value
    /// from its own parts panics. The check below is that rebuild, so a
    /// regression shows up as the panic a downstream caller would hit.
    #[test]
    fn with_ideal_scale_never_exceeds_max_scale() {
        for (value, ideal) in [("0.5", 36i64), ("0.311728394506172839", 35), ("0.05", 56)] {
            let got = with_ideal_scale(Decimal::from_str_exact(value).expect("literal"), ideal);
            assert!(
                got.scale() <= Decimal::MAX_SCALE,
                "{value} at ideal {ideal}: scale {}",
                got.scale()
            );
            let m = got.mantissa().unsigned_abs();
            #[allow(clippy::cast_possible_truncation)]
            let rebuilt = Decimal::from_parts(
                m as u32,
                (m >> 32) as u32,
                (m >> 64) as u32,
                got.is_sign_negative(),
                got.scale(),
            );
            assert_eq!(
                rebuilt, got,
                "{value} must survive a rebuild from its own parts"
            );
        }
    }

    use super::*;
    use rust_decimal_macros::dec;
    use std::str::FromStr;

    /// The exact shape `rust_decimal` gets wrong: a zero operand's scale is
    /// dropped. Both orders, since its zero shortcut applies to either side.
    ///
    /// Asserts on `to_string()`, NOT on `Decimal` equality. `==` compares
    /// value and ignores scale — `dec!(1) == dec!(1.00)` — so an
    /// `assert_eq!(add_python_scale(..), dec!(1.00))` here would pass against
    /// a plain `a + b` and pin nothing. That is exactly what this test looked
    /// like when Copilot caught it on #2046; the rendered form is the whole
    /// subject of the divergence, so it is what gets asserted.
    #[test]
    fn a_zero_operand_keeps_its_scale() {
        assert_eq!(add_python_scale(dec!(0.00), dec!(1)).to_string(), "1.00");
        assert_eq!(add_python_scale(dec!(1), dec!(0.00)).to_string(), "1.00");
        assert_eq!(sub_python_scale(dec!(0.00), dec!(1)).to_string(), "-1.00");
        assert_eq!(sub_python_scale(dec!(1), dec!(0.00)).to_string(), "1.00");
    }

    /// The trap the test above avoids, pinned so it cannot silently return:
    /// `Decimal`'s `==` cannot see a scale difference, and the raw operator
    /// really does drop it.
    #[test]
    fn decimal_equality_cannot_see_the_bug_but_rendering_can() {
        assert_eq!(dec!(1), dec!(1.00), "== ignores scale");
        assert_eq!((dec!(0.00) + dec!(1)).to_string(), "1", "the bug itself");
        assert_eq!(add_python_scale(dec!(0.00), dec!(1)).to_string(), "1.00");
    }

    /// Ordinary operands already behaved; the fix must not disturb them.
    #[test]
    fn non_zero_operands_are_unchanged() {
        for (a, b, want) in [
            (dec!(2.00), dec!(1), "3.00"),
            (dec!(1), dec!(2.00), "3.00"),
            (dec!(2.50), dec!(2.50), "5.00"),
            (dec!(111.11), dec!(-111.11), "0.00"),
            (dec!(1), dec!(2), "3"),
        ] {
            assert_eq!(add_python_scale(a, b).to_string(), want, "{a} + {b}");
        }
    }

    /// Padding is upward only — a result that already carries more scale than
    /// either operand (impossible for `+`, but the guard is what makes that
    /// true) keeps it, and no significant digit is ever dropped.
    #[test]
    fn never_truncates() {
        assert_eq!(add_python_scale(dec!(0.5), dec!(0.25)).to_string(), "0.75");
        assert_eq!(
            add_python_scale(dec!(0), dec!(1.2345)).to_string(),
            "1.2345"
        );
    }

    /// The running-total shape from the compat corpus: passing through zero
    /// mid-accumulation must not reset the scale for the terms that follow.
    #[test]
    fn accumulating_through_zero_keeps_the_widest_scale() {
        let terms = [
            dec!(-1),
            dec!(1),
            dec!(-111.11),
            dec!(111.11),
            dec!(-2),
            dec!(2),
        ];

        let mut python_like = Decimal::ZERO;
        let mut naive = Decimal::ZERO;
        for t in terms {
            python_like = add_python_scale(python_like, t);
            naive += t;
        }

        assert_eq!(python_like.to_string(), "0.00");
        assert_eq!(naive.to_string(), "0", "pins the pre-fix behavior");
    }

    /// Division scale, against Python `decimal`'s answers verbatim.
    ///
    /// Every expectation below was produced by running the case through
    /// `CPython`'s `decimal` (3.13) rather than reasoned out — the ideal-exponent
    /// rule is easy to state and easy to get subtly wrong, and a table of
    /// hand-derived expectations would just encode the same misreading twice.
    ///
    /// Asserts on `to_string()`: `Decimal`'s `==` ignores scale, which is the
    /// entire subject here.
    #[test]
    fn division_matches_python_decimal_scale() {
        // (dividend, divisor, python's rendering)
        let cases = [
            // Zero dividend — `rust_decimal` drops the scale (gives `0`).
            ("0.00", "4", "0.00"),
            ("0.000", "3", "0.000"),
            ("0.0", "7", "0.0"),
            ("0.00", "2.0", "0.0"),
            ("0.00", "1", "0.00"),
            ("-0.00", "3", "0.00"), // see the sign note below
            // Zero with no scale to keep.
            ("0", "4", "0"),
            // Exact quotients — `rust_decimal` OVER-pads `7 / 2` to `3.50`.
            ("7", "2", "3.5"),
            ("5", "4", "1.25"),
            ("1.0", "2.00", "0.5"),
            // Exact quotients both already agree on.
            ("1.00", "2", "0.50"),
            ("3.00", "3", "1.00"),
            ("1.000", "8", "0.125"),
            ("10.00", "4", "2.50"),
            ("2.50", "5", "0.50"),
            ("100.00", "8", "12.50"),
            ("12.345", "5", "2.469"),
            // Inexact: no trailing zeros to strip, scale far past the ideal,
            // so the rule leaves `rust_decimal`'s result alone.
            ("1", "3", "0.3333333333333333333333333333"),
        ];

        for (a, b, want) in cases {
            let a = Decimal::from_str(a).expect("dividend parses");
            let b = Decimal::from_str(b).expect("divisor parses");
            let got = checked_div_python_scale(a, b).expect("no overflow");
            assert_eq!(got.to_string(), want, "{a} / {b}");
        }
    }

    /// `from_str` drops a literal minus on zero, but the TYPE can hold a
    /// signed zero — the two are different things, and #2049 conflated them.
    ///
    /// That commit asserted "the type has no signed zero" from this same
    /// `from_str` evidence. It does: `-dec!(0.00)` renders `-0.00`, which is
    /// exactly the value the parser used to archive for a `-0.00` literal.
    /// The narrower true statement is pinned here instead, since the division
    /// table above depends on it: a `-0.00` DIVIDEND reaching
    /// `checked_div_python_scale` via `from_str` is already unsigned, so the
    /// `-0.00` Python would print is unreachable by that route.
    #[test]
    fn from_str_drops_the_sign_on_zero_though_the_type_can_carry_one() {
        let parsed = Decimal::from_str("-0.00").expect("parses");
        assert_eq!(parsed.to_string(), "0.00", "from_str drops it");
        assert!(!parsed.is_sign_negative());

        // ...but the type carries one when constructed by negation.
        assert_eq!((-Decimal::from_str("0.00").unwrap()).to_string(), "-0.00");

        assert_eq!(
            checked_div_python_scale(parsed, Decimal::from(3))
                .expect("no overflow")
                .to_string(),
            "0.00",
        );
    }

    /// Divide-by-zero is `None`, not a panic — BQL renders it NULL.
    #[test]
    fn division_by_zero_is_none() {
        assert_eq!(
            checked_div_python_scale(dec!(1.00), Decimal::ZERO),
            None,
            "div-by-zero must not panic",
        );
    }

    /// Negating a zero must yield a POSITIVE zero, as Python does.
    ///
    /// `rust_decimal`'s `Neg` flips the sign bit unconditionally, so a bare
    /// `-dec!(0.00)` renders `-0.00`. beancount loads a ledger posting written
    /// `-0.00 CNY` as `Decimal('0.00')` and bean-query prints `0.00`, so the
    /// signed zero was ours alone.
    ///
    /// Asserts on `to_string()` — `==` cannot see a sign on zero any more than
    /// it can see scale (`dec!(0.00) == -dec!(0.00)`), so a value-level
    /// assertion would pass against the bug.
    #[test]
    fn negating_a_zero_gives_an_unsigned_zero() {
        assert_eq!((-dec!(0.00)).to_string(), "-0.00", "the bug itself");
        assert_eq!(negate_python(dec!(0.00)).to_string(), "0.00");
        assert_eq!(negate_python(-dec!(0.00)).to_string(), "0.00");
        // Scale survives — `normalize()` would have flattened it to `0`.
        assert_eq!(negate_python(dec!(0.0000)).to_string(), "0.0000");
        // Non-zero negation is untouched.
        assert_eq!(negate_python(dec!(1.25)).to_string(), "-1.25");
        assert_eq!(negate_python(dec!(-1.25)).to_string(), "1.25");
    }

    /// Rounding a small negative to zero must KEEP the sign, as Python's
    /// `quantize` does — the opposite direction from the negation rule above,
    /// which is why one fix could not serve both.
    ///
    /// Expectations taken from `CPython`: `Decimal("-0.00495").quantize(
    /// Decimal("0.01"))` is `-0.00`. bean-query renders `-0.00 USD` for such a
    /// position; rledger rendered `0.00 USD`, which reads as an exactly flat
    /// balance when it is not.
    #[test]
    fn rounding_a_small_negative_to_zero_keeps_the_sign() {
        assert_eq!(dec!(-0.00495).round_dp(2).to_string(), "0.00", "the bug");

        for (value, dp, want) in [
            (dec!(-0.00495), 2, "-0.00"),
            (dec!(-0.004), 2, "-0.00"),
            (dec!(-0.0000001), 2, "-0.00"),
            (dec!(0.00495), 2, "0.00"),
            (dec!(-1.004), 2, "-1.00"),
            (dec!(-0.00495), 5, "-0.00495"),
            (dec!(1), 2, "1.00"),
        ] {
            assert_eq!(
                round_dp_python(value, dp).to_string(),
                want,
                "{value} at {dp}dp",
            );
        }
    }

    /// The checked variants exist so BQL can map a value-range overflow to
    /// NULL instead of panicking (`rust_decimal` panics on raw `+`). That
    /// path had no test — the one behavior the checked form is FOR.
    #[test]
    fn checked_variants_return_none_on_overflow() {
        assert_eq!(checked_add_python_scale(Decimal::MAX, Decimal::MAX), None);
        assert_eq!(checked_sub_python_scale(Decimal::MIN, Decimal::MAX), None);

        // And still compute the ordinary case, with the scale rule applied.
        assert_eq!(
            checked_add_python_scale(dec!(0.00), dec!(1))
                .expect("no overflow")
                .to_string(),
            "1.00"
        );
        assert_eq!(
            checked_sub_python_scale(dec!(1), dec!(0.00))
                .expect("no overflow")
                .to_string(),
            "1.00"
        );
    }

    /// The rescale step must never corrupt a value it cannot widen.
    ///
    /// A sum near `Decimal::MAX` has no room for extra fractional digits, so
    /// the requested scale is unreachable. `Decimal::rescale` is documented
    /// to leave the value alone in that case rather than truncating, and this
    /// pins that we depend on it: if it ever became saturating or truncating,
    /// the failure mode is a silently WRONG money value rather than a panic
    /// or an error, which nothing else here would catch.
    ///
    /// Verified against the real type rather than assumed — `MAX.rescale(2)`
    /// is a no-op returning `79228162514264337593543950335`.
    #[test]
    fn rescale_beyond_capacity_preserves_the_value() {
        let near_max = Decimal::MAX - Decimal::ONE;
        let sum = add_python_scale(near_max, dec!(0.00));

        assert_eq!(
            sum, near_max,
            "a value too large to carry the target scale must keep its VALUE",
        );
        assert_eq!(sum.to_string(), near_max.to_string());
    }

    /// #2404: the exact sum does not depend on the order of its operands,
    /// where a fold of `checked_add_python_scale` does.
    #[test]
    fn exact_sum_is_order_independent_where_the_fold_is_not() {
        let near_max = Decimal::MAX - dec!(10653859.85);
        let slot_order = [near_max, Decimal::MAX, -Decimal::MAX];
        let fold = |values: &[Decimal]| {
            values
                .iter()
                .try_fold(Decimal::ZERO, |acc, v| checked_add_python_scale(acc, *v))
        };
        // Precondition: the fold fails in slot order and succeeds in another,
        // so this pins the order dependence and not a total out of range.
        assert_eq!(fold(&slot_order), None, "the first partial sum overflows");
        assert_eq!(
            fold(&[Decimal::MAX, -Decimal::MAX, near_max]),
            Some(near_max),
            "the same values fold fine in another order"
        );

        assert_eq!(checked_exact_sum_python_scale(slot_order), Some(near_max));
        assert_eq!(
            checked_exact_sum_python_scale([-Decimal::MAX, near_max, Decimal::MAX]),
            Some(near_max)
        );
    }

    /// Only a TOTAL out of range is refused.
    #[test]
    fn exact_sum_refuses_only_an_out_of_range_total() {
        assert_eq!(
            checked_exact_sum_python_scale([Decimal::MAX, dec!(1)]),
            None
        );
        assert_eq!(
            checked_exact_sum_python_scale([Decimal::MIN, dec!(-1)]),
            None
        );
        assert_eq!(
            checked_exact_sum_python_scale([Decimal::MAX, dec!(1), dec!(-1)]),
            Some(Decimal::MAX),
            "a partial sum past MAX is not a total past MAX"
        );
        assert_eq!(
            checked_exact_sum_python_scale(std::iter::empty()),
            Some(Decimal::ZERO)
        );
    }

    /// Where the fold succeeds, the exact sum agrees with it, value AND scale,
    /// so escalating changes nothing but whether an answer exists. Scale is
    /// compared through `to_string`, since `==` ignores it.
    #[test]
    fn exact_sum_agrees_with_the_fold_value_and_scale() {
        for values in [
            vec![dec!(2.00), dec!(-2.00), dec!(1)],
            vec![dec!(1.00), dec!(-1)],
            vec![dec!(0.1), dec!(0.20), dec!(-0.3)],
            vec![dec!(123456.789), dec!(-0.000001), dec!(42)],
            vec![Decimal::MAX, -Decimal::MAX, dec!(0.5)],
        ] {
            let fold = values
                .iter()
                .try_fold(Decimal::ZERO, |acc, v| checked_add_python_scale(acc, *v))
                .expect("fixture folds");
            let exact = checked_exact_sum_python_scale(values.iter().copied()).expect("fits");
            assert_eq!(exact.to_string(), fold.to_string(), "{values:?}");
        }
    }
}
