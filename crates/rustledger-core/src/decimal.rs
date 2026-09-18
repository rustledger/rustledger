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

    // Minimal form first: this is what removes the EXTRA trailing zero in
    // `7 / 2 -> 3.50`. `normalize` never loses value.
    let mut result = quotient.normalize();
    let target = ideal_scale.max(i64::from(result.scale()));

    // `rescale` takes u32 and is a no-op past the mantissa's capacity; the
    // clamp keeps a pathological ideal from wrapping on the cast.
    if let Ok(target) = u32::try_from(target)
        && result.scale() < target
    {
        result.rescale(target);
    }
    Some(result)
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

#[cfg(test)]
mod tests {
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
}
