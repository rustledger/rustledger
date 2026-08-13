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

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    /// The exact shape `rust_decimal` gets wrong: a zero operand's scale is
    /// dropped. Both orders, since its zero shortcut applies to either side.
    #[test]
    fn a_zero_operand_keeps_its_scale() {
        assert_eq!(add_python_scale(dec!(0.00), dec!(1)), dec!(1.00));
        assert_eq!(add_python_scale(dec!(1), dec!(0.00)), dec!(1.00));
        assert_eq!(sub_python_scale(dec!(0.00), dec!(1)), dec!(-1.00));
        assert_eq!(sub_python_scale(dec!(1), dec!(0.00)), dec!(1.00));
    }

    /// `assert_eq!` on `Decimal` compares VALUE, not scale — `dec!(1)` and
    /// `dec!(1.00)` are equal to it. Every assertion above would therefore
    /// pass against plain `+`, which is the bug. Assert on the rendered
    /// string, which is what the divergence is actually about.
    #[test]
    fn scale_is_asserted_on_the_rendering_not_the_value() {
        assert_eq!(dec!(1), dec!(1.00), "precondition: == ignores scale");

        assert_eq!(add_python_scale(dec!(0.00), dec!(1)).to_string(), "1.00");
        assert_eq!((dec!(0.00) + dec!(1)).to_string(), "1", "the bug itself");
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
}
