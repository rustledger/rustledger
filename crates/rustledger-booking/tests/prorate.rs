//! `prorate` must be exact where it can be, correctly rounded where it
//! cannot, and must never hand back a number that is simply wrong (#2346).

use rustledger_booking::prorate;
use rustledger_core::Decimal;

fn dec(s: &str) -> Decimal {
    Decimal::from_str_exact(s).expect("literal parses")
}

#[test]
fn multiplies_first_so_a_whole_share_stays_exact() {
    // The reason multiply-before-divide is the fast path. Dividing first gives
    // 0.333...(28 digits), and multiplying back by 3 lands on 0.999...9 — a
    // share of the WHOLE that is not the whole.
    assert_eq!(
        prorate(Decimal::ONE, Decimal::from(3), Decimal::from(3)),
        Some(Decimal::ONE)
    );
    assert_eq!(
        prorate(Decimal::from(10), Decimal::from(3), Decimal::from(4)),
        Some(dec("7.5"))
    );
}

#[test]
fn computes_a_share_whose_intermediate_product_overflows() {
    let value = dec("500000000000000"); // 5e14
    let units = dec("1000000000000000"); // 1e15
    assert!(
        value.checked_mul(units).is_none(),
        "the premise of this test is that the PRODUCT does not fit"
    );

    let share = prorate(value, units, units).expect("a representable share");
    assert_eq!(share, value);
    // On the rendering, not just the value: `Decimal` equality ignores scale,
    // so `assert_eq!` alone passed while the first version returned
    // `500000000000000.00` — two trailing zeros its divide-first fallback
    // invented. They would reach the capgains CSV and JSON exports, which emit
    // the `Decimal` verbatim; TEXT renders through `DisplayContext` at display
    // precision and would not show them.
    assert_eq!(share.to_string(), "500000000000000");
}

/// The bug in the first version of this function, and the reason it is not a
/// divide-first fallback.
///
/// When the product overflows, dividing first can UNDERFLOW: `2 / MAX` is
/// about `2.5e-29`, below `Decimal`'s `1e-28` floor, so it becomes zero and the
/// share comes back `Some(0)`. Not an error — a wrong answer, presented as
/// valid. Each operand order fails on one of these two inputs, so both are
/// pinned.
#[test]
fn never_returns_an_underflowed_zero_for_a_nonzero_share() {
    assert_eq!(
        prorate(Decimal::from(2), Decimal::MAX, Decimal::MAX),
        Some(Decimal::from(2)),
        "dividing `value` first underflows here"
    );
    assert_eq!(
        prorate(Decimal::MAX, Decimal::from(2), Decimal::MAX),
        Some(Decimal::from(2)),
        "dividing `num` first underflows here"
    );
}

#[test]
fn refuses_rather_than_inventing_a_share() {
    assert_eq!(
        prorate(Decimal::ONE, Decimal::ONE, Decimal::ZERO),
        None,
        "a zero denominator has no share to report"
    );
    assert_eq!(
        prorate(Decimal::MAX, Decimal::MAX, Decimal::ONE),
        None,
        "a share beyond Decimal's range is refused, not clamped"
    );
}

/// EXACT shares take Python's ideal-exponent scale, `value.scale() +
/// num.scale() - den.scale()`, on the fast path (#2349).
///
/// Every expected string here was produced by Python's `decimal`, not written
/// by hand. The first two are the cases `rust_decimal` got wrong on its own —
/// its division keeps a non-minimal scale for an exact quotient — and the last
/// two are cases where it already agreed, pinned so that a fix for the first
/// pair cannot strip scale the user actually wrote.
#[test]
fn shares_take_pythons_ideal_exponent_scale() {
    for (v, n, d, python) in [
        ("900", "1", "1000", "0.9"),    // rust_decimal alone: 0.90
        ("10", "3", "4", "7.5"),        // rust_decimal alone: 7.50
        ("100.00", "1", "1", "100.00"), // ideal scale 2 is KEPT, not normalized away
        ("1.50", "2", "3", "1.00"),
    ] {
        let share = prorate(dec(v), dec(n), dec(d)).expect("representable");
        assert_eq!(share.to_string(), python, "{v} * {n} / {d}");
    }
}

/// ...and so does the exact `BigDecimal` path, which cannot reach
/// `checked_div_python_scale` because its product does not fit in a `Decimal`.
///
/// It gets there through `with_ideal_scale`, applied to an exact share. It does
/// NOT get there on its own: `BigDecimal`'s division happens to land on the
/// ideal exponent at small scales (the first two rows would pass without the
/// helper), which is what a nine-case sample once suggested, but the third row
/// — an ordinary 18-decimal token split — comes out `0.25` where Python gives
/// `0.250000000000000000`. All expected values are Python's.
#[test]
fn the_exact_slow_path_takes_the_same_scale() {
    for (v, n, d, python) in [
        // Product 5e29: overflows.
        (
            "500000000000000.00",
            "1000000000000000",
            "1000000000000000",
            "500000000000000.00",
        ),
        (
            "500000000000000",
            "1000000000000000",
            "1000000000000000",
            "500000000000000",
        ),
        // Product needs 36 decimal places: rounded, so not exact.
        (
            "0.500000000000000000",
            "1.000000000000000000",
            "2.000000000000000000",
            "0.250000000000000000",
        ),
    ] {
        let product = dec(v).checked_mul(dec(n));
        assert!(
            product.is_none_or(|p| p.scale() != dec(v).scale() + dec(n).scale()),
            "premise: {v} * {n} cannot take the fast path"
        );
        let share = prorate(dec(v), dec(n), dec(d)).expect("representable");
        assert_eq!(share.to_string(), python, "{v} * {n} / {d}");
    }
}

/// An INEXACT share keeps `rust_decimal`'s precision, which is a deliberate
/// deviation from Python and is pinned as one (CLAUDE.md, "Checklist for a
/// deliberate Python deviation").
///
/// Python rounds these to its 28-significant-digit context; `rust_decimal`
/// keeps up to 29. #2349's scale fix must not reach into them: the
/// ideal-exponent step only strips trailing zeros, and an inexact
/// `rust_decimal` quotient never has one. If this ever fails because someone
/// switched to Python's 28-digit rounding, that is a behavior change to make on
/// purpose, not a side effect to accept.
#[test]
fn inexact_shares_keep_rust_decimals_precision() {
    for (v, n, d, rledger, python) in [
        (
            "100",
            "1",
            "3",
            "33.333333333333333333333333333",
            "33.33333333333333333333333333",
        ),
        (
            "900",
            "1",
            "7",
            "128.57142857142857142857142857",
            "128.5714285714285714285714286",
        ),
        (
            "10.00",
            "1",
            "3",
            "3.3333333333333333333333333333",
            "3.333333333333333333333333333",
        ),
    ] {
        let share = prorate(dec(v), dec(n), dec(d)).expect("representable");
        assert_eq!(share.to_string(), rledger, "{v} * {n} / {d}");
        assert_ne!(
            share.to_string(),
            python,
            "this pins the deviation, not agreement"
        );
    }
}

/// A NEGATIVE ideal scale — a divisor finer than the dividend — is where Python
/// switches to exponent form and `rust_decimal`, which has no negative scale,
/// cannot follow. Pinned as a deliberate deviation.
///
/// This is not exotic: a whole-number `@@` total split across lots of `1` and
/// `0.5` units divides by `1.5`. Python's `decimal` measured `6.0E+2` and
/// `1.80E+3` for these; the values match, the representation cannot.
#[test]
fn a_negative_ideal_scale_is_written_out_not_in_exponent_form() {
    for (v, n, d, rledger, python) in [
        ("900", "1", "1.5", "600", "6.0E+2"),
        ("900", "1", "0.5", "1800", "1.80E+3"),
    ] {
        let share = prorate(dec(v), dec(n), dec(d)).expect("representable");
        assert_eq!(share.to_string(), rledger, "{v} * {n} / {d}");
        assert_ne!(
            share.to_string(),
            python,
            "this pins the deviation, not agreement"
        );
    }
}

/// The bottom of the range, on the FAST path.
///
/// `checked_mul` does not fail when the product needs more than 28 decimal
/// places; it rounds and returns `Some`, and for a small product that rounding
/// is to zero. Before the exactness check these came back `Some(0)` — a
/// representable share presented as nothing. The expected values are Python's
/// `decimal` at 60 digits of precision. The second row is 18-decimal token
/// dust, the shape an ERC-20 ledger produces.
#[test]
fn a_product_rounded_to_zero_does_not_become_a_zero_share() {
    for (v, n, d, python) in [
        (
            "0.0000000000000001",
            "0.0000000000001",
            "0.0000000001",
            "0.0000000000000000001",
        ),
        (
            "0.000000000000000001",
            "0.00000000001",
            "0.00000000001",
            "0.000000000000000001",
        ),
        (
            "0.00000000000000015",
            "0.0000000000001",
            "0.0000000001",
            "0.00000000000000000015",
        ),
    ] {
        assert!(
            dec(v).checked_mul(dec(n)).is_some_and(|p| p.is_zero()),
            "premise: checked_mul silently rounds {v} * {n} to zero"
        );
        let share = prorate(dec(v), dec(n), dec(d)).expect("representable");
        assert_eq!(share, dec(python), "{v} * {n} / {d}");
        assert!(!share.is_zero());
    }
}

/// The exact path gives only an EXACT share the ideal scale. An inexact one
/// keeps its rounded digits, trailing zeros included.
///
/// `with_ideal_scale` normalizes first, which is right for an exact share and
/// wrong for an inexact one: the zeros at the end of a rounded result are the
/// rounding, not padding. About one inexact exact-path share in ten ends in a
/// zero (1,978 of 19,997 measured on this shape). This one is correctly rounded
/// at 28 places; Python, which rounds the product and then the quotient to 28
/// significant digits, prints the same value at 27 (`0.250000000002500000250000000`).
/// Without the exactness gate, `with_ideal_scale` normalizes it and re-pads to
/// the ideal scale, giving `0.25000000000250000025000000000`: the same value,
/// but its trailing zeros would then be padding rather than rounding, a claim
/// of precision the computation never had.
#[test]
fn an_inexact_exact_path_share_keeps_its_rounded_digits() {
    let (v, n, d) = (dec("1.000000000000000001"), dec("1.00000000001"), dec("4"));
    assert!(
        v.checked_mul(n)
            .is_none_or(|p| p.scale() != v.scale() + n.scale()),
        "premise: 18 + 11 decimal places cannot take the fast path"
    );
    let share = prorate(v, n, d).expect("representable");
    assert_eq!(share.to_string(), "0.2500000000025000002500000000");
}

/// A realistic path to an out-of-range scale, pinned end to end.
///
/// 18-decimal lots sold by a posting written with one decimal place
/// (`-2.5 TKN`), at an ETH total under 1: the ideal scale is `18 + 18 - 1 =
/// 35`. Without the cap in `with_ideal_scale` the share came back at scale 29,
/// a value `rust_decimal`'s `from_parts` panics on. It is rebuilt from its own
/// parts here because that is the operation that would panic downstream.
#[test]
fn a_huge_ideal_scale_yields_a_valid_decimal() {
    let share = prorate(
        dec("0.623456789012345678"),
        dec("1.250000000000000000"),
        dec("2.5"),
    )
    .expect("representable");
    assert_eq!(share, dec("0.311728394506172839"), "value is exact");
    assert!(
        share.scale() <= Decimal::MAX_SCALE,
        "scale {}",
        share.scale()
    );
    let m = share.mantissa().unsigned_abs();
    #[allow(clippy::cast_possible_truncation)]
    let rebuilt = Decimal::from_parts(
        m as u32,
        (m >> 32) as u32,
        (m >> 64) as u32,
        false,
        share.scale(),
    );
    assert_eq!(rebuilt, share);
}
