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
/// It gets there because `BigDecimal`'s division already follows the ideal
/// exponent, not because of any correction applied afterwards. That is a
/// property of a dependency, so it is pinned: a change of library, or a
/// `normalize` added in the name of tidiness, would drop the two places Python
/// keeps in the first case, and this is what would notice.
#[test]
fn the_exact_slow_path_takes_the_same_scale() {
    let units = dec("1000000000000000"); // 1e15; each product below is 5e29
    for (v, python) in [
        ("500000000000000.00", "500000000000000.00"),
        ("500000000000000", "500000000000000"),
    ] {
        assert!(
            dec(v).checked_mul(units).is_none(),
            "premise: the product overflows"
        );
        let share = prorate(dec(v), units, units).expect("representable");
        assert_eq!(share.to_string(), python, "{v} * 1e15 / 1e15");
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
