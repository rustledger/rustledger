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
    // `500000000000000.00` — two trailing zeros the division invented, which a
    // capital-gains report would print.
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
