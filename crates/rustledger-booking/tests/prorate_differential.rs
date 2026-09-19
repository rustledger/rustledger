//! `prorate` against an exact reference, across the whole input space.
//!
//! Every earlier review of `prorate` found its bugs by hand-picking inputs,
//! and each round's sample turned out narrower than its conclusion. This asks
//! the question for arbitrary inputs instead: mantissas of 1 to 96 bits, every
//! scale from 0 to 28, both signs. The reference forms `value * num / den`
//! exactly in `BigDecimal` and rounds it once into a `Decimal`.
//!
//! As an exploratory sweep over 1.5 million triples this found nothing on the
//! current code, and, with the exactness guard removed, it reported both
//! fabricated zeros and wrong nonzero shares — one off from the 13th
//! significant digit (`0.0000444905880782270215971873` for
//! `0.0000444905880781070147260043`). So it can report dirty.
//!
//! Limitation: the reference shares the slow path's final conversion
//! (`Decimal::from_str` on the plain string), so it cannot catch an error in
//! that one step. The conversion's rounding was checked separately against
//! hand-computed ties and against `MAX`.

use bigdecimal::{BigDecimal, num_bigint::BigInt};
use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_booking::prorate;
use std::str::FromStr;

fn big(d: Decimal) -> BigDecimal {
    BigDecimal::new(BigInt::from(d.mantissa()), i64::from(d.scale()))
}

/// Exact quotient, rounded once into `Decimal`; `None` where it cannot fit.
fn reference(v: Decimal, n: Decimal, d: Decimal) -> Option<Decimal> {
    if d.is_zero() {
        return None;
    }
    Decimal::from_str(&(big(v) * big(n) / big(d)).to_plain_string()).ok()
}

/// Any `Decimal`: the mantissa's width is drawn first, so small and huge
/// magnitudes are equally likely instead of almost everything being ~2^96.
fn decimal() -> impl Strategy<Value = Decimal> {
    (1u32..=96, any::<u128>(), any::<bool>(), 0u32..=28).prop_filter_map(
        "fits a Decimal",
        |(bits, raw, negative, scale)| {
            let m = i128::try_from(raw >> (128 - bits)).ok()?;
            Decimal::try_from_i128_with_scale(if negative { -m } else { m }, scale).ok()
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 20_000, ..ProptestConfig::default() })]

    #[test]
    fn prorate_matches_an_exactly_rounded_reference(v in decimal(), n in decimal(), d in decimal()) {
        let got = prorate(v, n, d);
        let want = reference(v, n, d);
        match (got, want) {
            (None, None) => {}
            (None, Some(w)) => prop_assert!(false, "refused a representable share {w}"),
            (Some(g), None) => prop_assert!(false, "invented a share {g} that cannot be represented"),
            (Some(g), Some(w)) => {
                prop_assert!(g.scale() <= Decimal::MAX_SCALE, "invalid scale {}", g.scale());
                prop_assert!(!g.is_zero() || w.is_zero(), "fabricated zero; want {w}");
                // Equal, or one unit in the reference's last place: the fast
                // path's division breaks ties to even, the conversion away
                // from zero.
                let ulp = BigDecimal::new(BigInt::from(1), i64::from(w.scale()));
                prop_assert!((big(g) - big(w)).abs() <= ulp, "got {g}, want {w}");
            }
        }
    }
}
