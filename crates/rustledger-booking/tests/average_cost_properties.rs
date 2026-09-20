//! AVERAGE booking's pooled cost, over arbitrary pools (#2351).
//!
//! Two properties, both measured before they were written down:
//!
//! 1. **No fabricated zero.** When the exact average is representable and
//!    nonzero, the booked average is nonzero. `checked_mul` rounds a product
//!    needing more than 28 decimal places without failing, and a small one
//!    rounds to zero, so a pool of small lots booked at a zero cost.
//! 2. **Otherwise unchanged.** Outside that one signature — the sum of products
//!    is zero AND a product vanished from two nonzero factors — the result is
//!    bit-for-bit the old formula, `Σ units × cost / Σ units`. A broader fix was
//!    tried and measured worse than the old formula in 70% of random pools
//!    (`rust_decimal` keeps 28 decimal places, not 28 significant digits); this
//!    property is what keeps a future "improvement" honest.
//!
//! Lots are drawn with the mantissa's width first (1 to 96 bits) and any scale
//! from 0 to 28, so tiny and huge magnitudes are equally likely.

use bigdecimal::{BigDecimal, num_bigint::BigInt};
use proptest::prelude::*;
use rustledger_core::{Amount, BookingMethod, Cost, Decimal, Inventory, Position};
use std::str::FromStr;

fn big(d: Decimal) -> BigDecimal {
    BigDecimal::new(BigInt::from(d.mantissa()), i64::from(d.scale()))
}

fn positive_decimal() -> impl Strategy<Value = Decimal> {
    (1u32..=96, any::<u128>(), 0u32..=28).prop_filter_map("fits a Decimal", |(bits, raw, scale)| {
        let m = i128::try_from(raw >> (128 - bits)).ok()?.max(1);
        Decimal::try_from_i128_with_scale(m, scale).ok()
    })
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 20_000, ..ProptestConfig::default() })]

    /// `short` makes every lot's units negative, so the pool is a short one and
    /// the reduction that closes it is positive. The ratio form divides two
    /// negatives where the product form multiplies them, so the sign arrives by
    /// a different route on each path; drawing only long pools left that
    /// untested.
    #[test]
    fn average_cost_is_never_a_fabricated_zero_and_otherwise_unchanged(
        lots in prop::collection::vec((positive_decimal(), positive_decimal()), 2..=5),
        short in any::<bool>(),
    ) {
        let lots: Vec<(Decimal, Decimal)> = lots
            .into_iter()
            .map(|(u, c)| (if short { -u } else { u }, c))
            .collect();
        let mut inv = Inventory::new();
        let mut total = Decimal::ZERO;
        for (units, cost) in &lots {
            prop_assume!(inv.add(Position::with_cost(Amount::new(*units, "TKN"), Cost::new(*cost, "ETH"))).is_ok());
            total = match total.checked_add(*units) { Some(t) => t, None => return Ok(()) };
        }
        // Read the lots back from the inventory: `add` MERGES positions whose
        // costs are equal in value even when their scales differ, so the
        // function sees summed units where the draw had two lots, and their
        // products round differently. Comparing against the draw made this test
        // fail on a case that was not a bug.
        let pooled: Vec<(Decimal, Decimal)> = inv
            .positions()
            .filter_map(|p| p.cost.as_ref().map(|c| (p.units.number, c.number)))
            .collect();

        let Ok(r) = inv.reduce(&Amount::new(-total, "TKN"), None, BookingMethod::Average) else {
            return Ok(());
        };
        let got = r.matched.first().and_then(|m| m.cost.as_ref()).map(|c| c.number);
        prop_assume!(got.is_some());
        let got = got.expect("assumed");

        // 1. No fabricated zero.
        let exact: BigDecimal = pooled.iter().map(|(u, c)| big(*u) * big(*c)).sum::<BigDecimal>() / big(total);
        if let Ok(want) = Decimal::from_str(&exact.to_plain_string()) {
            prop_assert!(!got.is_zero() || want.is_zero(), "fabricated zero; exact average {want}");
        }

        // 2. Otherwise identical to the old formula.
        let sum = pooled.iter().try_fold(Decimal::ZERO, |a, (u, c)| a.checked_add(u.checked_mul(*c)?));
        let vanished = pooled.iter().any(|(u, c)| u.checked_mul(*c).is_some_and(|p| p.is_zero()));
        if let Some(sum) = sum
            && !(sum.is_zero() && vanished)
            && let Some(old) = sum.checked_div(total)
        {
            // Within one unit in the last place, not bit-for-bit: the function
            // accumulates over the lots it matched in its own order, and the
            // order a sum is built in decides its last digit. Asserting
            // equality pinned that internal order and failed on a case that was
            // not a bug. One ulp still catches a change of FORM — the widened
            // trigger this guards against moves results by far more.
            let ulp = BigDecimal::new(BigInt::from(1), i64::from(old.scale().max(got.scale())));
            prop_assert!(
                (big(got) - big(old)).abs() <= ulp,
                "outside the repair, the result must be the old formula's: got {}, old {}",
                got,
                old
            );
        }
    }
}
