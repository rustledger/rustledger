//! AVERAGE booking's pooled cost is correctly rounded, over arbitrary pools.
//!
//! One property now, where there used to be two: the booked average equals the
//! exact `Σ units × cost / Σ units` rounded once into a `Decimal`. That is
//! stronger than what this test asserted while the fix was a heuristic — then it
//! could only claim "no fabricated zero, and otherwise bit-for-bit the old
//! formula" (#2351), because every `Decimal`-only form is wrong on one
//! population or the other. The exact escalation (#2353) has no population it
//! is wrong on, so the test says so directly.
//!
//! One unit in the last place is allowed: the fast path's division breaks ties
//! to even and the escalation's conversion breaks them away from zero.
//!
//! Lots are drawn with the mantissa's width first (1 to 96 bits) and any scale
//! from 0 to 28, so tiny and huge magnitudes are equally likely, and `short`
//! flips the pool's direction — the sign arrives by a different route on each
//! tier.

use bigdecimal::BigDecimal;
use proptest::prelude::*;
use rustledger_core::{Amount, BookingMethod, Cost, Decimal, Inventory, Position, to_bigdecimal};
use std::str::FromStr;

fn positive_decimal() -> impl Strategy<Value = Decimal> {
    (1u32..=96, any::<u128>(), 0u32..=28).prop_filter_map("fits a Decimal", |(bits, raw, scale)| {
        let m = i128::try_from(raw >> (128 - bits)).ok()?.max(1);
        Decimal::try_from_i128_with_scale(m, scale).ok()
    })
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 20_000, ..ProptestConfig::default() })]

    #[test]
    fn average_cost_is_correctly_rounded(
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
            prop_assume!(
                inv.add(Position::with_cost(Amount::new(*units, "TKN"), Cost::new(*cost, "ETH")))
                    .is_ok()
            );
            total = match total.checked_add(*units) {
                Some(t) => t,
                None => return Ok(()),
            };
        }
        prop_assume!(!total.is_zero());

        // Read the lots back: `add` MERGES positions whose costs are equal in
        // value and differ only in scale, so the function sees summed units
        // where the draw had two lots.
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

        let exact: BigDecimal = pooled
            .iter()
            .map(|(u, c)| to_bigdecimal(*u) * to_bigdecimal(*c))
            .sum::<BigDecimal>()
            / to_bigdecimal(total);
        let Ok(want) = Decimal::from_str(&exact.to_plain_string()) else {
            return Ok(()); // not representable at all; the function reports it
        };

        let ulp = BigDecimal::new(bigdecimal::num_bigint::BigInt::from(1), i64::from(want.scale()));
        prop_assert!(
            (to_bigdecimal(got) - to_bigdecimal(want)).abs() <= ulp,
            "got {got}, correctly rounded {want}"
        );
    }
}
