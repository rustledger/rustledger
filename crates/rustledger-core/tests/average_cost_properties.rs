//! AVERAGE booking's pooled cost is correctly rounded, over arbitrary pools.
//!
//! Lives in `rustledger-core`, beside the code it tests, and not in
//! `rustledger-booking` where it started. `cargo mutants --package
//! rustledger-core` runs only this crate's tests, so from `rustledger-booking`
//! every exactness check it exercises was reported MISSED: the mutant `exact &&`
//! -> `exact ||` in `pool_units` survived the mutation gate while three tests
//! here killed it (#2363). Moving it killed four of the seven survivors.
//!
//! The three that remain are, as far as the analysis goes, equivalent: turning
//! an exactness `==` into `!=` on the sum or the pool total only makes
//! `all_exact` false from the first element on, which forces the escalation, and
//! the escalation is correctly rounded -- only slower. `+` -> `*` in the product
//! check escalates everywhere except where `su + sc == su * sc`, i.e. scales
//! (0,0) and (2,2), and can only mislead on a product that overflows and rounds
//! to exactly scale `su * sc`.
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
//! The reference divides by the units summed EXACTLY, not by the `Decimal`
//! running total. `checked_add` rounds a pool that mixes magnitudes, and a
//! reference built on a wrongly rounded divisor reports a failure that is partly
//! its own (#2363).
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

/// The #2363 pool, against a value computed OUTSIDE this codebase.
///
/// The property test's reference now divides by an exactly-summed denominator,
/// which is the same thing the escalation path does — so for an escalated pool
/// the two agree by construction and the property alone cannot catch a shared
/// mistake. This pins one pool to a number derived from exact rational
/// arithmetic in a separate tool:
///
/// ```text
/// units  = 1 + 0.0000000000007650000000001 + 6888859176335.69 + 79228162514263.4
/// exact total    = 86117021690600.0900000000007650000000001
/// exact quotient = 2983.482410536740787609404852...
/// rounded once   = 2983.4824105367407876094048518
/// ```
///
/// Before #2363 the function answered `...516`, dividing an exact numerator by
/// the caller's already-rounded total, and the property test called `...520`
/// correct while dividing by a total it had rounded differently again.
#[test]
fn the_2363_pool_matches_an_independently_computed_average() {
    let lots: [(&str, &str); 4] = [
        ("1", "0.00000000000000000000000002"),
        ("0.0000000000007650000000001", "1"),
        ("6888859176335.69", "37296.25078478979354335109"),
        ("79228162514263.4", "0.000000000000000000000000020"),
    ];
    let mut inv = Inventory::new();
    let mut total = Decimal::ZERO;
    for (u, c) in lots {
        let units = Decimal::from_str(u).expect("units parse");
        let cost = Decimal::from_str(c).expect("cost parse");
        inv.add(Position::with_cost(
            Amount::new(units, "TKN"),
            Cost::new(cost, "ETH"),
        ))
        .expect("add");
        total = total.checked_add(units).expect("total");
    }

    let r = inv
        .reduce(&Amount::new(-total, "TKN"), None, BookingMethod::Average)
        .expect("reduce");
    let got = r
        .matched
        .first()
        .and_then(|m| m.cost.as_ref())
        .map(|c| c.number)
        .expect("a pooled cost");

    assert_eq!(
        got.to_string(),
        "2983.4824105367407876094048518",
        "the pooled average must match the independently computed value"
    );
}

/// Builds the #2363 pool and returns it with its `Decimal` running total.
fn pool_2363() -> (Inventory, Decimal) {
    let lots: [(&str, &str); 4] = [
        ("1", "0.00000000000000000000000002"),
        ("0.0000000000007650000000001", "1"),
        ("6888859176335.69", "37296.25078478979354335109"),
        ("79228162514263.4", "0.000000000000000000000000020"),
    ];
    let mut inv = Inventory::new();
    let mut total = Decimal::ZERO;
    for (u, c) in lots {
        let units = Decimal::from_str(u).expect("units parse");
        let cost = Decimal::from_str(c).expect("cost parse");
        inv.add(Position::with_cost(
            Amount::new(units, "TKN"),
            Cost::new(cost, "ETH"),
        ))
        .expect("add");
        total = total.checked_add(units).expect("total");
    }
    (inv, total)
}

/// `merge_average` reaches the same average through its own caller, which
/// builds its own pool total. A sabotage check found this path uncovered:
/// telling `weighted_average_cost` the total was always exact, from this caller
/// alone, left every test green.
#[test]
fn merge_average_on_the_2363_pool_matches_the_independent_value() {
    let (mut inv, _) = pool_2363();
    inv.merge_average().expect("merge");
    let costs: Vec<String> = inv
        .positions()
        .filter_map(|p| p.cost.as_ref())
        .map(|c| c.number.to_string())
        .collect();
    assert_eq!(costs, vec!["2983.4824105367407876094048518".to_string()]);
}

/// The `{*}` merge path (`plan_merge`, via `merged_pool_cost`) the same way.
/// It computed its total with `Decimal`'s panicking `Sum` until this change,
/// and it was uncovered in the same way as `merge_average`.
#[test]
fn a_star_merge_on_the_2363_pool_matches_the_independent_value() {
    let (inv, total) = pool_2363();
    let pool = inv
        .merged_pool_cost(&Amount::new(-total, "TKN"))
        .expect("plan")
        .expect("a costed pool");
    assert_eq!(pool.number.to_string(), "2983.4824105367407876094048518");
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

        // The other two entry points see the SAME pool, so snapshot it before
        // `reduce` changes it.
        let for_merge = inv.clone();
        let for_plan = inv.clone();

        let Ok(r) = inv.reduce(&Amount::new(-total, "TKN"), None, BookingMethod::Average) else {
            return Ok(());
        };
        let got = r.matched.first().and_then(|m| m.cost.as_ref()).map(|c| c.number);
        prop_assume!(got.is_some());
        let got = got.expect("assumed");

        // The DENOMINATOR has to be exact too. `total` above is accumulated
        // with `checked_add`, which rounds when the pool mixes magnitudes, so
        // using it here compared the function against a reference built from a
        // wrongly rounded divisor: on the #2363 pool the reference was itself 2
        // units in the last place off the true average, in the opposite
        // direction to the function's own error. Summed exactly instead.
        let exact_total: BigDecimal = pooled.iter().map(|(u, _)| to_bigdecimal(*u)).sum();
        let exact: BigDecimal = pooled
            .iter()
            .map(|(u, c)| to_bigdecimal(*u) * to_bigdecimal(*c))
            .sum::<BigDecimal>()
            / exact_total;
        let Ok(want) = Decimal::from_str(&exact.to_plain_string()) else {
            return Ok(()); // not representable at all; the function reports it
        };

        let ulp = BigDecimal::new(bigdecimal::num_bigint::BigInt::from(1), i64::from(want.scale()));
        prop_assert!(
            (to_bigdecimal(got) - to_bigdecimal(want)).abs() <= ulp,
            "got {got}, correctly rounded {want}"
        );

        // `merge_average` and the `{*}` path build their own pool totals, and
        // the fix routes all three through one helper. The pinned #2363 tests
        // cover one pool each; this holds them to the same bar on every pool.
        let mut merged = for_merge;
        if merged.merge_average().is_ok() {
            let costs: Vec<Decimal> = merged
                .positions()
                .filter_map(|p| p.cost.as_ref())
                .map(|c| c.number)
                .collect();
            if let [only] = costs.as_slice() {
                prop_assert!(
                    (to_bigdecimal(*only) - to_bigdecimal(want)).abs() <= ulp,
                    "merge_average got {only}, correctly rounded {want}"
                );
            }
        }
        if let Ok(Some(pool)) = for_plan.merged_pool_cost(&Amount::new(-total, "TKN")) {
            prop_assert!(
                (to_bigdecimal(pool.number) - to_bigdecimal(want)).abs() <= ulp,
                "merged_pool_cost got {}, correctly rounded {want}",
                pool.number
            );
        }
    }
}
