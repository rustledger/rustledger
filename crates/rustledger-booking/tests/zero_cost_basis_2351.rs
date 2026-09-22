//! A small lot must not be booked at a zero cost basis (#2351).
//!
//! Both sites computed a cost from an intermediate product that `checked_mul`
//! rounds to 28 decimal places without failing. For a small lot that product
//! rounds to zero, and the cost it was headed for — perfectly representable —
//! came out `0`: a zero cost basis on a real holding, so every later sale of it
//! reads as pure gain. Expected values are Python's `decimal` at 60 digits.

use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, BookingMethod, Cost, CostNumber, CostSpec, Decimal, Inventory, Position, Posting,
    Transaction,
};
use std::str::FromStr;

fn dec(s: &str) -> Decimal {
    Decimal::from_str(s).expect("literal parses")
}

/// AVERAGE booking pooled `Σ units × cost / Σ units`. Each product here is
/// below `Decimal`'s `1e-28` floor, so the sum was `0` and the pool's average
/// cost booked as `0`.
#[test]
fn average_cost_of_small_lots_is_not_zero() {
    let units = dec("0.00000000001");
    assert!(
        units
            .checked_mul(dec("0.000000000000000001"))
            .is_some_and(|p| p.is_zero()),
        "premise: the product rounds to zero"
    );
    let mut inv = Inventory::new();
    inv.add(Position::with_cost(
        Amount::new(units, "TKN"),
        Cost::new(dec("0.000000000000000001"), "ETH"),
    ))
    .expect("first lot");
    inv.add(Position::with_cost(
        Amount::new(units, "TKN"),
        Cost::new(dec("0.000000000000000003"), "ETH"),
    ))
    .expect("second lot");

    let r = inv
        .reduce(
            &Amount::new(-(units + units), "TKN"),
            None,
            BookingMethod::Average,
        )
        .expect("the pool reduces");
    let avg = r.matched[0].cost.as_ref().expect("an averaged lot").number;
    assert_eq!(avg, dec("0.000000000000000002"), "(1e-29 + 3e-29) / 2e-11");
}

/// A compound `{a # b}` per-unit was `(N·a + b) / N` in the booker, while
/// `CostSpec::resolve` computed `a + b / N`. With `N·a` below the floor the
/// booker's form was `0 / N`.
#[test]
fn compound_per_unit_of_a_small_lot_is_not_zero() {
    let spec = CostSpec::empty()
        .with_number(CostNumber::Compound {
            per_unit: dec("0.000000000000000001"),
            total: Decimal::ZERO,
        })
        .with_currency("ETH");
    let txn = Transaction::new(
        rustledger_core::naive_date(2024, 1, 1).expect("date"),
        "compound",
    )
    .with_synthesized_posting(
        Posting::new("Assets:Token", Amount::new(dec("0.00000000001"), "TKN")).with_cost(spec),
    )
    .with_synthesized_posting(Posting::auto("Assets:Cash"));

    let booked = BookingEngine::new().book(&txn).expect("books");
    let cost = booked.transaction.postings[0]
        .cost
        .as_ref()
        .expect("cost filled");
    match cost.number {
        Some(CostNumber::PerUnitFromTotal(booked_cost)) => {
            assert_eq!(
                booked_cost.per_unit,
                dec("0.000000000000000001"),
                "a + b/N with b = 0 is a"
            );
        }
        ref other => panic!("expected a booked cost, got {other:?}"),
    }
}

/// The booker and `CostSpec::resolve` must agree on a compound cost, because
/// they disagreeing is how this bug arose. Checked on an ordinary cost and on
/// the small lot above.
#[test]
fn the_booker_and_resolve_agree_on_compound_per_unit() {
    for (units, a, b) in [
        ("3", "10.5", "7"),
        ("0.00000000001", "0.000000000000000001", "0"),
    ] {
        let spec = CostSpec::empty()
            .with_number(CostNumber::Compound {
                per_unit: dec(a),
                total: dec(b),
            })
            .with_currency("ETH");
        let date = rustledger_core::naive_date(2024, 1, 1).expect("date");
        let resolved = spec.resolve(dec(units), date).expect("resolves").number;

        let txn = Transaction::new(date, "compound")
            .with_synthesized_posting(
                Posting::new("Assets:Token", Amount::new(dec(units), "TKN")).with_cost(spec),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));
        let booked = BookingEngine::new().book(&txn).expect("books");
        let Some(CostNumber::PerUnitFromTotal(booked_cost)) = booked.transaction.postings[0]
            .cost
            .as_ref()
            .and_then(|c| c.number)
        else {
            panic!("expected a booked cost for {units} {{{a} # {b}}}");
        };
        assert_eq!(booked_cost.per_unit, resolved, "{units} {{{a} # {b}}}");
    }
}

/// A pool holding BOTH directions of the same commodity, through the exact
/// escalation (#2353).
///
/// The property test draws pools whose lots share a sign, so this regime, a
/// positive lot and a negative one averaged together, had no coverage, and it
/// is where a weighted average is least intuitive: the numerator is a
/// difference of products, not a sum of like terms. 18-decimal costs make
/// every product need 36 places, so this goes through `BigDecimal` rather than
/// the fast path.
///
/// Reached through `merge_average`, the realization of a SUM of an AVERAGE
/// account's postings, where a sale is a negative lot at the pool's cost and
/// is netted in. It used to be reached through an AVERAGE reduction over a
/// long and a short, but that pooling was the bug (#2393): a reduction takes
/// only the side opposite its sign, so the same inventory now sells from the
/// long lot at its own cost, which this also pins.
#[test]
fn a_mixed_sign_pool_is_correctly_rounded_through_the_escalation() {
    use bigdecimal::BigDecimal;
    use rustledger_core::{Inventory, to_bigdecimal};

    let (u1, c1) = (dec("1.234567890123456789"), dec("0.000000000000000002"));
    let (u2, c2) = (dec("-0.234567890123456789"), dec("0.000000000000000003"));
    assert!(
        u1.checked_mul(c1)
            .is_some_and(|p| p.scale() != u1.scale() + c1.scale()),
        "premise: the product cannot be exact, so the escalation runs"
    );

    let lots = || {
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(u1, "TKN"),
            Cost::new(c1, "ETH"),
        ))
        .expect("long lot");
        inv.add(Position::with_cost(
            Amount::new(u2, "TKN"),
            Cost::new(c2, "ETH"),
        ))
        .expect("negative lot");
        inv
    };
    let total = u1 + u2;

    let mut merged = lots();
    merged.merge_average().expect("merges");
    let got = merged
        .positions()
        .find(|p| p.units.currency == "TKN")
        .and_then(|p| p.cost.as_ref())
        .expect("one averaged lot")
        .number;
    let exact: BigDecimal = (to_bigdecimal(u1) * to_bigdecimal(c1)
        + to_bigdecimal(u2) * to_bigdecimal(c2))
        / to_bigdecimal(total);
    let want = Decimal::from_str(&exact.to_plain_string()).expect("representable");
    assert_eq!(got, want, "exact average of a positive and a negative lot");

    // The reduction, by contrast, takes from the long side alone.
    let mut sold = lots();
    let r = sold
        .reduce(&Amount::new(-total, "TKN"), None, BookingMethod::Average)
        .expect("the long side holds more than `total`");
    let sold_at = r.matched[0].cost.as_ref().expect("a costed lot").number;
    assert_eq!(
        sold_at, c1,
        "a sale is priced from the long pool only (#2393)"
    );
}
