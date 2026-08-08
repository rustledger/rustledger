//! `apply` must report a failed reduction, not assert in one build profile and
//! ignore it in the other (#1987).

use rustledger_booking::BookingEngine;
use rustledger_core::{Amount, BookingMethod, CostNumber, CostSpec, Decimal, Posting, Transaction};

/// A resolved per-unit cost spec, as booking would leave it.
fn spec(number: &str, cur: &str, day: u32) -> CostSpec {
    CostSpec {
        number: Some(CostNumber::PerUnit {
            value: number.parse::<Decimal>().unwrap(),
        }),
        currency: Some(cur.into()),
        date: Some(date(day)),
        label: None,
        merge: false,
    }
}

fn date(d: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(2024, 1, d).unwrap()
}

fn amount(n: &str, cur: &str) -> Amount {
    Amount::new(n.parse::<Decimal>().unwrap(), cur)
}

/// An EMPTY cost spec is what an unbooked reduction looks like.
///
/// `{}` is resolved by the booking phase; a transaction that reaches `apply`
/// still carrying one is by definition unbooked. Under STRICT with two lots
/// standing, it is ambiguous — the #1987 shape.
const fn empty_spec() -> CostSpec {
    CostSpec {
        number: None,
        currency: None,
        date: None,
        label: None,
        merge: false,
    }
}

/// Seed two lots at different costs, applied normally.
fn engine_with_two_lots() -> BookingEngine {
    let mut engine = BookingEngine::with_method(BookingMethod::Strict);
    // The cash leg is derived from the lot rather than hard-coded: Copilot
    // caught both buys paying -1500.00 while the second is 10 @ 200.00. `apply`
    // does not check balance today, so nothing failed — which is exactly why an
    // internally inconsistent fixture is worth fixing before it becomes load-
    // bearing for a test that does.
    for (day, units, cost) in [(5u32, "10", "150.00"), (6, "10", "200.00")] {
        let mut buy = Posting::new("Assets:Broker", amount(units, "AAPL"));
        buy.cost = Some(spec(cost, "USD", day));
        let paid = -(units.parse::<Decimal>().unwrap() * cost.parse::<Decimal>().unwrap());
        let txn = Transaction::new(date(day), "buy")
            .with_synthesized_posting(buy)
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(paid, "USD")));
        engine.apply(&txn).expect("an augmentation applies");
    }
    engine
}

/// An ambiguous reduction is REPORTED, not asserted-then-ignored.
///
/// This used to be `debug_assert!` followed by `let _ = reduced`, so the two
/// build profiles disagreed about a user's ledger: debug PANICKED, release
/// dropped the reduction and over-stated the holding. This test runs in both
/// and expects the same answer from each.
#[test]
fn an_ambiguous_reduction_is_reported() {
    let mut engine = engine_with_two_lots();

    let mut sell = Posting::new("Assets:Broker", amount("-5", "AAPL"));
    sell.cost = Some(empty_spec());
    let txn = Transaction::new(date(10), "sell 5")
        .with_synthesized_posting(sell)
        .with_synthesized_posting(Posting::new("Assets:Cash", amount("900.00", "USD")));

    let err = engine
        .apply(&txn)
        .expect_err("an ambiguous reduction must be reported, not ignored");
    assert!(
        format!("{err}").contains("Ambiguous lot match"),
        "unexpected error: {err}"
    );
}

/// Total USD units the cash account holds, via the public iterator.
fn cash_units(engine: &BookingEngine) -> Decimal {
    engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Cash")
        .flat_map(|(_, inv)| inv.positions())
        .filter(|p| p.units.currency.as_str() == "USD")
        .map(|p| p.units.number)
        .sum()
}

/// A failing transaction leaves NO posting applied.
///
/// The cash leg comes FIRST, so it is already applied when the reduction
/// fails. Without the rollback the engine keeps half of a transaction it just
/// rejected — the non-atomic-mutation shape from #1976, reachable here only
/// because reduction failures became fatal.
#[test]
fn a_failing_transaction_is_rolled_back_whole() {
    let mut engine = engine_with_two_lots();
    let cash_before = cash_units(&engine);

    let mut sell = Posting::new("Assets:Broker", amount("-5", "AAPL"));
    sell.cost = Some(empty_spec());
    let txn = Transaction::new(date(10), "sell 5")
        .with_synthesized_posting(Posting::new("Assets:Cash", amount("900.00", "USD")))
        .with_synthesized_posting(sell);

    engine.apply(&txn).expect_err("must fail");

    let cash_after = cash_units(&engine);
    assert_eq!(
        cash_before, cash_after,
        "the cash leg of a rejected transaction stayed applied"
    );
}

/// A well-formed reduction still applies, and still nets against its lot.
///
/// The other half: making failures fatal must not make successes fail.
/// Without this, deleting the reduction path entirely would pass both tests
/// above.
#[test]
fn a_matching_reduction_still_applies() {
    let mut engine = engine_with_two_lots();

    let mut sell = Posting::new("Assets:Broker", amount("-4", "AAPL"));
    sell.cost = Some(spec("150.00", "USD", 5));
    let txn = Transaction::new(date(10), "sell")
        .with_synthesized_posting(sell)
        .with_synthesized_posting(Posting::new("Assets:Cash", amount("600.00", "USD")));
    engine
        .apply(&txn)
        .expect("an unambiguous reduction applies");

    let inventories = engine.into_inventories();
    let broker = inventories
        .get(&rustledger_core::Account::from("Assets:Broker"))
        .expect("broker holds something");
    let total: Decimal = broker
        .positions()
        .filter(|p| p.units.currency.as_str() == "AAPL")
        .map(|p| p.units.number)
        .sum();
    assert_eq!(total, "16".parse::<Decimal>().unwrap(), "20 bought, 4 sold");
}
