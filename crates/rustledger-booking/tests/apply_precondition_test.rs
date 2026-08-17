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

/// A failing transaction restores the reducing account's LOTS exactly, not
/// merely its totals.
///
/// `a_failing_transaction_is_rolled_back_whole` checks the cash leg, which a
/// rollback that restored totals but scrambled lots would still pass. That was
/// adequate while `apply` snapshotted each touched account with
/// `Inventory::clone` — restoring a whole copy cannot get the lots wrong.
/// `apply` now records an undo log of only the slots it touched, so lot-level
/// restoration is a real obligation rather than a free consequence, and it is
/// asserted here.
///
/// The transaction reduces the SAME account twice: the first leg succeeds and
/// mutates a lot, the second fails. That is the case where the log has to
/// unwind more than one change, and where restoring only the last one would
/// leave the account quietly short.
#[test]
fn a_failing_transaction_restores_every_lot_it_touched() {
    let mut engine = engine_with_two_lots();

    let lots_before: Vec<(Decimal, Option<Decimal>)> = engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Broker")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| (p.units.number, p.cost.as_ref().map(|c| c.number)))
        .collect();
    assert_eq!(lots_before.len(), 2, "fixture holds two lots");

    // Leg 1 matches the 150.00 lot and succeeds. Leg 2 asks for more of the
    // 200.00 lot than it holds, so the transaction fails after leg 1 mutated.
    let mut ok_leg = Posting::new("Assets:Broker", amount("-4", "AAPL"));
    ok_leg.cost = Some(spec("150.00", "USD", 5));
    let mut bad_leg = Posting::new("Assets:Broker", amount("-99", "AAPL"));
    bad_leg.cost = Some(spec("200.00", "USD", 6));

    let txn = Transaction::new(date(10), "one good leg, one impossible")
        .with_synthesized_posting(ok_leg)
        .with_synthesized_posting(bad_leg);

    engine
        .apply(&txn)
        .expect_err("the second leg cannot be satisfied");

    let lots_after: Vec<(Decimal, Option<Decimal>)> = engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Broker")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| (p.units.number, p.cost.as_ref().map(|c| c.number)))
        .collect();

    assert_eq!(
        lots_after, lots_before,
        "the rejected transaction left the account's lots altered: the first \
         leg's reduction was not undone",
    );
}

/// Rollback must also undo a lot that was fully DRAINED and one that was
/// ADDED before the failure.
///
/// The other rollback tests only mutate lots in place, so they exercise one of
/// the three ways `apply` changes an inventory. Removing the recording from
/// either of the other two — the removal of a drained lot, or the push of a
/// new one — leaves every other test passing while a rejected transaction
/// silently destroys a lot or leaves a phantom one behind.
#[test]
fn a_failing_transaction_undoes_drained_and_added_lots() {
    let mut engine = engine_with_two_lots();

    let lots_before: Vec<(Decimal, Option<Decimal>)> = engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Broker")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| (p.units.number, p.cost.as_ref().map(|c| c.number)))
        .collect();
    assert_eq!(lots_before.len(), 2, "fixture holds two lots");

    // Leg 1 drains the 150.00 lot entirely -> the lot is REMOVED.
    let mut drain = Posting::new("Assets:Broker", amount("-10", "AAPL"));
    drain.cost = Some(spec("150.00", "USD", 5));
    // Leg 2 buys a new lot -> a slot is PUSHED.
    let mut buy = Posting::new("Assets:Broker", amount("7", "AAPL"));
    buy.cost = Some(spec("300.00", "USD", 11));
    // Leg 3 cannot be satisfied, so the whole transaction is rejected.
    let mut impossible = Posting::new("Assets:Broker", amount("-99", "AAPL"));
    impossible.cost = Some(spec("200.00", "USD", 6));

    let txn = Transaction::new(date(11), "drain, buy, then fail")
        .with_synthesized_posting(drain)
        .with_synthesized_posting(buy)
        .with_synthesized_posting(impossible);

    engine
        .apply(&txn)
        .expect_err("the third leg cannot be satisfied");

    let lots_after: Vec<(Decimal, Option<Decimal>)> = engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Broker")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| (p.units.number, p.cost.as_ref().map(|c| c.number)))
        .collect();

    assert_eq!(
        lots_after, lots_before,
        "a rejected transaction destroyed the drained lot or kept the added \
         one: {lots_before:?} -> {lots_after:?}",
    );
}

/// A `{*}` merge leg that is later rejected must give its lots back.
///
/// The merge path is the one that removes lots WITHOUT writing them first:
/// `reduce_merge` drops every matched lot through `retain_slots`, where the
/// other reduction paths zero a lot in place and only then remove it. On those,
/// the in-place write is what captures the lot for the undo log, so dropping
/// the capture in the removal path changes nothing — this is the case that
/// tells the two apart, and without it a rejected `{*}` transaction silently
/// destroys every lot it merged.
#[test]
fn a_failing_transaction_undoes_a_wildcard_merge() {
    let mut engine = engine_with_two_lots();

    let lots_before: Vec<(Decimal, Option<Decimal>)> = engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Broker")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| (p.units.number, p.cost.as_ref().map(|c| c.number)))
        .collect();
    assert_eq!(lots_before.len(), 2, "fixture holds two lots to merge");

    // Leg 1: `{*}` merges BOTH lots into one and reduces it — removing the
    // originals outright.
    let mut merge_leg = Posting::new("Assets:Broker", amount("-5", "AAPL"));
    merge_leg.cost = Some(CostSpec {
        number: None,
        currency: None,
        date: None,
        label: None,
        merge: true,
    });
    // Leg 2 cannot be satisfied, so the transaction is rejected.
    let mut impossible = Posting::new("Assets:Broker", amount("-99", "AAPL"));
    impossible.cost = Some(spec("200.00", "USD", 6));

    let txn = Transaction::new(date(12), "merge then fail")
        .with_synthesized_posting(merge_leg)
        .with_synthesized_posting(impossible);

    engine
        .apply(&txn)
        .expect_err("the second leg cannot be satisfied");

    let lots_after: Vec<(Decimal, Option<Decimal>)> = engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Broker")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| (p.units.number, p.cost.as_ref().map(|c| c.number)))
        .collect();

    assert_eq!(
        lots_after, lots_before,
        "the rejected merge destroyed the lots it consumed: {lots_before:?} \
         -> {lots_after:?}",
    );
}

/// A transaction that CREATES the lot it then fails to reduce must report an
/// error, not panic.
///
/// `rollback_needed` decides up front whether to prepare a rollback. It used
/// to ask whether each posting reduces something the account holds *at that
/// moment* — a question the transaction itself can falsify:
///
/// ```text
///   Assets:Stock   10 X {100.00 USD}
///   Assets:Stock  -20 X {100.00 USD}
/// ```
///
/// Against an empty account that answered "no reduction", so nothing was
/// prepared; the second posting then failed and `apply` hit its own "the guard
/// is unsound" assertion. An ordinary bad ledger became a panic out of
/// `rledger check`, on main as well as on this branch.
///
/// Carrying a cost spec is what makes a posting able to reduce, and that does
/// not depend on state, so the transaction cannot falsify it.
#[test]
fn a_transaction_that_creates_and_then_oversells_a_lot_errors_rather_than_panicking() {
    let mut engine = BookingEngine::with_method(BookingMethod::Strict);

    let mut buy = Posting::new("Assets:Stock", amount("10", "X"));
    buy.cost = Some(spec("100.00", "USD", 1));
    let mut oversell = Posting::new("Assets:Stock", amount("-20", "X"));
    oversell.cost = Some(spec("100.00", "USD", 1));

    let txn = Transaction::new(date(1), "buy then oversell")
        .with_synthesized_posting(buy)
        .with_synthesized_posting(oversell);

    let err = engine
        .apply(&txn)
        .expect_err("overselling the lot it just created must be an error");
    assert!(
        format!("{err:?}").contains("Insufficient") || format!("{err}").contains("not enough"),
        "expected an insufficient-units error, got {err:?}",
    );

    // And the buy must have been rolled back with it: a rejected transaction
    // leaves nothing behind.
    let held: Vec<Decimal> = engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Stock")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| p.units.number)
        .collect();
    assert!(
        held.is_empty(),
        "the rejected transaction left its buy applied: {held:?}",
    );
}
