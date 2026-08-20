//! The engine's holdings must equal the sum of the booked postings (#2070).
//!
//! `book` and `apply` are two derivations of the same quantity. `book` decides
//! what each posting does and writes that into the posting; `apply` re-runs
//! `Inventory::reduce` and decides again, against state that has moved on. When
//! the cost spec names a concrete lot the two land on the same answer, which is
//! why the disagreement went unnoticed — the merging paths (`AVERAGE`, `{*}`)
//! re-derive a pool instead, and a lot added earlier in the SAME transaction
//! moves it.
//!
//! The invariant compares units and cost basis, not lot structure: ADR-0007
//! deliberately lets the engine pool while the journal keeps per-lot costs, and
//! pooling preserves both totals. So this asserts only what both representations
//! must agree on, and stays silent about the representation itself.
//!
//! Every existing suite passed while the divergence shipped, so treat a clean
//! run here as meaningful only alongside `the_comparison_can_report_dirty`,
//! which pins that the comparison itself can report a disagreement.

use proptest::prelude::*;
use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, BookingMethod, CostNumber, CostSpec, Decimal, NaiveDate, Posting, Transaction,
    naive_date,
};
use std::collections::BTreeMap;

const CURRENCY: &str = "X";
const COST_CURRENCY: &str = "USD";
const ACCOUNT: &str = "Assets:Stock";

fn date(d: u32) -> NaiveDate {
    naive_date(2024, 1, d.clamp(1, 28)).expect("valid date")
}

fn per_unit(cost: u32) -> CostSpec {
    CostSpec {
        number: Some(CostNumber::PerUnit {
            value: Decimal::from(cost),
        }),
        currency: Some(COST_CURRENCY.into()),
        date: None,
        label: None,
        merge: false,
    }
}

const fn empty_spec() -> CostSpec {
    CostSpec {
        number: None,
        currency: None,
        date: None,
        label: None,
        merge: false,
    }
}

fn merge_spec() -> CostSpec {
    CostSpec {
        merge: true,
        ..empty_spec()
    }
}

/// `(units, cost basis)` per commodity, the two quantities both
/// representations must agree on.
type Totals = BTreeMap<String, (Decimal, Decimal)>;

/// What the ENGINE holds.
fn engine_totals(engine: &BookingEngine) -> Totals {
    let mut out = Totals::new();
    for (account, inv) in engine.inventories() {
        if account.as_str() != ACCOUNT {
            continue;
        }
        for p in inv.positions() {
            let e = out
                .entry(p.units.currency.to_string())
                .or_insert((Decimal::ZERO, Decimal::ZERO));
            e.0 += p.units.number;
            e.1 += p.units.number * p.cost.as_ref().map_or(Decimal::ZERO, |c| c.number);
        }
    }
    out
}

/// What the JOURNAL says — the booked postings, summed.
///
/// This is what BQL aggregates and what `print` shows, so it is the ledger's
/// record of what happened. Accumulating it is deliberately dumb: no matching,
/// no re-derivation, just addition.
fn add_booked_postings(totals: &mut Totals, txn: &Transaction) {
    for posting in &txn.postings {
        if posting.account.as_str() != ACCOUNT {
            continue;
        }
        let Some(units) = posting.amount() else {
            continue;
        };
        let cost = posting
            .cost
            .as_ref()
            .and_then(|c| c.number)
            .and_then(|n| n.per_unit())
            .unwrap_or(Decimal::ZERO);
        let e = totals
            .entry(units.currency.to_string())
            .or_insert((Decimal::ZERO, Decimal::ZERO));
        e.0 += units.number;
        e.1 += units.number * cost;
    }
}

/// Basis equality, ignoring the residue a weighted average cannot represent.
///
/// A pooled cost like `7939/79` does not terminate, so the engine stores it
/// rounded on the remainder while the journal keeps the un-rounded sum of what
/// was booked. They then differ in the last digits of `rust_decimal`'s 28 —
/// inherent to per-unit average costing, not a decision the two halves disagree
/// about, and it is what this predicate exists to ignore.
///
/// The tolerance is far below anything the divergence this file hunts produces:
/// #2070's shape is off by 50 whole units of cost currency, which is roughly
/// twenty orders of magnitude above this bar. Widening it further would start
/// masking real disagreement, so it stays pinned to representation error.
fn within_rounding_residue(a: Decimal, b: Decimal) -> bool {
    let scale = a.abs().max(b.abs()).max(Decimal::ONE);
    let tolerance = scale
        * Decimal::from_str_exact("0.00000000000000000001").expect("literal is a valid decimal");
    (a - b).abs() <= tolerance
}

/// One posting in a generated transaction.
#[derive(Debug, Clone)]
enum Leg {
    Buy {
        units: u32,
        cost: u32,
    },
    /// Reduce naming an explicit lot cost.
    SellAt {
        units: u32,
        cost: u32,
    },
    /// Reduce with a bare `{}` — the booking method picks the lot.
    SellAny {
        units: u32,
    },
    /// Reduce through a `{*}` merge.
    SellMerged {
        units: u32,
    },
}

fn leg_strategy() -> impl Strategy<Value = Leg> {
    prop_oneof![
        (1u32..12, 100u32..104).prop_map(|(units, cost)| Leg::Buy { units, cost }),
        (1u32..8, 100u32..104).prop_map(|(units, cost)| Leg::SellAt { units, cost }),
        (1u32..8).prop_map(|units| Leg::SellAny { units }),
        (1u32..8).prop_map(|units| Leg::SellMerged { units }),
    ]
}

fn posting_for(leg: &Leg) -> Posting {
    match leg {
        Leg::Buy { units, cost } => {
            let mut p = Posting::new(ACCOUNT, Amount::new(Decimal::from(*units), CURRENCY));
            p.cost = Some(Box::new(per_unit(*cost)));
            p
        }
        Leg::SellAt { units, cost } => {
            let mut p = Posting::new(ACCOUNT, Amount::new(-Decimal::from(*units), CURRENCY));
            p.cost = Some(Box::new(per_unit(*cost)));
            p
        }
        Leg::SellAny { units } => {
            let mut p = Posting::new(ACCOUNT, Amount::new(-Decimal::from(*units), CURRENCY));
            p.cost = Some(Box::new(empty_spec()));
            p
        }
        Leg::SellMerged { units } => {
            let mut p = Posting::new(ACCOUNT, Amount::new(-Decimal::from(*units), CURRENCY));
            p.cost = Some(Box::new(merge_spec()));
            p
        }
    }
}

/// Book and apply a stream, returning `(journal totals, engine totals)`.
///
/// A transaction that fails to book is SKIPPED, not applied — an unbookable
/// ledger is a different failure and says nothing about this invariant.
fn run(method: BookingMethod, seeds: &[u32], txns: &[Vec<Leg>]) -> (Totals, Totals) {
    let mut engine = BookingEngine::with_method(method);
    let mut journal = Totals::new();

    for (i, cost) in seeds.iter().enumerate() {
        let mut buy = Posting::new(ACCOUNT, Amount::new(Decimal::from(40), CURRENCY));
        buy.cost = Some(Box::new(per_unit(*cost)));
        let txn = Transaction::new(date(u32::try_from(i).unwrap_or(0) + 1), "seed")
            .with_synthesized_posting(buy);
        engine
            .apply(&txn)
            .expect("seed buys are fixtures and always apply");
        add_booked_postings(&mut journal, &txn);
    }

    for (i, legs) in txns.iter().enumerate() {
        let mut txn = Transaction::new(date(u32::try_from(i).unwrap_or(0) + 10), "generated");
        for leg in legs {
            txn = txn.with_synthesized_posting(posting_for(leg));
        }
        // An unbookable transaction is a different failure and says nothing
        // about this invariant, so it is skipped. A transaction that BOOKED and
        // then failed to apply is not skipped: `apply`'s precondition is booked
        // input, and `book` just produced it, so that combination is itself a
        // defect and must not be swallowed into a vacuous pass.
        let Ok(booked) = engine.book(&txn) else {
            continue;
        };
        engine
            .apply(&booked.transaction)
            .expect("a transaction that booked must apply");
        add_booked_postings(&mut journal, &booked.transaction);
    }

    (journal, engine_totals(&engine))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Whatever the booked postings add up to is what the account holds.
    #[test]
    fn the_engine_equals_the_sum_of_the_booked_postings(
        method in prop::sample::select(vec![
            BookingMethod::Strict,
            BookingMethod::Fifo,
            BookingMethod::Lifo,
            BookingMethod::Average,
        ]),
        seeds in prop::collection::vec(100u32..104, 1..4),
        txns in prop::collection::vec(
            prop::collection::vec(leg_strategy(), 1..4),
            1..5,
        ),
    ) {
        let (journal, engine) = run(method, &seeds, &txns);
        for (currency, (j_units, j_basis)) in &journal {
            let (e_units, e_basis) = engine
                .get(currency)
                .copied()
                .unwrap_or((Decimal::ZERO, Decimal::ZERO));
            prop_assert_eq!(
                j_units, &e_units,
                "unit counts disagree for {} under {:?}\n  seeds: {:?}\n  txns: {:?}",
                currency, method, seeds, txns,
            );
            prop_assert!(
                within_rounding_residue(*j_basis, e_basis),
                "cost basis disagrees for {} under {:?} by {}\n  journal {} vs engine {}\n                   seeds: {:?}\n  txns: {:?}",
                currency, method, (*j_basis - e_basis).abs(), j_basis, e_basis, seeds, txns,
            );
        }
    }
}

/// The comparison can report DIRTY.
///
/// A green property run is worth nothing until the comparison is shown to fail
/// on input that disagrees — 145 suites passed while #2070's divergence
/// shipped. This checks the COMPARATOR, deliberately, rather than asserting
/// that the engine still has the bug: a self-check written that way inverts the
/// moment the bug is fixed, and then the harness is unguarded exactly when it
/// starts mattering.
#[test]
fn the_comparison_can_report_dirty() {
    let one = |units: i64, basis: &str| {
        let mut t = Totals::new();
        t.insert(
            "X".to_string(),
            (
                Decimal::from(units),
                Decimal::from_str_exact(basis).expect("literal is a valid decimal"),
            ),
        );
        t
    };

    // #2070's magnitude: 50 whole units of cost currency.
    let journal = one(15, "1700");
    let engine = one(15, "1650");
    let (j_basis, e_basis) = (journal["X"].1, engine["X"].1);
    assert!(
        !within_rounding_residue(j_basis, e_basis),
        "a 50-unit basis gap must be reported, not absorbed as rounding",
    );

    // Unit counts are compared exactly, with no tolerance at all.
    assert_ne!(one(15, "1700")["X"].0, one(14, "1700")["X"].0);

    // ...and the residue a weighted average cannot represent is absorbed.
    assert!(
        within_rounding_residue(
            Decimal::from_str_exact("7838.5063291139240506329113924")
                .expect("literal is a valid decimal"),
            Decimal::from_str_exact("7838.5063291139240506329113920")
                .expect("literal is a valid decimal"),
        ),
        "representation residue must not be reported as disagreement",
    );
}
