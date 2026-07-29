//! Property-based invariants for lot booking — the silent-corruption class.
//!
//! The worst booking bugs (#1444 AVERAGE wiping a whole position on a partial
//! sale, #1666 a labeled reduction minting a phantom unlabeled negative lot)
//! shared a signature: booking *succeeded*, `check` stayed green, and only the
//! lot-level holdings were wrong. `spec/tla/Conservation.tla` and friends model
//! the *design*; these tests exercise the *implementation* with randomized
//! operation sequences and assert the invariants that both bugs violated:
//!
//! 1. **Conservation** — aggregate units equal buys minus successful sells.
//! 2. **Aggregate consistency** — `Inventory::units` equals the sum over lots.
//! 3. **No minted lot identity** — a reduction never creates a lot key
//!    (cost, date, label) that wasn't already present (AVERAGE excepted: its
//!    merge deliberately synthesizes the weighted-average pool lot).
//! 4. **No phantom negatives** — with only positive buys, no lot goes negative.
//! 5. **Failed reductions don't mutate** — an `Err` from `reduce` leaves the
//!    inventory exactly as it was.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{
    Amount, BookingMethod, Cost, CostSpec, Inventory, NaiveDate, Position, naive_date,
};

const CURRENCY: &str = "X";
const COST_CURRENCY: &str = "USD";
const LABELS: [&str; 4] = ["lot-a", "lot-b", "lot-c", "lot-d"];

/// One randomized inventory operation.
#[derive(Debug, Clone)]
enum Op {
    Buy {
        units: u32,
        cost: u32,
        label: Option<usize>,
        day: u32,
    },
    Sell {
        units: u32,
        label: Option<usize>,
    },
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        (
            1u32..=50,
            1u32..=20,
            proptest::option::of(0usize..LABELS.len()),
            0u32..=27,
        )
            .prop_map(|(units, cost, label, day)| Op::Buy {
                units,
                cost,
                label,
                day,
            }),
        (1u32..=60, proptest::option::of(0usize..LABELS.len()))
            .prop_map(|(units, label)| Op::Sell { units, label }),
    ]
}

fn method_strategy() -> impl Strategy<Value = BookingMethod> {
    prop_oneof![
        Just(BookingMethod::Strict),
        Just(BookingMethod::Fifo),
        Just(BookingMethod::Lifo),
        Just(BookingMethod::Average),
    ]
}

fn day_date(day: u32) -> NaiveDate {
    naive_date(2020, 1, day + 1).expect("day 0..=27 maps to a valid January date")
}

/// The identity of a lot: (cost number, cost currency, date, label). A
/// reduction may shrink or remove a lot but must never mint a new identity
/// (the #1666 phantom-lot signature).
type LotKey = (Decimal, String, Option<NaiveDate>, Option<String>);

/// Sorted lot keys + units for the test currency — an order-independent
/// snapshot of the lot-level state.
fn lot_snapshot(inv: &Inventory) -> Vec<(LotKey, Decimal)> {
    let mut lots: Vec<(LotKey, Decimal)> = inv
        .positions()
        .filter(|p| p.units.currency.as_ref() == CURRENCY)
        .map(|p| {
            let key = match &p.cost {
                Some(c) => (c.number, c.currency.to_string(), c.date, c.label.clone()),
                None => (Decimal::ZERO, String::new(), None, None),
            };
            (key, p.units.number)
        })
        .collect();
    lots.sort();
    lots
}

fn sell_spec(label: Option<usize>) -> CostSpec {
    let mut spec = CostSpec::empty();
    spec.label = label.map(|i| LABELS[i].to_string());
    spec
}

proptest! {
    /// Randomized buy/sell sequences hold the five invariants under every
    /// booking method. Errors (insufficient units, ambiguous match, no
    /// matching lot) are legitimate outcomes — the invariant there is that
    /// the failed reduction left the inventory untouched.
    #[test]
    fn reduce_preserves_conservation_and_lot_identity(
        method in method_strategy(),
        ops in proptest::collection::vec(op_strategy(), 1..12),
    ) {
        let mut inv = Inventory::new();
        let mut expected_total = Decimal::ZERO;

        for op in &ops {
            match op {
                Op::Buy { units, cost, label, day } => {
                    let n = Decimal::from(*units);
                    let mut c = Cost::new(Decimal::from(*cost), COST_CURRENCY)
                        .with_date(day_date(*day));
                    c.label = label.map(|i| LABELS[i].to_string());
                    inv.add(Position::with_cost(Amount::new(n, CURRENCY), c)).expect("fixture fits in Decimal");
                    expected_total += n;
                }
                Op::Sell { units, label } => {
                    let n = Decimal::from(*units);
                    let before = lot_snapshot(&inv);
                    let before_keys: Vec<&LotKey> = before.iter().map(|(k, _)| k).collect();
                    let spec = sell_spec(*label);
                    if inv
                        .reduce(&Amount::new(-n, CURRENCY), Some(&spec), method)
                        .is_ok()
                    {
                        expected_total -= n;
                        let after = lot_snapshot(&inv);
                        if method == BookingMethod::Average {
                            // AVERAGE merges into one weighted-average
                            // pool (#1444) — a synthesized key is the
                            // point; assert the pool shape instead.
                            prop_assert!(
                                after.len() <= 1,
                                "AVERAGE must leave at most one pool lot, got {after:?}",
                            );
                        } else {
                            // Invariant 3: no minted lot identity.
                            for (key, _) in &after {
                                prop_assert!(
                                    before_keys.contains(&key),
                                    "reduction minted a new lot identity {key:?} \
                                     (was {before_keys:?}) — the #1666 class",
                                );
                            }
                        }
                        // Invariant 4: only positive buys exist, so no
                        // lot may be driven negative by a reduction.
                        for (key, n) in &after {
                            prop_assert!(
                                *n > Decimal::ZERO,
                                "lot {key:?} driven to {n} (phantom negative)",
                            );
                        }
                    } else {
                        // Invariant 5: a failed reduce must not mutate.
                        let after = lot_snapshot(&inv);
                        prop_assert_eq!(
                            &before, &after,
                            "failed reduce mutated the inventory",
                        );
                    }
                }
            }

            // Invariants 1 + 2 after every operation.
            let aggregate = inv.units(CURRENCY);
            prop_assert_eq!(aggregate, expected_total, "conservation violated");
            let lot_sum: Decimal = lot_snapshot(&inv).iter().map(|(_, n)| *n).sum();
            prop_assert_eq!(aggregate, lot_sum, "aggregate != sum of lots");
        }
    }

    /// Engine-level #1666 as a property: selling an explicitly-labeled lot
    /// books a reduction that carries that label and nets against that lot —
    /// never a phantom unlabeled negative lot in the holdings.
    #[test]
    fn labeled_sell_nets_against_its_lot(
        lot_units in proptest::collection::vec(1u32..=30, 2..=LABELS.len()),
        sell_lot in 0usize..LABELS.len(),
        sell_fraction in 1u32..=100,
    ) {
        use rustledger_booking::BookingEngine;
        use rustledger_core::{CostNumber, Posting, Transaction};

        let sell_lot = sell_lot % lot_units.len();
        let mut engine = BookingEngine::new();

        // Distinct label + cost + date per lot so every match is unambiguous.
        for (i, units) in lot_units.iter().enumerate() {
            let cost_number = Decimal::from(10 + i as u32);
            let mut cost = CostSpec::empty()
                .with_number(CostNumber::PerUnit { value: cost_number })
                .with_currency(COST_CURRENCY);
            cost.label = Some(LABELS[i].to_string());
            cost.date = Some(day_date(i as u32));
            let buy = Transaction::new(day_date(i as u32), "buy")
                .with_synthesized_posting(
                    Posting::new("Assets:S", Amount::new(Decimal::from(*units), CURRENCY))
                        .with_cost(cost),
                )
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(-Decimal::from(*units) * cost_number, COST_CURRENCY),
                ));
            engine.apply(&buy).expect("fixture fits in Decimal");
        }

        // Sell 1..=100% of the chosen lot, matched by its label.
        let held = lot_units[sell_lot];
        let sell_units = ((held * sell_fraction).div_ceil(100)).max(1);
        let cost_number = Decimal::from(10 + sell_lot as u32);
        let mut spec = CostSpec::empty();
        spec.label = Some(LABELS[sell_lot].to_string());
        let sell = Transaction::new(day_date(28), "sell")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:S",
                    Amount::new(-Decimal::from(sell_units), CURRENCY),
                )
                .with_cost(spec),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(Decimal::from(sell_units) * cost_number, COST_CURRENCY),
            ));

        let result = engine
            .book_and_interpolate(&sell)
            .expect("labeled sell within the lot's units must book");

        // The booked reduction posting carries the matched lot's label (#1666).
        let booked_label = result.transaction.postings[0]
            .cost
            .as_ref()
            .and_then(|c| c.label.clone());
        prop_assert_eq!(
            booked_label.as_deref(),
            Some(LABELS[sell_lot]),
            "reduction must carry the matched lot's label",
        );

        engine.apply(&result.transaction).expect("fixture fits in Decimal");
        let inv = engine
            .inventory(&"Assets:S".into())
            .expect("account has inventory");

        // No phantom lot: every remaining lot is positive and carries one of
        // the original labels; totals reconcile.
        let total: u32 = lot_units.iter().sum();
        prop_assert_eq!(
            inv.units(CURRENCY),
            Decimal::from(total - sell_units),
            "aggregate after labeled sell",
        );
        for (key, n) in lot_snapshot(inv) {
            prop_assert!(n > Decimal::ZERO, "phantom negative lot {key:?} = {n}");
            let label = key.3.as_deref().expect("all lots were labeled");
            prop_assert!(
                LABELS.contains(&label),
                "unexpected lot label {label:?}",
            );
        }
        // The sold-from lot shrank (or vanished on a full sale).
        let remaining_in_lot: Decimal = lot_snapshot(inv)
            .iter()
            .filter(|(k, _)| k.3.as_deref() == Some(LABELS[sell_lot]))
            .map(|(_, n)| *n)
            .sum();
        prop_assert_eq!(
            remaining_in_lot,
            Decimal::from(held - sell_units),
            "sold-from lot must shrink by exactly the sold units",
        );
    }
}
