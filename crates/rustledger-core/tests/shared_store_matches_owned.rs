//! Property: a shared inventory holds what an owned one holds, for any
//! sequence of adds, rebuilds and clones (#2388).
//!
//! The shared store (BQL's running `balance`) finds an `add`'s merge target
//! through a persistent cost index, the owned store through a plain hash
//! map. Lots differing only in cost scale (`100` and `100.00`), date or label
//! exercise the index's hashing and the merge test behind it; a rebuild
//! (`compact`) used to empty the shared index, after which earlier lots
//! stopped merging. Every snapshot taken along the way must also keep the
//! value it had, since later adds copy only the path they change.

use proptest::prelude::*;
use rustledger_core::{Amount, Cost, Decimal, Inventory, Position};
use std::str::FromStr;

#[derive(Debug, Clone)]
enum Step {
    Add {
        units: i64,
        cost: usize,
        date: Option<u32>,
        label: bool,
        commodity: usize,
    },
    Cash(i64),
    Rebuild,
    Snapshot,
}

const COSTS: [&str; 6] = ["100", "100.0", "100.00", "101.5", "101.50", "99"];

fn step() -> impl Strategy<Value = Step> {
    prop_oneof![
        8 => (-3i64..6, 0usize..6, prop::option::of(1u32..4), any::<bool>(), 0usize..2)
            .prop_filter("non-zero", |(u, ..)| *u != 0)
            .prop_map(|(units, cost, date, label, commodity)| Step::Add { units, cost, date, label, commodity }),
        1 => (-50i64..50).prop_map(Step::Cash),
        1 => Just(Step::Rebuild),
        2 => Just(Step::Snapshot),
    ]
}

fn position(step: &Step) -> Option<Position> {
    match *step {
        Step::Add {
            units,
            cost,
            date,
            label,
            commodity,
        } => {
            let mut c = Cost::new(Decimal::from_str(COSTS[cost]).expect("cost"), "USD");
            if let Some(day) = date {
                c = c.with_date(rustledger_core::naive_date(2024, 1, day).expect("date"));
            }
            if label {
                c = c.with_label("a");
            }
            Some(Position::with_cost(
                Amount::new(Decimal::from(units), ["X", "Y"][commodity]),
                c,
            ))
        }
        Step::Cash(n) => Some(Position::simple(Amount::new(Decimal::from(n), "USD"))),
        Step::Rebuild | Step::Snapshot => None,
    }
}

/// Live lots, sorted, with costs compared by value rather than scale.
///
/// The two stores differ in slot order and cost scale by design, on main as
/// on this change: a lot netted to zero is dropped from the owned store
/// (#2378) but kept on the shared one, where dropping it would shift every
/// later slot. A later add of the same lot then merges into the kept slot,
/// with the scale it was first written in (`100`), where the owned store
/// appends a new lot (`100.0`). Same lots, same value; the inventory renderer
/// orders lots itself.
fn lots(inv: &Inventory) -> Vec<String> {
    let mut lots = inv
        .positions()
        .filter(|p| !p.units.number.is_zero())
        .map(|p| {
            let cost = p.cost.as_ref().map(|c| {
                format!(
                    "{} {} {:?} {:?}",
                    c.number.normalize(),
                    c.currency,
                    c.date,
                    c.label
                )
            });
            format!(
                "{} {} {cost:?}",
                p.units.number.normalize(),
                p.units.currency
            )
        })
        .collect::<Vec<_>>();
    lots.sort();
    lots
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 512, ..ProptestConfig::default() })]

    #[test]
    fn a_shared_store_holds_what_an_owned_one_holds(steps in prop::collection::vec(step(), 1..40)) {
        let mut shared = Inventory::new_shared();
        let mut owned = Inventory::new();
        let mut snapshots: Vec<(Inventory, Vec<String>)> = Vec::new();
        for step in &steps {
            match step {
                Step::Rebuild => {
                    shared.compact();
                    owned.compact();
                }
                Step::Snapshot => snapshots.push((shared.clone(), lots(&owned))),
                _ => {
                    let p = position(step).expect("an add");
                    shared.add(p.clone()).expect("fits");
                    owned.add(p).expect("fits");
                }
            }
            prop_assert_eq!(lots(&shared), lots(&owned), "after {:?}", step);
            prop_assert_eq!(shared.units("X"), owned.units("X"));
        }
        for (snap, want) in &snapshots {
            prop_assert_eq!(&lots(snap), want, "a snapshot changed after it was taken");
        }
    }
}
