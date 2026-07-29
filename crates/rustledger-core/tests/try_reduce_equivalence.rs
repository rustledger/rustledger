//! `try_reduce` ≅ `reduce` equivalence — the preview must predict the commit.
//!
//! [`Inventory::try_reduce`] is the read-only preview of [`Inventory::reduce`]
//! ("returns what would be matched without actually modifying the
//! inventory"). It duplicates every booking method's selection logic, which
//! is exactly the one-logic-two-paths shape behind this codebase's recurring
//! drift class (#1648, the `@@` price, #1663, #1686) — and it HAD drifted:
//! before the fix accompanying this test, `try_reduce` under STRICT fell back
//! to FIFO on any multi-lot match while `reduce` returned `AmbiguousMatch`
//! unless the lots were financially interchangeable, and `try_reduce` under
//! NONE/`{*}`-merge routed to entirely different implementations than the
//! mutating dispatch.
//!
//! The obligation, checked here for every booking method against randomized
//! inventories and satisfiable/unsatisfiable reductions alike:
//!
//! ```text
//! try_reduce(&inv, op) == reduce(&mut inv.clone(), op)
//! ```
//!
//! — identical `Ok` (matched lots AND cost basis) or identical `Err`.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{
    Amount, BookingMethod, Cost, CostNumber, CostSpec, Inventory, NaiveDate, Position, naive_date,
};

const CURRENCY: &str = "AAPL";
const LABELS: [&str; 3] = ["lot-a", "lot-b", "lot-c"];

fn day(d: u32) -> NaiveDate {
    naive_date(2024, 1, d).expect("valid day")
}

fn position_strategy() -> impl Strategy<Value = Position> {
    (
        1i64..50,
        1i64..20,
        1u32..28,
        proptest::option::of(0usize..LABELS.len()),
    )
        .prop_map(|(units, cost, d, label)| {
            let mut c = Cost::new(Decimal::from(cost), "USD").with_date(day(d));
            c.label = label.map(|i| LABELS[i].to_string());
            Position::with_cost(Amount::new(Decimal::from(units), CURRENCY), c)
        })
}

fn method_strategy() -> impl Strategy<Value = BookingMethod> {
    prop_oneof![
        Just(BookingMethod::Strict),
        Just(BookingMethod::StrictWithSize),
        Just(BookingMethod::Fifo),
        Just(BookingMethod::Lifo),
        Just(BookingMethod::Hifo),
        Just(BookingMethod::Average),
        Just(BookingMethod::None),
    ]
}

/// Cost specs spanning the satisfiable and unsatisfiable spectrum: empty,
/// label match, unknown label, unmatched cost number, and the `{*}` merge
/// operator (which has its own dispatch arm).
fn spec_strategy() -> impl Strategy<Value = Option<CostSpec>> {
    prop_oneof![
        Just(None),
        Just(Some(CostSpec::default())),
        (0usize..LABELS.len()).prop_map(|i| {
            Some(CostSpec {
                label: Some(LABELS[i].to_string()),
                ..CostSpec::default()
            })
        }),
        Just(Some(CostSpec {
            label: Some("no-such-lot".to_string()),
            ..CostSpec::default()
        })),
        Just(Some(CostSpec::default().with_number(CostNumber::PerUnit {
            value: Decimal::from(9999),
        }),)),
        Just(Some(CostSpec {
            merge: true,
            ..CostSpec::default()
        })),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// For any inventory, method, spec, and (possibly excessive) amount, the
    /// preview and the commit agree exactly.
    #[test]
    fn try_reduce_predicts_reduce(
        positions in prop::collection::vec(position_strategy(), 0..5),
        method in method_strategy(),
        spec in spec_strategy(),
        amount in 1i64..200,
        wrong_currency in proptest::bool::weighted(0.15),
    ) {
        let mut inv = Inventory::new();
        for pos in &positions {
            inv.add(pos.clone()).expect("fixture fits in Decimal");
        }

        let currency = if wrong_currency { "MSFT" } else { CURRENCY };
        let units = Amount::new(Decimal::from(-amount), currency);

        let preview = inv.try_reduce(&units, spec.as_ref(), method);
        let mut committed_inv = inv.clone();
        let commit = committed_inv.reduce(&units, spec.as_ref(), method);

        prop_assert_eq!(
            &preview,
            &commit,
            "try_reduce diverged from reduce (method {:?}, spec {:?}, amount {})",
            method,
            spec,
            amount
        );
    }
}
