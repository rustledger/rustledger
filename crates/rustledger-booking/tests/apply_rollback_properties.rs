//! Transaction-level rollback, under randomized failure.
//!
//! `booking_properties.rs` pins that a failed `Inventory::reduce` does not
//! mutate. That is one posting. `apply` is the transaction: it can apply
//! several postings and then fail on a later one, and must undo everything it
//! already did.
//!
//! It used to do that by cloning each touched account before mutating, which
//! cannot get the restoration wrong — restoring a whole copy is total by
//! construction. It now records an undo log of the slots it writes, so
//! completeness is a property of the recording hooks instead, and the hand-
//! written cases only cover the interleavings someone thought of. These
//! generate them.

use proptest::prelude::*;
use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, BookingMethod, CostNumber, CostSpec, Decimal, NaiveDate, Posting, Transaction,
    naive_date,
};

const CURRENCY: &str = "X";
/// A commodity the generated legs never mention, so the doomed posting can
/// always find lots to fail against.
const ANCHOR: &str = "ANCHOR";
const COST_CURRENCY: &str = "USD";

fn date(d: u32) -> NaiveDate {
    naive_date(2024, 1, d.clamp(1, 28)).expect("valid date")
}

fn per_unit(cost: u32, day: u32) -> CostSpec {
    CostSpec {
        number: Some(CostNumber::PerUnit {
            value: Decimal::from(cost),
        }),
        currency: Some(COST_CURRENCY.into()),
        date: Some(date(day)),
        label: None,
        merge: false,
    }
}

/// One posting in the generated transaction.
#[derive(Debug, Clone)]
enum Leg {
    /// Add a new lot at this cost.
    Buy { units: u32, cost: u32 },
    /// Reduce against a lot at this cost, by this much.
    Sell { units: u32, cost: u32 },
    /// Reduce every lot into one and take from it.
    Merge { units: u32 },
}

fn leg_strategy(costs: Vec<u32>) -> impl Strategy<Value = Leg> {
    let c = costs.clone();
    prop_oneof![
        (1u32..20, prop::sample::select(costs)).prop_map(|(units, cost)| Leg::Buy { units, cost }),
        (1u32..20, prop::sample::select(c)).prop_map(|(units, cost)| Leg::Sell { units, cost }),
        (1u32..20).prop_map(|units| Leg::Merge { units }),
    ]
}

/// The lots an account holds, as a comparable snapshot.
fn holdings(engine: &BookingEngine) -> Vec<(String, Decimal, Option<Decimal>, Option<NaiveDate>)> {
    engine
        .inventories()
        .filter(|(account, _)| account.as_str() == "Assets:Stock")
        .flat_map(|(_, inv)| inv.positions())
        .map(|p| {
            (
                // The commodity is part of the snapshot because the account
                // now holds two: the generated legs work on one, the doomed
                // leg reduces the other. Without it, a rollback that restored
                // the right numbers against the wrong commodity would compare
                // equal.
                p.units.currency.to_string(),
                p.units.number,
                p.cost.as_ref().map(|c| c.number),
                p.cost.as_ref().and_then(|c| c.date),
            )
        })
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(192))]

    /// A transaction that fails part-way leaves the account EXACTLY as it was.
    ///
    /// The legs before the failure are randomized across all three shapes that
    /// mutate an inventory differently — a buy pushes a slot, a sell writes a
    /// lot in place or drains it, and `{*}` drops every matched lot at once —
    /// so the undo log has to cover whatever combination comes up. The final
    /// leg oversells by far more than the account can hold, which fails under
    /// every booking method.
    #[test]
    fn a_failed_transaction_restores_the_account_exactly(
        seed_costs in prop::collection::vec(100u32..104, 1..4),
        legs in prop::collection::vec(leg_strategy((100u32..104).collect()), 0..5),
    ) {
        let mut engine = BookingEngine::with_method(BookingMethod::Fifo);

        // Seed: one lot per cost, so sells have something to match.
        for (i, cost) in seed_costs.iter().enumerate() {
            let day = u32::try_from(i).unwrap_or(0) + 1;
            let mut buy = Posting::new("Assets:Stock", Amount::new(Decimal::from(50), CURRENCY));
            buy.cost = Some(per_unit(*cost, day));
            let txn = Transaction::new(date(day), "seed")
                .with_synthesized_posting(buy);
            engine.apply(&txn).expect("seeding fits");
        }

        // A lot in a commodity no generated leg touches. The doomed posting
        // below reduces THIS, so it is a reduction no matter what the prefix
        // did to the generated commodity — see the comment there.
        let mut anchor = Posting::new("Assets:Stock", Amount::new(Decimal::from(50), ANCHOR));
        anchor.cost = Some(per_unit(7, 1));
        engine
            .apply(&Transaction::new(date(1), "anchor").with_synthesized_posting(anchor))
            .expect("the anchor lot fits");

        let before = holdings(&engine);

        // The transaction: some legs, then one that cannot succeed.
        let mut txn = Transaction::new(date(20), "randomized then doomed");
        for (i, leg) in legs.iter().enumerate() {
            let day = u32::try_from(i).unwrap_or(0) + 1;
            let posting = match leg {
                Leg::Buy { units, cost } => {
                    let mut p = Posting::new(
                        "Assets:Stock",
                        Amount::new(Decimal::from(*units), CURRENCY),
                    );
                    p.cost = Some(per_unit(*cost, day));
                    p
                }
                Leg::Sell { units, cost } => {
                    let mut p = Posting::new(
                        "Assets:Stock",
                        Amount::new(-Decimal::from(*units), CURRENCY),
                    );
                    p.cost = Some(per_unit(*cost, day));
                    p
                }
                Leg::Merge { units } => {
                    let mut p = Posting::new(
                        "Assets:Stock",
                        Amount::new(-Decimal::from(*units), CURRENCY),
                    );
                    p.cost = Some(CostSpec {
                        number: None,
                        currency: None,
                        date: None,
                        label: None,
                        merge: true,
                    });
                    p
                }
            };
            txn = txn.with_synthesized_posting(posting);
        }
        // Doomed against the ANCHOR commodity, not the generated one.
        //
        // It used to oversell the generated commodity, on the assumption that
        // overselling always
        // fails. It does not: a prefix of
        // `{*}` merges can empty the account, and an empty cost spec against an
        // empty account is an AUGMENTATION,
        // not a failed reduction — beancount's `book_reductions` makes the same
        // call (`if balance.is_reduced_by(units)`, else augment). So the
        // transaction succeeded, and this property test failed at random
        // depending on which prefix proptest generated. Reducing a commodity
        // the prefix cannot drain restores "this leg always fails" as a fact
        // rather than a hope.
        let mut doomed = Posting::new(
            "Assets:Stock",
            Amount::new(Decimal::from(-100_000), ANCHOR),
        );
        doomed.cost = Some(CostSpec {
            number: None,
            currency: None,
            date: None,
            label: None,
            merge: false,
        });
        txn = txn.with_synthesized_posting(doomed);

        // Some generated prefixes fail before the doomed leg (an ambiguous
        // match, an oversell of one lot). Either way the transaction is
        // rejected, and either way the account must be untouched.
        let result = engine.apply(&txn);
        prop_assert!(result.is_err(), "the doomed leg must reject the transaction");
        prop_assert_eq!(
            holdings(&engine),
            before,
            "a rejected transaction changed the account",
        );
    }
}
