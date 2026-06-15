//! Booking-coupled validation phase-consistency property test (#1235).
//!
//! The real load pipeline is `early-validate(raw) -> book -> late-validate(booked)`:
//! `run_late`'s own contract requires booking to have filled in elided
//! amounts and cost specs first. The earlier validation determinism test
//! (`pipeline_invariants.rs`) used only explicit postings, so booking was a
//! no-op there — this test closes that gap with the public
//! [`rustledger_booking::book`] one-shot helper, generating ledgers whose
//! transactions need interpolation and cost-spec booking (augmentations
//! that drive `book` past its no-cost-spec fast path). Lot *reduction*
//! matching is covered by `rustledger-booking`'s own unit tests, not here.
//!
//! Two invariants:
//! 1. **Determinism** — the full early->book->late sequence yields the same
//!    error codes every run.
//! 2. **Booking idempotence at the pipeline boundary** — re-booking the
//!    already-booked directives does not change what late validation sees
//!    (`late(book(book(L))) == late(book(L))`), i.e. booking reaches a
//!    fixed point that validation agrees on.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_booking::book;
use rustledger_core::{
    Amount, BookingMethod, CostNumber, CostSpec, Directive, NaiveDate, Open, Posting,
    PriceAnnotation, Transaction,
};
use rustledger_validate::{ErrorCode, ValidationOptions, ValidationSession};

fn date(day: u32) -> NaiveDate {
    rustledger_core::naive_date(2024, 1, day).unwrap()
}

const ACCOUNTS: &[&str] = &[
    "Assets:Cash",
    "Assets:Stock",
    "Expenses:Food",
    "Income:Salary",
];

fn amount(currency: &'static str) -> impl Strategy<Value = Amount> {
    (1i64..100_000, 0u32..3)
        .prop_map(move |(n, scale)| Amount::new(Decimal::new(n, scale), currency))
}

/// Transactions that exercise the booker:
/// - `Elided`: one explicit posting + one auto posting interpolation fills.
/// - `Priced`: a priced stock posting + an auto cash posting.
/// - `Cost`: a stock buy carrying an explicit per-unit `{N USD}` cost spec +
///   an auto cash posting. Drives `BookingEngine::book` past its no-cost-spec
///   fast path into the real cost-filling / position-accumulation machinery
///   (an augmentation — no prior inventory, so it always books).
/// - `TotalCost`: a buy with a `{{ T USD }}` total cost. Booking rewrites
///   `Total` into `PerUnitFromTotal`, so re-booking exercises a cost
///   representation that genuinely changes during the first book — this is
///   where the idempotence assertion has teeth.
///
/// Lot *reductions* (sells that must match a lot) are covered by the
/// `book_partitions_failed_transaction` unit test rather than here, since
/// generating a sell that matches a prior buy under Strict is awkward in a
/// property strategy.
///
/// Random accounts mean some postings hit unopened accounts.
fn txn() -> impl Strategy<Value = Transaction> {
    prop_oneof![
        (
            1u32..28,
            0usize..ACCOUNTS.len(),
            0usize..ACCOUNTS.len(),
            amount("USD")
        )
            .prop_map(|(day, a, b, amt)| {
                Transaction::new(date(day), "elided")
                    .with_synthesized_posting(Posting::new(ACCOUNTS[a], amt))
                    .with_synthesized_posting(Posting::auto(ACCOUNTS[b]))
            }),
        (1u32..28, amount("HOOL"), amount("USD")).prop_map(|(day, units, price)| {
            Transaction::new(date(day), "priced")
                .with_synthesized_posting(
                    Posting::new("Assets:Stock", units).with_price(PriceAnnotation::unit(price)),
                )
                .with_synthesized_posting(Posting::auto("Assets:Cash"))
        }),
        (1u32..28, amount("HOOL"), 1i64..100_000, 0u32..3).prop_map(|(day, units, n, scale)| {
            let cost = CostSpec::empty()
                .with_number(CostNumber::PerUnit {
                    value: Decimal::new(n, scale),
                })
                .with_currency("USD");
            Transaction::new(date(day), "cost")
                .with_synthesized_posting(Posting::new("Assets:Stock", units).with_cost(cost))
                .with_synthesized_posting(Posting::auto("Assets:Cash"))
        }),
        // Total-cost buy (`{{ T USD }}`). Booking rewrites `Total` into
        // `PerUnitFromTotal` (per-unit = total / units) — the cost
        // representation that actually *changes* during booking, so this is
        // where the `late(book(book(L))) == late(book(L))` fixed-point
        // assertion has real teeth (the `PerUnit` shape above is stable by
        // construction and can't exercise that rewrite).
        (1u32..28, amount("HOOL"), 1i64..1_000_000, 0u32..2).prop_map(|(day, units, n, scale)| {
            let cost = CostSpec::empty()
                .with_number(CostNumber::Total {
                    value: Decimal::new(n, scale),
                })
                .with_currency("USD");
            Transaction::new(date(day), "total_cost")
                .with_synthesized_posting(Posting::new("Assets:Stock", units).with_cost(cost))
                .with_synthesized_posting(Posting::auto("Assets:Cash"))
        }),
    ]
}

fn ledger() -> impl Strategy<Value = Vec<Directive>> {
    (
        prop::collection::vec(any::<bool>(), ACCOUNTS.len()),
        prop::collection::vec(txn(), 1..8),
    )
        .prop_map(|(open_mask, txns)| {
            let mut ds: Vec<Directive> = ACCOUNTS
                .iter()
                .zip(open_mask)
                .filter(|(_, open)| *open)
                .map(|(a, _)| Directive::Open(Open::new(date(1), *a)))
                .collect();
            ds.extend(txns.into_iter().map(Directive::Transaction));
            ds
        })
}

/// Run the real coupled pipeline: early on raw, book, late on booked.
fn run_pipeline(raw: &[Directive]) -> Vec<ErrorCode> {
    let today = date(28);
    let session = ValidationSession::new(ValidationOptions::default());
    let (session, early) = session.run_early(raw, today);
    let booked = book(raw, BookingMethod::Strict).booked;
    let (session, late) = session.run_late(&booked, today);
    let pad = session.finalize();
    early
        .iter()
        .chain(&late)
        .chain(&pad)
        .map(|e| e.code)
        .collect()
}

/// Late validation over directives that were booked twice — used to check
/// the pipeline-level booking fixed point.
fn run_pipeline_double_booked(raw: &[Directive]) -> Vec<ErrorCode> {
    let today = date(28);
    let session = ValidationSession::new(ValidationOptions::default());
    let (session, early) = session.run_early(raw, today);
    let once = book(raw, BookingMethod::Strict).booked;
    let twice = book(&once, BookingMethod::Strict).booked;
    let (session, late) = session.run_late(&twice, today);
    let pad = session.finalize();
    early
        .iter()
        .chain(&late)
        .chain(&pad)
        .map(|e| e.code)
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn coupled_pipeline_is_deterministic(directives in ledger()) {
        let first = run_pipeline(&directives);
        let second = run_pipeline(&directives);
        prop_assert_eq!(first, second, "early->book->late produced different error codes across runs");
    }

    #[test]
    fn booking_is_idempotent_at_pipeline_boundary(directives in ledger()) {
        let once = run_pipeline(&directives);
        let twice = run_pipeline_double_booked(&directives);
        prop_assert_eq!(once, twice, "re-booking changed what late validation saw");
    }
}
