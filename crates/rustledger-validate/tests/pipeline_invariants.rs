//! Pipeline-boundary property test for validation (#1235).
//!
//! Validation-pipeline determinism: the full early -> late -> finalize
//! sequence over the same ledger must produce the same errors (by code)
//! every run. Validators emit into per-currency/-account maps internally,
//! so this guards against nondeterministic error emission (e.g. a future
//! refactor that surfaces errors in hash-map order). Generated ledgers mix
//! valid (balanced), unbalanced, and unopened-account transactions across
//! several currencies — including transactions balanced in two currencies
//! at once — so a variety of codes and the per-currency map ordering are
//! all exercised.
//!
//! (The booking-coupled early-vs-late equivalence from #1235 is handled
//! separately on top of the public one-shot `book` helper added in #1362.)

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_validate::{ErrorCode, ValidationOptions, ValidationSession};

fn date(day: u32) -> NaiveDate {
    rustledger_core::naive_date(2024, 1, day).unwrap()
}

const ACCOUNTS: &[&str] = &[
    "Assets:Bank",
    "Expenses:Food",
    "Income:Salary",
    "Liabilities:Card",
];

/// A small static currency set so transactions span multiple currencies —
/// validators bucket residuals/errors per currency, so multiple currencies
/// are needed to exercise cross-currency map-ordering determinism.
const CURRENCIES: &[&str] = &["USD", "EUR", "CAD"];

fn amt(n: i64, scale: u32, ccy: usize) -> Amount {
    Amount::new(Decimal::new(n, scale), CURRENCIES[ccy])
}

/// A spread of transaction shapes so a variety of error codes — and the
/// valid path — are all exercised:
/// - **unbalanced**: two independent random postings (random currencies),
///   usually `TransactionUnbalanced`, on random (sometimes unopened)
///   accounts.
/// - **balanced single-currency**: a posting and its exact negation — the
///   valid path.
/// - **balanced multi-currency**: a balanced USD leg plus a balanced EUR
///   leg, so the per-currency residual map holds two buckets at once.
fn txn() -> impl Strategy<Value = Transaction> {
    prop_oneof![
        // Unbalanced / random.
        (
            1u32..28,
            0usize..ACCOUNTS.len(),
            0usize..ACCOUNTS.len(),
            0usize..CURRENCIES.len(),
            -1_000_000i64..1_000_000,
            0u32..3,
            0usize..CURRENCIES.len(),
            -1_000_000i64..1_000_000,
            0u32..3,
        )
            .prop_map(|(day, a, b, c1, n1, s1, c2, n2, s2)| {
                Transaction::new(date(day), "u")
                    .with_synthesized_posting(Posting::new(ACCOUNTS[a], amt(n1, s1, c1)))
                    .with_synthesized_posting(Posting::new(ACCOUNTS[b], amt(n2, s2, c2)))
            }),
        // Balanced, single currency (valid path).
        (
            1u32..28,
            0usize..ACCOUNTS.len(),
            0usize..ACCOUNTS.len(),
            0usize..CURRENCIES.len(),
            1i64..1_000_000,
            0u32..3,
        )
            .prop_map(|(day, a, b, c, n, s)| {
                let x = amt(n, s, c);
                let neg = Amount::new(-x.number, x.currency.clone());
                Transaction::new(date(day), "b")
                    .with_synthesized_posting(Posting::new(ACCOUNTS[a], x))
                    .with_synthesized_posting(Posting::new(ACCOUNTS[b], neg))
            }),
        // Balanced across two currencies at once.
        (
            1u32..28,
            0usize..ACCOUNTS.len(),
            0usize..ACCOUNTS.len(),
            1i64..1_000_000,
            0u32..3,
            1i64..1_000_000,
            0u32..3,
        )
            .prop_map(|(day, a, b, n1, s1, n2, s2)| {
                let usd = Amount::new(Decimal::new(n1, s1), "USD");
                let eur = Amount::new(Decimal::new(n2, s2), "EUR");
                Transaction::new(date(day), "m")
                    .with_synthesized_posting(Posting::new(ACCOUNTS[a], usd.clone()))
                    .with_synthesized_posting(Posting::new(
                        ACCOUNTS[a],
                        Amount::new(-usd.number, "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(ACCOUNTS[b], eur.clone()))
                    .with_synthesized_posting(Posting::new(
                        ACCOUNTS[b],
                        Amount::new(-eur.number, "EUR"),
                    ))
            }),
    ]
}

fn ledger() -> impl Strategy<Value = Vec<Directive>> {
    // Open a random subset of accounts so some postings reference unopened
    // ones; then a handful of transactions.
    (
        prop::collection::vec(any::<bool>(), ACCOUNTS.len()),
        prop::collection::vec(txn(), 1..10),
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

fn run_pipeline(directives: &[Directive]) -> Vec<ErrorCode> {
    let today = date(28);
    let session = ValidationSession::new(ValidationOptions::default());
    let (session, early) = session.run_early(directives, today);
    // Postings are explicit here, so booking is a no-op; late runs on the
    // same directives.
    let (session, late) = session.run_late(directives, today);
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
    fn validation_pipeline_is_deterministic(directives in ledger()) {
        let first = run_pipeline(&directives);
        let second = run_pipeline(&directives);
        prop_assert_eq!(first, second, "validation produced different error codes across runs");
    }
}
