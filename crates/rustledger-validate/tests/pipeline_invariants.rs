//! Pipeline-boundary property test for validation (#1235).
//!
//! Validation-pipeline determinism: the full early -> late -> finalize
//! sequence over the same ledger must produce the same errors (by code)
//! every run. Validators emit into per-currency/-account maps internally,
//! so this guards against nondeterministic error emission (e.g. a future
//! refactor that surfaces errors in hash-map order). Generated ledgers mix
//! valid, unbalanced, and unopened-account transactions so a variety of
//! codes are exercised.
//!
//! (The booking-coupled early-vs-late equivalence from #1235 needs a
//! one-shot `book` helper that isn't public today; left as a follow-up.)

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

fn amount() -> impl Strategy<Value = Amount> {
    (-1_000_000i64..1_000_000, 0u32..3)
        .prop_map(|(n, scale)| Amount::new(Decimal::new(n, scale), "USD"))
}

/// Two explicit postings with independent random amounts — often
/// unbalanced (`TransactionUnbalanced`), on random accounts (some may be
/// unopened, giving `AccountNotOpen`).
fn txn() -> impl Strategy<Value = Transaction> {
    (
        1u32..28,
        0usize..ACCOUNTS.len(),
        0usize..ACCOUNTS.len(),
        amount(),
        amount(),
    )
        .prop_map(|(day, a, b, amt_a, amt_b)| {
            Transaction::new(date(day), "t")
                .with_synthesized_posting(Posting::new(ACCOUNTS[a], amt_a))
                .with_synthesized_posting(Posting::new(ACCOUNTS[b], amt_b))
        })
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
