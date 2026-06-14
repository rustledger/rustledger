//! Pipeline-boundary property tests for the query engine (#1235).
//!
//! Query result determinism: the same query over the same ledger must
//! produce the same rows every time — including stable row ordering, even
//! for aggregations/grouping where the engine may use hashing or parallel
//! evaluation internally. This is exactly the invariant the
//! `row_group_keys` parallel non-DISTINCT bug (#1177) violated; a fresh
//! `Executor` per run gives each run an independent hashing seed, so a
//! non-deterministically-ordered result surfaces here.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, parse};

fn date(day: u32) -> NaiveDate {
    rustledger_core::naive_date(2024, 1, day).unwrap()
}

/// A small fixed account universe so generated ledgers stay realistic and
/// shrink to readable counterexamples.
const ACCOUNTS: &[&str] = &[
    "Expenses:Food",
    "Expenses:Transport",
    "Income:Salary",
    "Assets:Bank",
];

/// A balanced two-posting transaction with a random leg account, amount,
/// and day.
fn txn_strategy() -> impl Strategy<Value = Transaction> {
    (
        1u32..28,
        0usize..ACCOUNTS.len(),
        -1_000_000i64..1_000_000,
        0u32..3,
    )
        .prop_filter("non-zero amount", |(_, _, n, _)| *n != 0)
        .prop_map(|(day, acct, n, scale)| {
            let amt = Decimal::new(n, scale);
            Transaction::new(date(day), "t")
                .with_synthesized_posting(Posting::new(ACCOUNTS[acct], Amount::new(amt, "USD")))
                .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(-amt, "USD")))
        })
}

fn ledger_strategy() -> impl Strategy<Value = Vec<Directive>> {
    proptest::collection::vec(txn_strategy(), 1..12).prop_map(|txns| {
        let mut ds: Vec<Directive> = ACCOUNTS
            .iter()
            .map(|a| Directive::Open(Open::new(date(1), *a)))
            .collect();
        ds.extend(txns.into_iter().map(Directive::Transaction));
        ds
    })
}

/// A spread of shapes: grouping/aggregation (the #1177 risk), DISTINCT,
/// ordered, and plain projection.
const QUERIES: &[&str] = &[
    "SELECT account, SUM(number) GROUP BY account",
    "SELECT account, SUM(number) GROUP BY account ORDER BY account",
    "SELECT DISTINCT account",
    "SELECT date, account, number",
];

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn query_execution_is_deterministic(ledger in ledger_strategy()) {
        for q in QUERIES {
            let query = parse(q).expect("query parses");
            let r1 = Executor::new(&ledger).execute(&query).expect("first execution");
            let r2 = Executor::new(&ledger).execute(&query).expect("second execution");
            prop_assert_eq!(
                &r1.rows,
                &r2.rows,
                "non-deterministic result (including row order) for query: {}",
                q
            );
        }
    }
}
