//! Pipeline-boundary property tests for the query engine (#1235).
//!
//! Query result determinism: the same query over the same ledger must
//! produce the same rows every time — including stable row ordering and the
//! per-row GROUP BY key sidecar (`group_key`). This is the invariant the
//! `row_group_keys` non-DISTINCT bug (#1177) violated.
//!
//! Two paths in `executor::execution` matter here, and they are NOT the
//! same path:
//! - **Aggregation / GROUP BY runs sequentially** (`group_postings`), using
//!   a `std::HashMap` for buckets plus an explicit `key_order` vec to keep
//!   emission deterministic despite the map's random seed. The GROUP BY
//!   queries below exercise this path and the `group_key` sidecar.
//! - **Parallel evaluation** (`use_parallel`, rayon `par_iter`) is reached
//!   ONLY in the non-aggregate branch, when posting count >=
//!   `PARALLEL_THRESHOLD` (1000) and there are no window functions. So the
//!   plain-projection / DISTINCT queries — not GROUP BY — are what hit it.
//!
//! Two tests, deliberately split by scale:
//! - [`query_execution_is_deterministic`] runs many *small* generated
//!   ledgers through a spread of query shapes — broad shape coverage below
//!   the parallel threshold, including the sequential GROUP BY path.
//! - [`large_ledger_query_is_deterministic`] drives a ledger past
//!   `PARALLEL_THRESHOLD` so the non-aggregate **parallel** evaluation
//!   branch runs (via the projection / DISTINCT queries). rayon's `par_iter`
//!   preserves input order by contract, so this guards against a future
//!   refactor that loses that ordering (e.g. an unordered `par_extend`).
//!
//! Net: these guard against accidental dependence on hash-map iteration
//! order or parallel scheduling, not a per-run hashing seed.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, QueryResult, parse};

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

/// A spread of shapes: grouping/aggregation (the #1177 risk), DISTINCT,
/// ordered, and plain projection.
const QUERIES: &[&str] = &[
    "SELECT account, SUM(number) GROUP BY account",
    "SELECT account, SUM(number) GROUP BY account ORDER BY account",
    "SELECT DISTINCT account",
    "SELECT date, account, number",
];

/// Two executions agree iff their rows AND their per-row group-key sidecars
/// match. Comparing only `rows` would miss a divergence in the parallel
/// `row_group_keys` vector — precisely the #1177 failure mode.
fn results_match(a: &QueryResult, b: &QueryResult) -> bool {
    a.rows == b.rows && (0..a.rows.len()).all(|i| a.group_key(i) == b.group_key(i))
}

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

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn query_execution_is_deterministic(ledger in ledger_strategy()) {
        for q in QUERIES {
            let query = parse(q).expect("query parses");
            let r1 = Executor::new(&ledger).execute(&query).expect("first execution");
            let r2 = Executor::new(&ledger).execute(&query).expect("second execution");
            prop_assert!(
                results_match(&r1, &r2),
                "non-deterministic result (rows or group keys) for query: {}",
                q
            );
        }
    }
}

/// Build a ledger with enough postings to push the executor onto its
/// parallel evaluation path. `PARALLEL_THRESHOLD` is 1000 postings; each
/// transaction contributes 2, so `txn_count` of 600 yields 1200.
fn large_ledger(txn_count: usize) -> Vec<Directive> {
    let mut ds: Vec<Directive> = ACCOUNTS
        .iter()
        .map(|a| Directive::Open(Open::new(date(1), *a)))
        .collect();
    for i in 0..txn_count {
        // Rotate the leg account so GROUP BY has multiple non-trivial
        // buckets to populate (sequential path) and DISTINCT has >1 value.
        let acct = ACCOUNTS[i % ACCOUNTS.len()];
        let amt = Decimal::new(i64::try_from(i).unwrap() + 1, 2);
        let day = u32::try_from(i % 27).unwrap() + 1;
        ds.push(Directive::Transaction(
            Transaction::new(date(day), "t")
                .with_synthesized_posting(Posting::new(acct, Amount::new(amt, "USD")))
                .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(-amt, "USD"))),
        ));
    }
    ds
}

/// Determinism at scale, across both executor paths. 1200 postings clears
/// `PARALLEL_THRESHOLD`, so the non-aggregate queries (`SELECT date,
/// account, number` and `SELECT DISTINCT account`) run through the
/// rayon `par_iter` branch, while the GROUP BY queries run through the
/// sequential `group_postings` path (aggregation never goes parallel). We
/// execute each query many times with fresh executors and assert every run
/// matches the first — guarding both the parallel evaluation ordering and
/// the sequential grouping/`group_key` emission order.
#[test]
fn large_ledger_query_is_deterministic() {
    let ledger = large_ledger(600);
    // Sanity: we actually cleared the parallel threshold (1000 postings).
    let posting_count: usize = ledger
        .iter()
        .filter_map(|d| match d {
            Directive::Transaction(t) => Some(t.postings.len()),
            _ => None,
        })
        .sum();
    assert!(
        posting_count >= 1000,
        "expected >=1000 postings to exercise the parallel path, got {posting_count}"
    );

    for q in QUERIES {
        let query = parse(q).expect("query parses");
        let baseline = Executor::new(&ledger)
            .execute(&query)
            .expect("baseline execution");
        for run in 0..10 {
            let again = Executor::new(&ledger)
                .execute(&query)
                .expect("repeat execution");
            assert!(
                results_match(&baseline, &again),
                "non-deterministic parallel result (rows or group keys) on run {run} for query: {q}"
            );
        }
    }
}
