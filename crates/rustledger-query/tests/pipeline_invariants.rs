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

/// Magnitudes spanning three scales, not one uniform range.
///
/// The original `-1_000_000..1_000_000` made a value near the boundary
/// vanishingly rare: landing in `(0, 1]` needs `|n| <= 10^scale`, so at most
/// 1000 of two million draws — roughly 0.3 expected hits across a whole run.
/// A predicate bug at the boundary would have gone unseen, which sabotaging
/// the partition property is how I found out: swapping `number > 0` for
/// `number > 1` changed nothing, because there was nothing between them.
fn amount_strategy() -> impl Strategy<Value = i64> {
    prop_oneof![
        3 => -1_000_000i64..1_000_000,  // ordinary magnitudes
        2 => -1_000i64..1_000,          // small — puts values around 1
        1 => -5i64..5,                  // tiny — puts values either side of 0
    ]
}

/// A balanced two-posting transaction with a random leg account, amount,
/// and day.
fn txn_strategy() -> impl Strategy<Value = Transaction> {
    (1u32..28, 0usize..ACCOUNTS.len(), amount_strategy(), 0u32..3)
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

// ---------------------------------------------------------------------------
// Algebraic properties (#1902 Phase 1).
//
// The determinism properties above ask "does the same input give the same
// answer twice". These ask whether the answer is RIGHT, using relationships
// that must hold whatever the ledger contains — so they need no expected
// value, which is what makes them checkable over generated input.
//
// Miri excludes this crate for rowan reasons that are not going away, so this
// is the compensating coverage. It is also aimed where the crate has actually
// broken: #1177 was a grouping/parallel-path divergence, and the two bugs
// found by hand this cycle (#1963, #1966) were both in evaluation rather than
// parsing.
// ---------------------------------------------------------------------------

/// Every posting's number, straight from the executor, with no predicate.
fn all_numbers(ledger: &[Directive]) -> Vec<String> {
    let q = parse("SELECT number").expect("query parses");
    let r = Executor::new(ledger).execute(&q).expect("runs");
    let mut v: Vec<String> = r.rows.iter().map(|row| format!("{:?}", row[0])).collect();
    v.sort();
    v
}

fn numbers_where(ledger: &[Directive], predicate: &str) -> Vec<String> {
    let q = parse(&format!("SELECT number WHERE {predicate}")).expect("query parses");
    let r = Executor::new(ledger).execute(&q).expect("runs");
    let mut v: Vec<String> = r.rows.iter().map(|row| format!("{:?}", row[0])).collect();
    v.sort();
    v
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    /// `WHERE p` and `WHERE NOT p` must PARTITION the unfiltered rows.
    ///
    /// Neither half may invent a row, lose one, or claim the same row twice.
    /// A predicate that misevaluates in one direction only — the shape a
    /// three-valued-logic slip takes — shows up here as a sum that no longer
    /// reconstructs the whole.
    ///
    /// `number > 0` on purpose: the ledger strategy balances every transaction,
    /// so both sides are always populated and the property never degenerates
    /// into comparing something against nothing.
    #[test]
    fn a_predicate_and_its_negation_partition_the_rows(ledger in ledger_strategy()) {
        let all = all_numbers(&ledger);
        let yes = numbers_where(&ledger, "number > 0");
        let no = numbers_where(&ledger, "NOT (number > 0)");

        prop_assert!(!all.is_empty(), "the fixture must produce rows");
        prop_assert!(!yes.is_empty() && !no.is_empty(),
            "both halves must be populated or the partition is vacuous: \
             {} positive, {} non-positive", yes.len(), no.len());

        let mut union: Vec<String> = yes.iter().chain(no.iter()).cloned().collect();
        union.sort();
        prop_assert_eq!(
            union, all,
            "WHERE p and WHERE NOT p must reconstruct exactly the unfiltered rows"
        );
    }

    /// Grouping must not change the total, and each group must own its rows.
    ///
    /// Two assertions, because the weaker one alone would have missed #1177.
    ///
    /// The total is the obvious half: `SUM(number) GROUP BY account`, summed
    /// back over the groups, must equal the ungrouped `SUM(number)`.
    ///
    /// But a total is blind to the failure that actually happened — rows right
    /// while their group-key sidecar was not. Permute the sums across the
    /// account labels and the total still reconciles perfectly; every group is
    /// simply attributed to the wrong account. So the second assertion pins
    /// each group's sum against the rows that belong to that key.
    #[test]
    fn grouping_preserves_the_total(ledger in ledger_strategy()) {
        let grouped = parse("SELECT account, SUM(number) GROUP BY account").expect("parses");
        let total = parse("SELECT SUM(number)").expect("parses");
        let rows = parse("SELECT account, number").expect("parses");

        let g = Executor::new(&ledger).execute(&grouped).expect("runs");
        let t = Executor::new(&ledger).execute(&total).expect("runs");
        let r = Executor::new(&ledger).execute(&rows).expect("runs");

        prop_assert!(!g.rows.is_empty(), "grouping must produce at least one group");
        prop_assert_eq!(t.rows.len(), 1, "an ungrouped SUM is a single row");

        let sum_of_groups: Decimal = g
            .rows
            .iter()
            .map(|r| number_of(&format!("{:?}", r[1])))
            .sum();
        let ungrouped = number_of(&format!("{:?}", t.rows[0][0]));

        prop_assert_eq!(
            sum_of_groups, ungrouped,
            "the group sums must add up to the ungrouped total"
        );

        // Each group key must sum exactly the ungrouped rows carrying that key.
        for group in &g.rows {
            let key = format!("{:?}", group[0]);
            let reported = number_of(&format!("{:?}", group[1]));
            let expected: Decimal = r
                .rows
                .iter()
                .filter(|row| format!("{:?}", row[0]) == key)
                .map(|row| number_of(&format!("{:?}", row[1])))
                .sum();
            prop_assert_eq!(
                reported, expected,
                "group {} sums rows that are not its own", key
            );
        }
    }

    /// `ORDER BY` must permute, never add, drop or alter.
    ///
    /// Sorting is where a comparator that is not a total order silently loses
    /// or duplicates rows — and the null-ordering tests next door pin WHICH
    /// order, not that the multiset survived it.
    #[test]
    fn ordering_is_a_permutation(ledger in ledger_strategy()) {
        let unordered = parse("SELECT date, account, number").expect("parses");
        let ordered =
            parse("SELECT date, account, number ORDER BY number DESC").expect("parses");

        let u = Executor::new(&ledger).execute(&unordered).expect("runs");
        let o = Executor::new(&ledger).execute(&ordered).expect("runs");

        let key = |r: &Vec<rustledger_query::Value>| {
            r.iter().map(|v| format!("{v:?}")).collect::<Vec<_>>().join("|")
        };
        let mut a: Vec<String> = u.rows.iter().map(key).collect();
        let mut b: Vec<String> = o.rows.iter().map(key).collect();
        a.sort();
        b.sort();

        prop_assert!(!a.is_empty(), "the fixture must produce rows");
        prop_assert_eq!(a, b, "ORDER BY changed the multiset of rows, not just their order");
    }
}

/// The `number:` field of a rendered `Value`, as a `Decimal`.
fn number_of(rendered: &str) -> Decimal {
    let after = rendered
        .rsplit("number: ")
        .next()
        .filter(|_| rendered.contains("number: "))
        .unwrap_or(rendered);
    let text: String = after
        .trim_start_matches(|c: char| !c.is_ascii_digit() && c != '-')
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '.' || *c == '-')
        .collect();
    text.parse()
        .unwrap_or_else(|e| panic!("parsing {rendered:?}: {e}"))
}
