//! Regression: PIVOT BY names its columns the way bean-query does (#2217).
//!
//! Unlike the `BALANCES`/`JOURNAL` names (#2221) and the inventory slot layout
//! (#2222) -- which are a name-less query template and a column renderer, and
//! so are deliberately NOT matched -- these names are set in bean-query's
//! evaluator (`EvalPivot` in `query_compile.py`) and are visible through its
//! API, not just its CLI:
//!
//! ```text
//! [d[0] for d in conn.execute(q).description]
//!   -> ['account/year', '2024/sum(number)', '2024/count(number)', ...]
//! ```
//!
//! Each part is also the better answer on its own terms:
//!
//! * The key column spans two source columns, so naming it after only the
//!   first drops the spread column's name.
//! * Columns are emitted grouped by pivot value, so leading the name with the
//!   pivot value describes the layout the right way round.
//! * No spaces around the separator.
//!
//! Measured against beanquery 0.2.0.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, parse};

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

/// Two accounts, one posting each, in different years.
fn ledger() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
        Directive::Transaction(
            Transaction::new(date(2024, 6, 1), "a")
                .with_synthesized_posting(Posting::new("Assets:A", Amount::new(dec!(10), "USD")))
                .with_synthesized_posting(Posting::new("Equity:O", Amount::new(dec!(-10), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2025, 6, 1), "b")
                .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(5), "USD")))
                .with_synthesized_posting(Posting::new("Equity:O", Amount::new(dec!(-5), "USD"))),
        ),
    ]
}

fn columns(q: &str) -> Vec<String> {
    let dirs = ledger();
    let query = parse(q).expect("parse");
    let mut ex = Executor::new(&dirs);
    ex.execute(&query).expect("execute").columns
}

/// More than one non-pivot column: every value column is
/// `<pivot_value>/<column>`, grouped by pivot value.
///
/// bean-query's API reports exactly this list for the same query.
#[test]
fn multiple_value_columns_lead_with_the_pivot_value() {
    assert_eq!(
        columns(
            "SELECT account, year, sum(number), count(number) FROM #postings \
             GROUP BY account, year PIVOT BY account, year"
        ),
        vec![
            "account/year",
            "2024/sum(number)",
            "2024/count(number)",
            "2025/sum(number)",
            "2025/count(number)",
        ],
    );
}

/// Exactly one non-pivot column: bean-query drops the qualification entirely
/// and heads each column with the bare pivot value. `EvalPivot` only composes
/// a two-part name in its `nother > 1` branch. We already agreed here before
/// #2217 -- pinned so the multi-column fix did not collapse the two branches
/// into one.
#[test]
fn a_single_value_column_is_headed_by_the_bare_pivot_value() {
    assert_eq!(
        columns(
            "SELECT account, year, sum(number) FROM #postings \
             GROUP BY account, year PIVOT BY account, year"
        ),
        vec!["account/year", "2024", "2025"],
    );
}

/// The key column names BOTH source columns. Asserted separately from the
/// lists above because it is the one part that was wrong in both branches.
#[test]
fn the_key_column_names_the_key_and_the_spread() {
    for q in [
        "SELECT account, year, sum(number) FROM #postings \
         GROUP BY account, year PIVOT BY account, year",
        "SELECT account, year, sum(number), count(number) FROM #postings \
         GROUP BY account, year PIVOT BY account, year",
    ] {
        assert_eq!(
            columns(q).first().map(String::as_str),
            Some("account/year"),
            "the key column spans both source columns",
        );
    }
}

/// No spaces around the separator, in any branch. Pinned on its own because
/// the old format differed from bean-query by spacing as well as by order,
/// and a fix that only reversed the halves would still be wrong.
#[test]
fn the_separator_carries_no_spaces() {
    let all = columns(
        "SELECT account, year, sum(number), count(number) FROM #postings \
         GROUP BY account, year PIVOT BY account, year",
    )
    .join(",");
    assert!(
        !all.contains(" / ") && !all.contains(" /") && !all.contains("/ "),
        "the separator must be a bare `/`; got {all}",
    );
}
