//! `FIRST(balance)` sees a fully-accumulated running balance.
//!
//! `balance` is a stateful column: evaluating it advances a running inventory.
//! beanquery's `FIRST.update` evaluates its operand only on a group's first row,
//! so postings after that row never reach the accumulator and later groups read
//! a balance that skipped them — beanquery#279. Its answer changes depending on
//! what else appears in the SELECT list, because adding `LAST(balance)` forces
//! evaluation on every row.
//!
//! rledger pre-computes the balance per row, so `FIRST` and `LAST` always agree
//! about what the running balance was, and the aggregate cannot be perturbed by
//! its neighbors in the SELECT list.
//!
//! This is pinned here because the compatibility corpus can no longer catch it.
//! `tests/compatibility/bql-queries.toml` selects `LAST(balance)` alongside
//! `FIRST(balance)` precisely so beanquery evaluates correctly and the suites
//! agree — which means the corpus no longer exercises the bare-`FIRST` shape at
//! all. Without this test, a change to our accumulation would be invisible in
//! both places.
//!
//! The fixture mirrors the worked example in that file: three postings in one
//! month, four in the next, all +10 EUR, so the running balance is 10/20/30 then
//! 40/50/60/70. `FIRST` per month is 10 and 40. beanquery answers 40 only when
//! forced; unforced it says 20, which is March's first posting plus May's first
//! posting — the four rows it never evaluated.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// Three postings on `march_day`, four on `may_day`, each +10.00 EUR.
fn ledger() -> Vec<Directive> {
    let mut dirs = vec![
        Directive::Open(Open::new(date(2018, 1, 1), "Assets:Test")),
        Directive::Open(Open::new(date(2018, 1, 1), "Equity:Opening-Balance")),
    ];
    for (month, day, count) in [(3u32, 17u32, 3), (5, 16, 4)] {
        for _ in 0..count {
            dirs.push(Directive::Transaction(
                Transaction::new(date(2018, month, day), "Test")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Test",
                        Amount::new(dec!(10.00), "EUR"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Equity:Opening-Balance",
                        Amount::new(dec!(-10.00), "EUR"),
                    )),
            ));
        }
    }
    dirs
}

fn run(query_str: &str) -> Vec<Vec<Value>> {
    let dirs = ledger();
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(&dirs);
    executor.execute(&query).expect("query should execute").rows
}

/// The single EUR amount held in a row's inventory cell.
fn eur(rows: &[Vec<Value>], row: usize, col: usize) -> rustledger_core::Decimal {
    let inv = match &rows[row][col] {
        Value::Inventory(inv) => inv,
        other => panic!("expected an Inventory at row {row} col {col}, got {other:?}"),
    };
    let positions = inv.position_list();
    assert_eq!(
        positions.len(),
        1,
        "expected exactly one position, got {positions:?}"
    );
    assert_eq!(positions[0].units.currency.as_str(), "EUR");
    positions[0].units.number
}

#[test]
fn first_balance_reflects_every_prior_posting() {
    let rows = run(
        "SELECT year, month, FIRST(balance) WHERE account ~ '^Assets' \
         ORDER BY year, month LIMIT 12",
    );
    assert_eq!(rows.len(), 2, "expected one row per month, got {rows:?}");
    assert_eq!(
        eur(&rows, 0, 2),
        dec!(10.00),
        "March's first posting is the first balance"
    );
    assert_eq!(
        eur(&rows, 1, 2),
        dec!(40.00),
        "May's first balance must include all three March postings — 20.00 here \
         would mean the accumulator skipped rows, which is beanquery#279"
    );
}

/// The aggregate must not depend on what else is selected. This is the property
/// beanquery lacks, and the reason its answer for May moves between 20 and 40.
#[test]
fn first_balance_is_unaffected_by_a_neighboring_aggregate() {
    let bare = run(
        "SELECT year, month, FIRST(balance) WHERE account ~ '^Assets' \
         ORDER BY year, month LIMIT 12",
    );
    let forced = run(
        "SELECT year, month, FIRST(balance), LAST(balance) WHERE account ~ '^Assets' \
         ORDER BY year, month LIMIT 12",
    );
    assert_eq!(bare.len(), forced.len());
    for row in 0..bare.len() {
        assert_eq!(
            eur(&bare, row, 2),
            eur(&forced, row, 2),
            "row {row}: FIRST(balance) changed when LAST(balance) was added to \
             the SELECT list"
        );
    }
    // And LAST is the end-of-month balance, confirming the accumulator ran to
    // completion rather than stopping at each group's first row.
    assert_eq!(eur(&forced, 0, 3), dec!(30.00));
    assert_eq!(eur(&forced, 1, 3), dec!(70.00));
}
