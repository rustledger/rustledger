//! A table row keeps the posting it was read from, beside the row (#2442).
//!
//! `weight`, `cost` and `sum` of a column holding a posting's `position`
//! answer from that posting, through the default FROM's own functions,
//! lazily: only for the rows and columns a query reads. These tests pin what
//! the row origins must survive (ORDER BY, LIMIT, nesting, synthesized
//! `OPEN ON` transactions, a table moving to another executor) and what they
//! changed: no hidden columns, and a column repeated under one name answers
//! from the posting too.

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive};
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
2024-01-01 open Assets:E
2024-01-01 open Assets:C
2024-01-01 open Assets:B X "FIFO"
2024-01-01 open Assets:U Z "FIFO"

2024-01-02 * "priced"
  Assets:E  10 EUR @ 1.10 USD
  Assets:C

2024-01-03 * "priced again"
  Assets:E  10 EUR @ 1.20 USD
  Assets:C

2024-01-04 * "total lot"
  Assets:B  3 X {{500 USD}}
  Assets:C

2024-01-05 * "per-unit lot"
  Assets:U  4 Z {12.50 USD}
  Assets:C
"#;

fn booked(source: &str) -> Vec<Directive> {
    let parsed = rustledger_parser::parse(source);
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
    engine.register_account_methods(directives.iter());
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            engine
                .book_interpolate_apply(txn)
                .expect("the fixture books");
        }
    }
    directives
}

fn run(executor: &mut Executor<'_>, bql: &str) -> Vec<Vec<Value>> {
    let query = parse(bql).unwrap_or_else(|e| panic!("{bql}: {e:?}"));
    executor
        .execute(&query)
        .unwrap_or_else(|e| panic!("{bql}: {e}"))
        .rows
}

fn rows(directives: &[Directive], bql: &str) -> Vec<Vec<Value>> {
    run(&mut Executor::new(directives), bql)
}

/// A name a subquery gives two columns resolves to the last, as the value
/// path reads it; when that column holds the posting's `position`, it
/// answers from the posting. The hidden columns could not tell which column
/// an outer query meant, and kept the value path: `10 EUR` for
/// `10 EUR @ 1.10 USD`, where the default FROM gives `11.00 USD`.
#[test]
fn a_column_repeated_under_one_name_answers_from_the_posting() {
    let directives = booked(LEDGER);
    let direct = rows(
        &directives,
        "SELECT weight(position), cost(position) ORDER BY date, account",
    );
    for inner in [
        "SELECT date, account, position, position",
        "SELECT date, account, units(position) AS position, position",
        "SELECT *, position",
    ] {
        let bql = format!(
            "SELECT weight(position), cost(position) FROM ({inner}) ORDER BY date, account"
        );
        assert_eq!(rows(&directives, &bql), direct, "{bql}");
    }
    // The last column is the units, so the value path answers: no price.
    let units = rows(
        &directives,
        "SELECT weight(position) FROM (SELECT date, account, position, \
         units(position) AS position) WHERE account = 'Assets:E' ORDER BY date",
    );
    assert_eq!(
        units[0][0],
        Value::Amount(rustledger_core::Amount::new(
            rust_decimal_macros::dec!(10),
            "EUR"
        ))
    );
}

/// A table built from postings has exactly the columns its SELECT names:
/// it keeps the postings beside its rows, not in hidden columns.
#[test]
fn a_created_table_keeps_only_its_columns() {
    let directives = booked(LEDGER);
    let mut executor = Executor::new(&directives);
    run(&mut executor, "CREATE TABLE t AS SELECT account, position");
    run(&mut executor, "CREATE TABLE u (account, position)");
    run(&mut executor, "INSERT INTO u SELECT account, position");
    let tables = executor.take_created_tables();
    for name in ["t", "u"] {
        let table = tables.get(name).expect("created");
        assert_eq!(table.columns, ["account", "position"], "{name}");
        assert!(table.rows.iter().all(|r| r.len() == 2), "{name}");
    }
}

/// The row's posting follows it through the inner query's ORDER BY and
/// LIMIT, and through the transactions `OPEN ON`, `CLOSE` and `CLEAR`
/// synthesize, which have no place in the ledger.
#[test]
fn the_posting_follows_its_row_through_sorts_limits_and_synthesized_entries() {
    let directives = booked(LEDGER);
    for (from, order) in [
        ("", "ORDER BY date DESC, account LIMIT 5"),
        ("", "ORDER BY account, date"),
        ("FROM OPEN ON 2024-01-03", "ORDER BY date, account"),
        (
            "FROM OPEN ON 2024-01-03 CLOSE CLEAR",
            "ORDER BY date, account",
        ),
    ] {
        let direct = rows(
            &directives,
            &format!("SELECT date, account, weight(position), cost(position) {from} {order}"),
        );
        assert!(!direct.is_empty(), "{from} {order}");
        let through = rows(
            &directives,
            &format!(
                "SELECT date, account, weight(position), cost(position) \
                 FROM (SELECT date, account, position {from} {order})"
            ),
        );
        assert_eq!(through, direct, "{from} {order}");
        let nested = rows(
            &directives,
            &format!(
                "SELECT date, account, weight(p), cost(p) FROM \
                 (SELECT date, account, position AS p FROM \
                 (SELECT date, account, position {from} {order}))"
            ),
        );
        assert_eq!(nested, direct, "nested: {from} {order}");
    }
}

/// A created table carries to another executor (#2579) with its postings:
/// they are its own copies, not places in the ledger it was made from, so
/// over a ledger in a different order it still answers from them.
#[test]
fn a_created_table_answers_from_its_own_postings_in_another_executor() {
    let directives = booked(LEDGER);
    let bql = "SELECT account, weight(position), cost(position) FROM t";
    let mut maker = Executor::new(&directives);
    run(
        &mut maker,
        "CREATE TABLE t AS SELECT account, position WHERE account != 'Assets:C'",
    );
    let expected = run(&mut maker, bql);
    assert_eq!(
        expected[0][1],
        Value::Amount(rustledger_core::Amount::new(
            rust_decimal_macros::dec!(11.00),
            "USD",
        ))
    );

    let mut reversed = directives.clone();
    reversed.reverse();
    let mut other = Executor::new(&reversed);
    other.set_created_tables(maker.take_created_tables());
    assert_eq!(run(&mut other, bql), expected);
}

/// An INSERT naming a column twice writes the last value to it, so the
/// column holds a posting's `position` only when that last value is one.
#[test]
fn an_insert_naming_a_column_twice_keeps_the_last_value_and_its_origin() {
    let directives = booked(LEDGER);
    let create = "CREATE TABLE t (account, position)";
    let weight = "SELECT weight(position) FROM t";

    let mut executor = Executor::new(&directives);
    run(&mut executor, create);
    run(
        &mut executor,
        "INSERT INTO t (position, position) SELECT position, account WHERE account = 'Assets:E'",
    );
    let query = parse(weight).expect("parses");
    let err = executor
        .execute(&query)
        .expect_err("the column holds an account name, which has no weight");
    assert!(err.to_string().starts_with("type error"), "{err}");

    let mut executor = Executor::new(&directives);
    run(&mut executor, create);
    run(
        &mut executor,
        "INSERT INTO t (position, position) SELECT account, position WHERE account = 'Assets:E'",
    );
    assert_eq!(
        run(&mut executor, weight)[0][0],
        Value::Amount(rustledger_core::Amount::new(
            rust_decimal_macros::dec!(11.00),
            "USD"
        ))
    );
}
