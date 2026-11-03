//! Three places where BQL answered something plausible and wrong instead of
//! what bean-query (beanquery 0.2.0 / beancount 3.2.3) answers. Every expected
//! value below is bean-query's on the same ledger.
//!
//! - #2826: `BALANCES AT value` / `JOURNAL ... AT value` ignored the AT clause
//!   and showed units.
//! - #2827: aggregates in WHERE, as a GROUP BY expression or reference, and
//!   aggregates of aggregates were accepted; bean-query refuses them.
//! - #2828: `AND` / `OR` read NULL as FALSE, and `first()` returned a leading
//!   NULL; bean-query propagates NULL its own way and `first()` skips NULLs.

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Decimal, Directive};
use rustledger_query::{Executor, QueryError, QueryResult, Value, parse};

/// Parse `source` and book it the way the loader does.
fn booked(source: &str) -> Vec<Directive> {
    let parsed = rustledger_parser::parse(source);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
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

fn run(source: &str, query: &str) -> Result<QueryResult, QueryError> {
    let directives = booked(source);
    let query = parse(query).expect("query should parse");
    Executor::new(&directives).execute(&query)
}

/// The USD in an amount, position or inventory cell; `None` for any other.
fn usd(value: &Value) -> Option<Decimal> {
    match value {
        Value::Amount(a) if a.currency.as_str() == "USD" => Some(a.number),
        Value::Position(p) if p.units.currency.as_str() == "USD" => Some(p.units.number),
        Value::Inventory(inv) => {
            let mut usd = None;
            for p in inv.positions() {
                if p.units.currency.as_str() != "USD" {
                    return None;
                }
                *usd.get_or_insert(Decimal::ZERO) += p.units.number;
            }
            usd
        }
        _ => None,
    }
}

const PRICED: &str = "\
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-01 * \"x\"
  Assets:Bank     1000 USD
  Equity:Opening
2024-01-02 * \"buy\"
  Assets:Stock  4 VHT {100.00 USD}
  Assets:Bank
2024-01-02 price VHT 120.00 USD
";

/// #2826: bean-query gives `480.00 USD` for the stock and `600.00 USD` for
/// the bank.
#[test]
fn test_balances_at_value_converts_at_the_latest_price() {
    let result = run(PRICED, "BALANCES AT value").expect("runs");
    let row = |account: &str| {
        result
            .rows
            .iter()
            .find(|r| matches!(&r[0], Value::String(a) if a == account))
            .unwrap_or_else(|| panic!("a row for {account}"))
            .clone()
    };
    assert_eq!(usd(&row("Assets:Stock")[1]), Some(Decimal::from(480)));
    assert_eq!(usd(&row("Assets:Bank")[1]), Some(Decimal::from(600)));
}

/// #2826: bean-query's JOURNAL is `value(position), value(balance)`: both
/// `480.00 USD` on the purchase row.
#[test]
fn test_journal_at_value_converts_position_and_balance() {
    let result = run(PRICED, "JOURNAL 'Assets:Stock' AT value").expect("runs");
    assert_eq!(result.rows.len(), 1);
    let row = &result.rows[0];
    assert_eq!(usd(&row[5]), Some(Decimal::from(480)), "position: {row:?}");
    assert_eq!(usd(&row[6]), Some(Decimal::from(480)), "balance: {row:?}");
}

/// #2826: an AT function that does not exist, or an aggregate, is an error,
/// as bean-query's compiler refuses `f(position)`, even with no matching row.
#[test]
fn test_at_refuses_an_unknown_function_or_an_aggregate() {
    for query in [
        "BALANCES AT nosuchfn",
        "JOURNAL 'Assets:Stock' AT nosuchfn",
        "JOURNAL 'Nothing:Matches' AT nosuchfn",
        "BALANCES AT sum",
        "JOURNAL 'Assets:Stock' AT sum",
    ] {
        assert!(run(PRICED, query).is_err(), "{query} should be refused");
    }
}

const TWO: &str = "\
2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
2024-01-03 * \"Acme\" \"second\"
  Assets:Bank      5 USD
  Equity:Opening
";

/// #2827: each is a bean-query `CompilationError`, with the same reason.
#[test]
fn test_select_refuses_misplaced_aggregates() {
    for (query, reason) in [
        (
            "SELECT date WHERE count(*) > 1",
            "aggregates are not allowed in WHERE clause",
        ),
        (
            "SELECT date GROUP BY count(*)",
            "GROUP-BY expressions may not be aggregates",
        ),
        (
            "SELECT account, count(*) GROUP BY 2",
            "GROUP-BY expressions may not reference aggregates",
        ),
        (
            "SELECT account, count(*) AS c GROUP BY c",
            "GROUP-BY expressions may not reference aggregates",
        ),
        (
            "SELECT sum(cost(sum(position)))",
            "aggregates of aggregates are not allowed",
        ),
    ] {
        match run(TWO, query) {
            Err(QueryError::Aggregation(message)) => {
                assert!(message.contains(reason), "{query}: {message}");
            }
            other => panic!("{query}: expected a refusal, got {other:?}"),
        }
    }
}

/// #2827: the right places for an aggregate still work.
#[test]
fn test_select_keeps_aggregates_where_they_belong() {
    for query in [
        "SELECT account, count(*) GROUP BY account HAVING count(*) > 1",
        "SELECT account, count(*) GROUP BY 1",
        "SELECT units(sum(position))",
        "SELECT account, sum(position) GROUP BY account ORDER BY account",
    ] {
        assert!(run(TWO, query).is_ok(), "{query}");
    }
}

fn first_row(query: &str) -> Vec<Value> {
    run(TWO, query).expect("runs").rows[0].clone()
}

/// #2828: bean-query's `EvalAnd` / `EvalOr`. AND: the first NULL is NULL, the
/// first FALSE before any NULL is FALSE. OR: any TRUE is TRUE, else NULL if an
/// operand was NULL.
#[test]
fn test_and_or_propagate_null_as_bean_query_does() {
    let t = Value::Boolean(true);
    let f = Value::Boolean(false);
    assert_eq!(
        first_row("SELECT NULL AND TRUE, NULL AND FALSE, FALSE AND NULL, TRUE AND NULL LIMIT 1"),
        vec![Value::Null, Value::Null, f, Value::Null]
    );
    assert_eq!(
        first_row("SELECT NULL OR TRUE, NULL OR FALSE, FALSE OR NULL, TRUE OR NULL LIMIT 1"),
        vec![t.clone(), Value::Null, Value::Null, t]
    );
}

/// #2828: a NULL condition still drops the row in WHERE.
#[test]
fn test_where_drops_a_row_whose_condition_is_null() {
    let rows = run(TWO, "SELECT date, payee WHERE payee = 'Acme' OR NULL")
        .expect("runs")
        .rows;
    assert_eq!(rows.len(), 2, "only the Acme postings: {rows:?}");
}

/// #2828: `first()` skips NULLs (beanquery's `First.update`); `last()` does
/// not need to.
#[test]
fn test_first_skips_a_leading_null() {
    let acme = Value::String("Acme".to_string());
    assert_eq!(
        first_row("SELECT first(payee), last(payee)"),
        vec![acme.clone(), acme]
    );
}
