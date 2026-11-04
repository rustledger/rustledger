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
        // Refused even when no row matches, as bean-query's compiler is.
        "BALANCES AT nosuchfn WHERE account ~ 'XYZ'",
        "BALANCES AT sum WHERE account ~ 'XYZ'",
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

/// The amounts in a cell, as `(number, currency)` pairs sorted by currency.
fn amounts(value: &Value) -> Vec<(Decimal, String)> {
    let mut out: Vec<(Decimal, String)> = match value {
        Value::Amount(a) => vec![(a.number, a.currency.to_string())],
        Value::Position(p) => vec![(p.units.number, p.units.currency.to_string())],
        Value::Inventory(inv) => inv
            .positions()
            .map(|p| (p.units.number, p.units.currency.to_string()))
            .collect(),
        other => panic!("not an amount: {other:?}"),
    };
    out.sort_by(|a, b| a.1.cmp(&b.1));
    out
}

fn d(n: i64) -> Decimal {
    Decimal::from(n)
}

/// An account holding lots at a USD cost, lots at an EUR cost and EUR cash:
/// bean-query values each position in its own cost currency (#2826).
const MIXED: &str = "\
2024-01-01 open Assets:Mix
2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 * \"vht\"
  Assets:Mix  2 VHT {100 USD}
  Assets:Bank  -200 USD
2024-01-03 * \"abc\"
  Assets:Mix  3 ABC {10 EUR}
  Assets:Bank  -30 EUR
2024-01-04 * \"eur in\"
  Assets:Mix  50 EUR
  Equity:Opening  -50 EUR
2024-01-05 * \"eur out\"
  Assets:Mix  -20 EUR
  Equity:Opening  20 EUR
2024-01-06 price VHT 130 USD
2024-01-06 price ABC 12 EUR
2024-01-06 price ABC 15 USD
2024-01-06 price EUR 1.20 USD
";

fn account_cell(result: &QueryResult, account: &str, column: usize) -> Value {
    result
        .rows
        .iter()
        .find(|r| matches!(&r[0], Value::String(a) if a == account))
        .unwrap_or_else(|| panic!("a row for {account}"))[column]
        .clone()
}

/// bean-query: `Assets:Mix  66 EUR  260 USD`, not one sum in USD.
#[test]
fn test_balances_at_value_values_each_position_in_its_own_cost_currency() {
    let result = run(MIXED, "BALANCES AT value").expect("runs");
    assert_eq!(
        amounts(&account_cell(&result, "Assets:Mix", 1)),
        vec![(d(66), "EUR".into()), (d(260), "USD".into())]
    );
    let summed = run(
        MIXED,
        "SELECT value(sum(position)) WHERE account = 'Assets:Mix'",
    )
    .expect("runs");
    assert_eq!(
        amounts(&summed.rows[0][0]),
        vec![(d(66), "EUR".into()), (d(260), "USD".into())],
        "value() of an inventory, outside BALANCES"
    );
}

/// bean-query's `value(balance)` on each JOURNAL row: `260 USD`, then
/// `36 EUR 260 USD`, `86 EUR 260 USD`, `66 EUR 260 USD`.
#[test]
fn test_journal_at_value_balance_values_each_position() {
    let result = run(MIXED, "JOURNAL 'Assets:Mix' AT value").expect("runs");
    let balances: Vec<_> = result.rows.iter().map(|r| amounts(&r[6])).collect();
    assert_eq!(
        balances,
        vec![
            vec![(d(260), "USD".into())],
            vec![(d(36), "EUR".into()), (d(260), "USD".into())],
            vec![(d(86), "EUR".into()), (d(260), "USD".into())],
            vec![(d(66), "EUR".into()), (d(260), "USD".into())],
        ]
    );
}

/// A non-linear `AT f`: bean-query sums `abs(position)` per posting, so the
/// bank shows 1540 USD (every movement), not `abs` of its 670 USD balance.
const MOVEMENTS: &str = "\
2024-01-01 open Assets:Bank
2024-01-01 open Assets:Stock
2024-01-01 open Expenses:Food
2024-01-01 open Equity:Opening
2024-01-01 * \"open\"
  Assets:Bank  1000 USD
  Equity:Opening
2024-01-02 * \"buy\"
  Assets:Stock  4 VHT {100 USD}
  Assets:Bank  -400 USD
2024-01-03 * \"food\"
  Expenses:Food  35 USD
  Assets:Bank  -35 USD
2024-01-04 * \"refund\"
  Expenses:Food  -5 USD
  Assets:Bank  5 USD
2024-01-05 * \"sell\"
  Assets:Stock  -1 VHT {100 USD}
  Assets:Bank  100 USD
";

#[test]
fn test_balances_at_abs_sums_abs_of_each_posting() {
    let result = run(MOVEMENTS, "BALANCES AT abs").expect("runs");
    assert_eq!(
        amounts(&account_cell(&result, "Assets:Bank", 1)),
        vec![(d(1540), "USD".into())]
    );
    assert_eq!(
        amounts(&account_cell(&result, "Expenses:Food", 1)),
        vec![(d(40), "USD".into())]
    );
    assert_eq!(
        amounts(&account_cell(&result, "Equity:Opening", 1)),
        vec![(d(1000), "USD".into())]
    );
    assert_eq!(
        amounts(&account_cell(&result, "Assets:Stock", 1)),
        vec![(d(5), "VHT".into())]
    );
}

/// bean-query: `abs(position)` 4 then 1 VHT, `abs(balance)` 4 then 3 VHT.
#[test]
fn test_journal_at_abs_applies_abs_per_row() {
    let result = run(MOVEMENTS, "JOURNAL 'Assets:Stock' AT abs").expect("runs");
    let cells: Vec<_> = result
        .rows
        .iter()
        .map(|r| (amounts(&r[5]), amounts(&r[6])))
        .collect();
    assert_eq!(
        cells,
        vec![
            (vec![(d(4), "VHT".into())], vec![(d(4), "VHT".into())]),
            (vec![(d(1), "VHT".into())], vec![(d(3), "VHT".into())]),
        ]
    );
}

/// An aggregate inside BETWEEN or a set is still an aggregate in WHERE.
#[test]
fn test_where_refuses_an_aggregate_inside_between_or_a_set() {
    for query in [
        "SELECT date WHERE number BETWEEN 0 AND count(*)",
        "SELECT date WHERE number IN (count(*), 2)",
    ] {
        match run(TWO, query) {
            Err(QueryError::Aggregation(message)) => {
                assert!(
                    message.contains("aggregates are not allowed in WHERE clause"),
                    "{query}: {message}"
                );
            }
            other => panic!("{query}: expected a refusal, got {other:?}"),
        }
    }
}

/// An `AT f` that does not map a position to an amount, position or
/// inventory is refused before any row is read, as bean-query's compiler
/// refuses `number(position)` (`no function matches`). `AT number` summed
/// bare numbers across currencies; `AT currency` failed only on a row.
/// `JOURNAL ... AT str` is stricter than bean-query, which prints the
/// position as text: rledger's `str()` does not take a position yet (#2822),
/// so it is refused rather than failing on the first row.
#[test]
fn test_at_refuses_a_function_that_does_not_give_an_amount() {
    for f in ["number", "currency", "str"] {
        for query in [
            format!("BALANCES AT {f}"),
            format!("BALANCES AT {f} WHERE account ~ 'XYZ'"),
            format!("JOURNAL 'Assets:Stock' AT {f}"),
            format!("JOURNAL 'Nothing:Matches' AT {f}"),
        ] {
            match run(MOVEMENTS, &query) {
                Err(QueryError::UnknownFunction(sig)) => {
                    assert_eq!(sig, format!("{f}(position)"), "{query}");
                }
                other => panic!("{query}: expected a refusal, got {other:?}"),
            }
        }
    }
}

/// The functions that do map a position to an amount, position or inventory
/// still work. `weight` is an rledger extension: bean-query has no
/// `weight(position)` and refuses `AT weight`.
#[test]
fn test_at_keeps_the_amount_valued_functions() {
    for f in ["value", "abs", "neg", "weight", "cost", "units"] {
        for query in [
            format!("BALANCES AT {f}"),
            format!("JOURNAL 'Assets:Stock' AT {f}"),
        ] {
            let result = run(MOVEMENTS, &query).unwrap_or_else(|e| panic!("{query}: {e}"));
            assert!(!result.rows.is_empty(), "{query}");
        }
    }
}
