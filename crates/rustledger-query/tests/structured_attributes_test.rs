//! Attribute access on bean-query's structured types (#2700, #2702).
//!
//! bean-query's `Amount`, `Position`, `Cost`, `Transaction`, `Open` and
//! `Close` structures expose the fields of beancount's namedtuples. rledger
//! had attributes only on `entry`: `position.units.number` failed with "not
//! structured", and `#accounts` held bare dates in `open` and `close`, so
//! `open.date` failed. `entry.accounts` was silently NULL. Expected values
//! are bean-query's (beanquery 0.2.0 on beancount 3.2.3) on the same ledger.

use rust_decimal_macros::dec;
use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive, NaiveDate};
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
2020-01-01 open Assets:Bank USD
  bank: "x"
2020-01-01 open Assets:Stock HOOL "FIFO"
2020-01-01 open Income:Gains
2020-01-01 open Equity:Open
2020-01-02 * "Init"
  Assets:Bank 1000.00 USD
  Equity:Open
2020-01-03 * "Buy"
  Assets:Stock 10 HOOL {10 USD, 2020-01-03, "lot1"}
  Assets:Bank -100 USD
2020-01-04 price HOOL 12 USD
2020-01-05 balance Assets:Bank 900.00 USD
2020-01-09 * "Sell"
  Assets:Stock -5 HOOL {10 USD} @ 12 USD
  Assets:Bank 60 USD
  Income:Gains
2020-12-31 close Equity:Open
"#;

/// Parse and book the ledger as the loader does, so a sale's cost carries
/// the lot's date and label.
fn booked() -> Vec<Directive> {
    let parsed = rustledger_parser::parse(LEDGER);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(BookingMethod::Strict);
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

fn rows(bql: &str) -> Vec<Vec<Value>> {
    let directives = booked();
    let mut executor = Executor::new(&directives);
    executor
        .execute(&parse(bql).expect("query parses"))
        .unwrap_or_else(|e| panic!("{bql}: {e}"))
        .rows
}

fn error(bql: &str) -> String {
    let directives = booked();
    let mut executor = Executor::new(&directives);
    executor
        .execute(&parse(bql).expect("query parses"))
        .expect_err(bql)
        .to_string()
}

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

fn s(text: &str) -> Value {
    Value::String(text.to_string())
}

/// The #2702 query, and every field of a position, its units and its cost.
#[test]
fn position_units_and_cost_attributes() {
    assert_eq!(
        rows(
            "SELECT position.units.number, position.units.currency, position.cost.number, \
             position.cost.currency, position.cost.date, position.cost.label \
             WHERE account = 'Assets:Stock'"
        ),
        vec![
            vec![
                Value::Number(dec!(10)),
                s("HOOL"),
                Value::Number(dec!(10)),
                s("USD"),
                Value::Date(date(2020, 1, 3)),
                s("lot1"),
            ],
            vec![
                Value::Number(dec!(-5)),
                s("HOOL"),
                Value::Number(dec!(10)),
                s("USD"),
                Value::Date(date(2020, 1, 3)),
                s("lot1"),
            ],
        ]
    );
}

/// `position.units` is the units amount, the value `units(position)` gives.
#[test]
fn position_units_is_an_amount() {
    let got = rows("SELECT position.units, units(position) WHERE account = 'Assets:Stock'");
    for row in got {
        assert!(matches!(row[0], Value::Amount(_)), "{row:?}");
        assert_eq!(row[0], row[1]);
    }
}

/// A position without a cost has a NULL `cost`, and NULL fields under it.
#[test]
fn position_without_cost() {
    assert_eq!(
        rows(
            "SELECT position.units.number, position.cost, position.cost.number \
             WHERE narration = 'Init' AND account = 'Assets:Bank'"
        ),
        vec![vec![Value::Number(dec!(1000.00)), Value::Null, Value::Null]]
    );
}

/// Every amount-valued column and function is structured the same way.
#[test]
fn amount_attributes() {
    assert_eq!(
        rows(
            "SELECT price.number, price.currency, weight.number, weight.currency, \
             cost(position).currency, value(position).number \
             WHERE account = 'Assets:Stock'"
        ),
        vec![
            vec![
                Value::Null,
                Value::Null,
                Value::Number(dec!(100)),
                s("USD"),
                s("USD"),
                Value::Number(dec!(120)),
            ],
            vec![
                Value::Number(dec!(12)),
                s("USD"),
                Value::Number(dec!(-50)),
                s("USD"),
                s("USD"),
                Value::Number(dec!(-60)),
            ],
        ]
    );
    assert_eq!(
        rows("SELECT amount.number, amount.currency FROM #balances"),
        vec![vec![Value::Number(dec!(900.00)), s("USD")]]
    );
    assert_eq!(
        rows("SELECT amount.number, amount.currency FROM #prices"),
        vec![vec![Value::Number(dec!(12)), s("USD")]]
    );
}

/// Attributes work where an expression is evaluated: WHERE, an aggregate's
/// argument, GROUP BY, and over a subquery's column.
#[test]
fn attributes_in_every_clause() {
    assert_eq!(
        rows(
            "SELECT position.units.currency, sum(position.units.number) \
             WHERE position.cost.label = 'lot1' GROUP BY position.units.currency"
        ),
        vec![vec![s("HOOL"), Value::Number(dec!(5))]]
    );
    assert_eq!(
        rows(
            "SELECT p.cost.date FROM (SELECT position AS p WHERE account = 'Assets:Stock') LIMIT 1"
        ),
        vec![vec![Value::Date(date(2020, 1, 3))]]
    );
    assert_eq!(
        rows("SELECT position.units.number FROM #postings WHERE account = 'Assets:Stock'"),
        vec![vec![Value::Number(dec!(10))], vec![Value::Number(dec!(-5))]]
    );
}

/// A position, amount or cost has a fixed set of fields; any other is an
/// error, as bean-query's compile error is, never a silent NULL.
#[test]
fn unknown_attribute_on_a_typed_value_errors() {
    assert!(error("SELECT position.foo").contains("position has no attribute 'foo'"));
    assert!(error("SELECT position.units.foo").contains("amount has no attribute 'foo'"));
    assert!(error("SELECT price.units").contains("amount has no attribute 'units'"));
}

/// The #2700 query: `open` and `close` are the directives.
#[test]
fn accounts_open_and_close_are_structured() {
    assert_eq!(
        rows("SELECT account, open.date, close.date FROM #accounts ORDER BY 1"),
        vec![
            vec![s("Assets:Bank"), Value::Date(date(2020, 1, 1)), Value::Null],
            vec![
                s("Assets:Stock"),
                Value::Date(date(2020, 1, 1)),
                Value::Null
            ],
            vec![
                s("Equity:Open"),
                Value::Date(date(2020, 1, 1)),
                Value::Date(date(2020, 12, 31)),
            ],
            vec![
                s("Income:Gains"),
                Value::Date(date(2020, 1, 1)),
                Value::Null
            ],
        ]
    );
    assert_eq!(
        rows(
            "SELECT open.account, open.currencies, open.booking, open.meta['bank'] \
             FROM #accounts WHERE account ~ '^Assets'"
        ),
        vec![
            vec![
                s("Assets:Bank"),
                Value::StringSet(vec!["USD".into()]),
                Value::Null,
                s("x"),
            ],
            vec![
                s("Assets:Stock"),
                Value::StringSet(vec!["HOOL".into()]),
                s("FIFO"),
                Value::Null,
            ],
        ]
    );
    assert_eq!(
        rows("SELECT close.account FROM #accounts WHERE close IS NOT NULL"),
        vec![vec![s("Equity:Open")]]
    );
}

/// beancount's `get_account_open_close` keeps the EARLIEST directive of
/// each kind for an account opened or closed twice: not the last one seen
/// (`Assets:A`), and not the first one seen (`Assets:B`).
#[test]
fn accounts_keep_the_earliest_directive() {
    let source = "2020-01-01 open Assets:A\n\
                  2020-03-01 open Assets:A\n\
                  2020-05-01 close Assets:A\n\
                  2020-06-01 close Assets:A\n\
                  2020-03-01 open Assets:B\n\
                  2020-01-01 open Assets:B\n\
                  2020-06-01 close Assets:B\n\
                  2020-05-01 close Assets:B\n";
    let directives: Vec<Directive> = rustledger_parser::parse(source)
        .directives
        .iter()
        .map(|d| (**d).clone())
        .collect();
    let mut executor = Executor::new(&directives);
    let got = executor
        .execute(&parse("SELECT account, open.date, close.date FROM #accounts").unwrap())
        .unwrap()
        .rows;
    let earliest = |account: &str| {
        vec![
            s(account),
            Value::Date(date(2020, 1, 1)),
            Value::Date(date(2020, 5, 1)),
        ]
    };
    assert_eq!(got, vec![earliest("Assets:A"), earliest("Assets:B")]);
}

/// bean-query's `Transaction` structure has `accounts`; it was NULL.
#[test]
fn entry_accounts() {
    assert_eq!(
        rows("SELECT entry.accounts WHERE narration = 'Sell' LIMIT 1"),
        vec![vec![Value::StringSet(vec![
            "Assets:Bank".into(),
            "Assets:Stock".into(),
            "Income:Gains".into(),
        ])]]
    );
    assert_eq!(
        rows("SELECT entry.accounts FROM #postings WHERE narration = 'Init' LIMIT 1"),
        vec![vec![Value::StringSet(vec![
            "Assets:Bank".into(),
            "Equity:Open".into(),
        ])]]
    );
}

/// A date is bean-query's `Date` structure: `year`, `month` and `day`, at
/// any depth (`position.cost.date.year`, `open.date.year`), and nothing else.
#[test]
fn date_attributes() {
    assert_eq!(
        rows(
            "SELECT date.year, date.month, date.day, position.cost.date.year, entry.date.month \
             WHERE account = 'Assets:Stock'"
        ),
        vec![
            [2020, 1, 3, 2020, 1].map(Value::Integer).to_vec(),
            [2020, 1, 9, 2020, 1].map(Value::Integer).to_vec(),
        ]
    );
    assert_eq!(
        rows("SELECT open.date.year, year(open.date) FROM #accounts LIMIT 1"),
        vec![vec![Value::Integer(2020), Value::Integer(2020)]]
    );
    assert!(error("SELECT date.weekday").contains("date has no attribute 'weekday'"));
}
