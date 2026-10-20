//! `getitem()`'s default argument (#2699), and `neg()` / `abs()` over
//! positions and inventories (#2703), with the other functions bean-query
//! defines over them (`possign()`, `filter_currency()`), as it does in
//! `beanquery/query_env.py`. Expected values are bean-query's (beanquery
//! 0.2.0 on beancount 3.2.3) on the same ledger.

use rust_decimal_macros::dec;
use rustledger_booking::BookingEngine;
use rustledger_core::{Amount, BookingMethod, Cost, Directive, Inventory, Position};
use rustledger_query::{Executor, Value, parse};

/// The issues' ledger, plus a lot held at cost and a key with no value.
const LEDGER: &str = r#"
2026-01-01 open Assets:Bank
2026-01-01 open Assets:Stock HOOL "FIFO"
2026-01-01 open Expenses:Food

2026-01-02 * "Shop" "Groceries"
  concept: "SHOP 123"
  empty:
  Assets:Bank   -10.00 EUR
  Expenses:Food  10.00 EUR

2026-01-03 * "Market" "Fruit"
  Assets:Bank   -100 MAD @ 0.09 EUR
    note: "priced"
  Expenses:Food  100 MAD

2026-01-04 * "Buy"
  Assets:Stock  10 HOOL {10 USD}
  Assets:Bank  -100 USD
"#;

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

fn run(bql: &str) -> Result<Vec<Vec<Value>>, String> {
    let directives = booked();
    let mut executor = Executor::new(&directives);
    executor
        .execute(&parse(bql).expect("query parses"))
        .map(|result| result.rows)
        .map_err(|e| e.to_string())
}

fn rows(bql: &str) -> Vec<Vec<Value>> {
    run(bql).unwrap_or_else(|e| panic!("{bql}: {e}"))
}

fn s(text: &str) -> Value {
    Value::String(text.to_string())
}

fn amount(number: rust_decimal::Decimal, currency: &str) -> Amount {
    Amount::new(number, currency)
}

fn inventory(positions: Vec<Position>) -> Value {
    Value::Inventory(std::sync::Arc::new(
        Inventory::try_from_positions(positions).unwrap(),
    ))
}

/// The #2699 query: the default stands in for the missing key.
#[test]
fn getitem_default_for_a_missing_key() {
    assert_eq!(
        rows(
            "SELECT narration, getitem(entry.meta, 'concept', narration) \
             WHERE account ~ '^(Assets:Bank|Expenses)' AND narration != 'Buy'"
        ),
        vec![
            vec![s("Groceries"), s("SHOP 123")],
            vec![s("Groceries"), s("SHOP 123")],
            vec![s("Fruit"), s("Fruit")],
            vec![s("Fruit"), s("Fruit")],
        ]
    );
    // On the posting's own metadata, with a default of another type.
    let got: Vec<Value> = rows("SELECT getitem(meta, 'note', 5) WHERE narration = 'Fruit'")
        .into_iter()
        .map(|row| row[0].clone())
        .collect();
    assert_eq!(got, vec![s("priced"), Value::Integer(5)]);
}

/// Python's `dict.get(key, default)`: a key that is present keeps its value
/// even when that value is NULL (`empty:` with nothing after it), and a NULL
/// container is NULL whatever the default.
#[test]
fn getitem_default_only_for_an_absent_key() {
    assert_eq!(
        rows(
            "SELECT getitem(entry.meta, 'empty', 'dflt'), getitem(entry.meta, 'missing', 'dflt') \
             WHERE narration = 'Groceries' LIMIT 1"
        ),
        vec![vec![Value::Null, s("dflt")]]
    );
    assert_eq!(
        rows("SELECT getitem(NULL, 'k', 'dflt') LIMIT 1"),
        vec![vec![Value::Null]]
    );
}

/// The default applies to an inventory read by currency too.
#[test]
fn getitem_default_on_an_inventory() {
    assert_eq!(
        rows("SELECT getitem(balance, 'JPY', 0), getitem(balance, 'EUR', 0) LIMIT 1"),
        vec![vec![
            Value::Integer(0),
            Value::Amount(amount(dec!(-10.00), "EUR")),
        ]]
    );
}

/// Two arguments still work, and four are refused.
#[test]
fn getitem_arity() {
    assert_eq!(
        rows("SELECT getitem(entry.meta, 'missing') LIMIT 1"),
        vec![vec![Value::Null]]
    );
    let err = run("SELECT getitem(meta, 'note', 1, 2)").unwrap_err();
    assert!(err.contains("expected 2 or 3 argument(s), got 4"), "{err}");
}

/// The #2703 query: `neg(position)` and `neg(balance)`, a multi-currency
/// inventory.
#[test]
fn neg_position_and_running_balance() {
    assert_eq!(
        rows(
            "SELECT neg(position), neg(balance) \
             WHERE account = 'Assets:Bank' AND narration != 'Buy'"
        ),
        vec![
            vec![
                Value::Position(Box::new(Position::simple(amount(dec!(10.00), "EUR")))),
                inventory(vec![Position::simple(amount(dec!(10.00), "EUR"))]),
            ],
            vec![
                Value::Position(Box::new(Position::simple(amount(dec!(100), "MAD")))),
                inventory(vec![
                    Position::simple(amount(dec!(10.00), "EUR")),
                    Position::simple(amount(dec!(100), "MAD")),
                ]),
            ],
        ]
    );
}

/// A position keeps its cost under `neg()` and `abs()`, as beancount's
/// `-Position` and `abs(Position)` do, and so does an inventory's.
#[test]
fn neg_and_abs_keep_the_cost() {
    let lot = |units| {
        Position::with_cost(
            amount(units, "HOOL"),
            Cost::new(dec!(10), "USD").with_date(rustledger_core::naive_date(2026, 1, 4).unwrap()),
        )
    };
    assert_eq!(
        rows(
            "SELECT neg(position), abs(neg(position)), neg(sum(position)) \
             WHERE account = 'Assets:Stock' GROUP BY position"
        ),
        vec![vec![
            Value::Position(Box::new(lot(dec!(-10)))),
            Value::Position(Box::new(lot(dec!(10)))),
            inventory(vec![lot(dec!(-10))]),
        ]]
    );
}

/// `abs()` of an inventory takes each position's absolute value. The
/// running `balance` sums only the rows `WHERE` keeps, so the second row's
/// is both bank postings.
#[test]
fn abs_of_an_inventory() {
    let got = rows("SELECT abs(balance) WHERE account = 'Assets:Bank' AND narration != 'Buy'");
    assert_eq!(
        got[1],
        vec![inventory(vec![
            Position::simple(amount(dec!(10.00), "EUR")),
            Position::simple(amount(dec!(100), "MAD")),
        ])]
    );
}

/// Numbers and amounts are unchanged, and NULL stays NULL.
#[test]
fn neg_and_abs_of_scalars() {
    assert_eq!(
        rows(
            "SELECT neg(number), neg(units(position)), abs(neg(number)), neg(NULL), abs(NULL) \
             WHERE account = 'Assets:Bank' AND narration = 'Groceries'"
        ),
        vec![vec![
            Value::Number(dec!(10.00)),
            Value::Amount(amount(dec!(10.00), "EUR")),
            Value::Number(dec!(10.00)),
            Value::Null,
            Value::Null,
        ]]
    );
}

/// `possign()` takes a position and an inventory too, as bean-query does:
/// negated for a credit-normal account, unchanged otherwise.
#[test]
fn possign_of_positions_and_inventories() {
    let mad = |n| Position::simple(amount(n, "MAD"));
    assert_eq!(
        rows(
            "SELECT possign(position, 'Income:X'), possign(position, account), \
             possign(balance, 'Liabilities:X') \
             WHERE account = 'Expenses:Food' AND narration = 'Fruit'"
        ),
        vec![vec![
            Value::Position(Box::new(mad(dec!(-100)))),
            Value::Position(Box::new(mad(dec!(100)))),
            inventory(vec![mad(dec!(-100))]),
        ]]
    );
}

/// `filter_currency()` of a position is the position when its units are in
/// that currency, else NULL.
#[test]
fn filter_currency_of_a_position() {
    assert_eq!(
        rows(
            "SELECT filter_currency(position, 'MAD'), filter_currency(position, 'EUR') \
             WHERE account = 'Expenses:Food' AND narration = 'Fruit'"
        ),
        vec![vec![
            Value::Position(Box::new(Position::simple(amount(dec!(100), "MAD")))),
            Value::Null,
        ]]
    );
}
