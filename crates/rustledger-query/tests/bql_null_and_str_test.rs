//! NULL in, NULL out for scalar functions (#2820), `number()` / `currency()`
//! of an inventory that holds nothing (#2821), and `#entries` tags/links and
//! `str()` of compound values (#2822), each against beanquery 0.2.0 /
//! beancount 3.2.3.

use rustledger_core::Directive;
use rustledger_query::{Executor, Value, parse};

/// The first transaction has no payee, so `payee` is NULL on its rows; no
/// account is closed, so `close_date(account)` is a NULL date everywhere.
const LEDGER: &str = r#"
2024-01-01 open Assets:Bank
2024-01-01 open Assets:Stock
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening  -10 USD
2024-01-03 * "Acme" "second" #t1 ^l1
  Assets:Bank      5 USD
  Equity:Opening   -5 USD
2024-01-04 * "Acme" "back to zero"
  Assets:Bank    -15 USD
  Equity:Opening   15 USD
2024-01-05 * "Broker" "lot"
  Assets:Stock    2 HOOL {100 USD, 2024-01-05, "lot"}
    note: "first lot"
  Equity:Opening -200 USD
2024-01-06 balance Assets:Bank 0 USD
"#;

fn directives() -> Vec<Directive> {
    let parsed = rustledger_parser::parse(LEDGER);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    parsed.directives.iter().map(|d| (**d).clone()).collect()
}

fn run(bql: &str) -> Vec<Vec<Value>> {
    let directives = directives();
    let mut executor = Executor::new(&directives);
    executor
        .execute(&parse(bql).unwrap_or_else(|e| panic!("{bql:?}: {e}")))
        .unwrap_or_else(|e| panic!("{bql:?}: {e}"))
        .rows
}

/// One column of every row.
fn column(bql: &str) -> Vec<Value> {
    run(bql).into_iter().map(|mut r| r.remove(0)).collect()
}

fn s(text: &str) -> Value {
    Value::String(text.to_string())
}

/// A function given a NULL argument answers NULL for that row instead of
/// failing the whole query, as bean-query's `@function` wrapper does. On the
/// NULL-payee rows bean-query prints a blank for every one of these.
#[test]
fn test_function_null_argument_gives_null() {
    for expr in [
        "substr(payee, 0, 2)",
        "substring(payee, 0, 2)",
        "maxwidth(payee, 5)",
        "date(payee)",
        "parse_date(payee)",
        "startswith(payee, 'A')",
        "endswith(payee, 'e')",
        "splitcomp(payee, ':', 0)",
        "root(payee, 1)",
        "date_trunc(payee, date)",
        "interval(payee)",
        "weekday(close_date(account))",
        "ymonth(close_date(account))",
        "date_add(close_date(account), 1)",
        "date_diff(close_date(account), date)",
        "date_part('year', close_date(account))",
        "date_trunc('year', close_date(account))",
        "getitem(meta, payee)",
    ] {
        let values = column(&format!("SELECT {expr} WHERE date = 2024-01-02"));
        assert_eq!(values.len(), 2, "{expr}");
        assert!(
            values.iter().all(|v| matches!(v, Value::Null)),
            "{expr}: {values:?}"
        );
    }
    // The rows with a payee still compute.
    assert_eq!(
        column("SELECT substr(payee, 0, 2) WHERE date = 2024-01-03"),
        [s("Ac"), s("Ac")]
    );
    assert_eq!(
        column("SELECT maxwidth(payee, 5) WHERE date = 2024-01-03"),
        [s("Acme"), s("Acme")]
    );
}

/// The NULL guard in WHERE: both operands of AND are evaluated, so before,
/// the SUBSTR error escaped even though `payee IS NOT NULL` was false.
#[test]
fn test_function_null_argument_in_where_does_not_fail_the_query() {
    let rows = column(
        "SELECT account WHERE payee IS NOT NULL AND substr(payee, 0, 2) = 'Ac' \
         AND date = 2024-01-03",
    );
    assert_eq!(rows, [s("Assets:Bank"), s("Equity:Opening")]);
}

/// NULL does not paper over a wrong argument count.
#[test]
fn test_function_null_argument_with_a_wrong_arity_is_still_an_error() {
    let directives = directives();
    let mut executor = Executor::new(&directives);
    for bql in ["SELECT substr(payee)", "SELECT weekday(payee, 1)"] {
        assert!(executor.execute(&parse(bql).unwrap()).is_err(), "{bql}");
    }
}

/// An inventory that holds nothing (a balance back at zero, or a sum that
/// nets out) has no number and no currency: NULL, as `get` and `only` read
/// it. Before, `number` said `0` and `currency` named `USD`.
#[test]
fn test_number_and_currency_of_an_inventory_holding_nothing_are_null() {
    let rows = run(
        "SELECT number(balance), currency(balance), get(balance, 'USD') \
         WHERE account = 'Assets:Bank'",
    );
    assert_eq!(rows[0][0], Value::Number(10.into()));
    assert_eq!(rows[0][1], s("USD"));
    assert_eq!(rows[2], [Value::Null, Value::Null, Value::Null]);
    let rows = run("SELECT number(sum(position)), currency(sum(position)) \
         WHERE account ~ 'Bank'");
    assert_eq!(rows[0], [Value::Null, Value::Null]);
}

/// On `#entries`, a directive kind without tags or links has them NULL, as
/// bean-query's `getattr(entry, 'tags', None)`; a transaction has a set,
/// empty or not. bean-query: three opens and the balance are `TRUE` for
/// `tags IS NULL` with a blank `length(tags)`; the transactions are `FALSE`.
#[test]
fn test_entries_tags_and_links_are_null_where_the_directive_has_none() {
    let rows =
        run("SELECT type, tags IS NULL, links IS NULL, length(tags), str(tags) FROM #entries");
    for row in &rows {
        let carries = row[0] == s("transaction");
        assert_eq!(row[1], Value::Boolean(!carries), "{row:?}");
        assert_eq!(row[2], Value::Boolean(!carries), "{row:?}");
        if !carries {
            assert_eq!(row[3], Value::Null, "{row:?}");
            assert_eq!(row[4], Value::Null, "{row:?}");
        }
    }
    assert_eq!(
        column("SELECT count(*) FROM #entries WHERE tags IS NULL"),
        [Value::Integer(4)]
    );
    // A transaction's tags stay a set; `str` lists them as the cell does.
    let tagged = run("SELECT length(tags), str(tags), str(links) FROM #entries WHERE 't1' IN tags");
    assert_eq!(tagged, [vec![Value::Integer(1), s("t1"), s("l1")]]);
}

/// `str()` of a position or inventory is Python's `str()`, as bean-query
/// prints it; before, both were a type error.
#[test]
fn test_str_renders_positions_and_inventories_as_bean_query() {
    let rows = run("SELECT str(position), str(balance) WHERE account = 'Assets:Bank'");
    assert_eq!(rows[0], [s("10 USD"), s("(10 USD)")]);
    assert_eq!(rows[2], [s("-15 USD"), s("()")]);
    let rows = run("SELECT str(position), str(balance) WHERE account = 'Assets:Stock'");
    assert_eq!(
        rows[0],
        [
            s("2 HOOL {100 USD, 2024-01-05, \"lot\"}"),
            s("(2 HOOL {100 USD, 2024-01-05, \"lot\"})")
        ]
    );
    // Sorted by beancount's `Position.sortkey`, USD before HOOL, and an
    // aggregate that nets a currency to zero leaves it out.
    assert_eq!(
        column("SELECT str(sum(position))"),
        [s("(-200 USD, 2 HOOL {100 USD, 2024-01-05, \"lot\"})")]
    );
    assert_eq!(
        column("SELECT str(sum(position)) WHERE account ~ 'Opening'"),
        [s("(-200 USD)")]
    );
    // Metadata no longer errors.
    assert!(matches!(
        &column("SELECT str(meta) LIMIT 1")[0],
        Value::String(_)
    ));
}

/// The other NULL readers bean-query answers NULL (or the default) for:
/// `meta` and its kin on a NULL key, `joinstr` of a NULL set, and a
/// three-argument `getitem` whose key is NULL.
#[test]
fn test_meta_joinstr_and_getitem_on_null() {
    let rows = run("SELECT meta(payee), entry_meta(payee), any_meta(payee), \
         getitem(meta, payee, 'd') WHERE date = 2024-01-02");
    assert_eq!(rows[0], [Value::Null, Value::Null, Value::Null, s("d")]);
    let rows = run("SELECT type, joinstr(tags) FROM #entries");
    assert_eq!(rows[0], [s("open"), Value::Null]);
}

/// `str()` of metadata or an entry is the cell's own text, deliberately not
/// bean-query's Python repr (`{'note': 'first lot', ...}`,
/// `Transaction(meta=..., ...)`).
#[test]
fn test_str_of_meta_and_entry_is_the_cell_text() {
    let rows = run("SELECT str(meta), str(entry) WHERE account = 'Assets:Stock'");
    assert_eq!(rows[0][0], s("{note: first lot}"));
    assert_eq!(
        rows[0][1],
        s(
            "{accounts: Assets:Stock, Equity:Opening, date: 2024-01-05, flag: *, links: , \
             meta: {}, narration: lot, payee: Broker, tags: }"
        )
    );
}

/// A NULL container gives NULL even with a NULL key and a default:
/// bean-query's `GetItem3` returns None for a None container before it reads
/// the key, and prints a blank for `getitem(currency_meta(payee), payee, 'd')`
/// on a row with no payee. The NULL-key arm answered the default for it.
/// bean-query refuses the literal `getitem(NULL, NULL, 'd')` at compile time
/// (`getitem(nonetype, nonetype, str)`); here it is NULL, as main gave it.
#[test]
fn test_getitem_null_container_wins_over_the_default() {
    let rows = run("SELECT getitem(currency_meta(payee), payee, 'd') WHERE date = 2024-01-02");
    assert!(!rows.is_empty());
    assert!(rows.iter().all(|r| r[0] == Value::Null), "{rows:?}");
    assert_eq!(
        column("SELECT getitem(NULL, NULL, 'd') LIMIT 1"),
        [Value::Null]
    );
}
