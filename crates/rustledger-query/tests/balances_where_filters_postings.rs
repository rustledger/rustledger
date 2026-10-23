//! `BALANCES WHERE` filters the POSTINGS before they are summed, as in
//! bean-query (#2630).
//!
//! bean-query's BALANCES is `SELECT account, SUM(position) ... GROUP BY
//! account` with the WHERE on the postings (`transform_balances`), and its
//! compiler joins the FROM expression to that WHERE with AND. rledger applied
//! the WHERE to the result rows, where only `account` and the total exist, so
//! `WHERE year = 2024` or `WHERE narration ~ 'salary'` saw nothing to filter.
//!
//! Every expected value on [`LEDGER`] is beanquery 0.2.0's (beancount 3.2.3)
//! on the same ledger. The AVERAGE ledger is rledger's own: beancount does
//! not book AVERAGE.

use std::path::Path;

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_query::executor::SummaryAccounts;
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"2023-01-01 open Assets:Bank USD
2023-01-01 open Assets:Stock X
2023-01-01 open Income:Salary USD
2023-01-01 open Expenses:Food USD
2023-01-01 open Equity:Opening USD

2023-01-05 * "Employer" "Salary jan"
  Assets:Bank      1000.00 USD
  Income:Salary   -1000.00 USD

2023-06-01 * "Shop" "Lunch"
  Expenses:Food      20.00 USD
  Assets:Bank       -20.00 USD

2023-07-01 * "Broker" "Buy"
  Assets:Stock      2 X {100 USD}
  Assets:Bank      -200.00 USD

2024-01-05 * "Employer" "Salary 2024"
  Assets:Bank      1500.00 USD
  Income:Salary   -1500.00 USD

2024-02-01 * "Shop" "Dinner"
  Expenses:Food      35.00 USD
  Assets:Bank       -35.00 USD

2024-03-01 * "Broker" "Buy more"
  Assets:Stock      1 X {130 USD}
  Assets:Bank      -130.00 USD

2024-04-01 * "Broker" "Sell"
  Assets:Stock     -1 X {100 USD} @ 150 USD
  Assets:Bank       150.00 USD
  Income:Salary     -50.00 USD
"#;

/// Two buys and a sale out of an AVERAGE pool (#2590's presentation).
const AVERAGE: &str = r#"
2024-01-01 open Assets:Broker "AVERAGE"
2024-01-01 open Assets:Cash USD
2024-01-01 open Income:Gains USD
2024-01-03 * "buy"
  Assets:Broker   10 X {100.00 USD}
  Assets:Cash  -1000.00 USD
2024-01-04 * "buy"
  Assets:Broker   10 X {200.00 USD}
  Assets:Cash  -2000.00 USD
2024-01-20 * "sell"
  Assets:Broker   -5 X {}
  Assets:Cash    900.00 USD
  Income:Gains   -150.00 USD
"#;

fn cell(value: &Value) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Date(d) => d.to_string(),
        Value::Amount(a) => a.to_string(),
        Value::Position(p) => p.to_string(),
        Value::Inventory(inv) => inv.to_string(),
        Value::Null => String::new(),
        other => format!("{other:?}"),
    }
}

fn run(source: &str, query: &str) -> Result<Vec<Vec<String>>, String> {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", source);
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    let ledger = process(raw, &LoadOptions::default()).expect("processes");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    executor.set_account_types(ledger.options.to_account_types());
    executor.set_booking_method(ledger.booking_method);
    executor.set_summary_accounts(SummaryAccounts::from_options(&ledger.options));
    let result = executor
        .execute(&parse(query).expect("parses"))
        .map_err(|e| e.to_string())?;
    Ok(result
        .rows
        .iter()
        .map(|row| row.iter().map(cell).collect())
        .collect())
}

fn rows(source: &str, query: &str) -> Vec<Vec<String>> {
    run(source, query).unwrap_or_else(|e| panic!("{query}: {e}"))
}

fn table(expected: &[&[&str]]) -> Vec<Vec<String>> {
    expected
        .iter()
        .map(|row| row.iter().map(ToString::to_string).collect())
        .collect()
}

#[test]
fn an_entry_column_in_where_filters_the_postings() {
    assert_eq!(
        rows(LEDGER, "BALANCES WHERE narration ~ 'salary'"),
        table(&[
            &["Assets:Bank", "2500.00 USD"],
            &["Income:Salary", "-2500.00 USD"],
        ])
    );
    assert_eq!(
        rows(LEDGER, "BALANCES WHERE 'Employer' = payee"),
        table(&[
            &["Assets:Bank", "2500.00 USD"],
            &["Income:Salary", "-2500.00 USD"],
        ])
    );
    assert_eq!(rows(LEDGER, "BALANCES WHERE year = 2025"), table(&[]));
}

/// A sale in the selected year of a lot bought before it: the selected
/// postings are summed, as bean-query sums them, and booking still reads the
/// sale against the lot it sold from. Replaying only the selected
/// transactions failed with "No matching lot", on `FROM` as on `WHERE`.
#[test]
fn a_year_with_a_sale_of_an_earlier_lot_sums_its_postings() {
    let expected = table(&[
        &["Assets:Bank", "1485.00 USD"],
        &[
            "Assets:Stock",
            "-1 X { 100 USD, 2023-07-01}, 1 X { 130 USD, 2024-03-01}",
        ],
        &["Income:Salary", "-1550.00 USD"],
        &["Expenses:Food", "35.00 USD"],
    ]);
    assert_eq!(rows(LEDGER, "BALANCES WHERE year = 2024"), expected);
    assert_eq!(rows(LEDGER, "BALANCES FROM year = 2024"), expected);
}

#[test]
fn a_posting_column_in_where_sums_the_matching_postings() {
    assert_eq!(
        rows(LEDGER, "BALANCES WHERE number > 0"),
        table(&[
            &["Assets:Bank", "2650.00 USD"],
            &[
                "Assets:Stock",
                "2 X { 100 USD, 2023-07-01}, 1 X { 130 USD, 2024-03-01}"
            ],
            &["Expenses:Food", "55.00 USD"],
        ])
    );
    assert_eq!(
        rows(LEDGER, "BALANCES AT units WHERE number > 0"),
        table(&[
            &["Assets:Bank", "2650.00 USD"],
            &["Assets:Stock", "3 X"],
            &["Expenses:Food", "55.00 USD"],
        ])
    );
    // An account column selects every posting of the account: its total.
    assert_eq!(
        rows(LEDGER, "BALANCES WHERE account ~ 'Bank'"),
        table(&[&["Assets:Bank", "2265.00 USD"]])
    );
}

#[test]
fn where_is_joined_to_the_from_filter() {
    assert_eq!(
        rows(LEDGER, "BALANCES FROM year = 2024 WHERE number < 0"),
        rows(LEDGER, "BALANCES WHERE year = 2024 AND number < 0"),
    );
    assert_eq!(
        rows(LEDGER, "BALANCES FROM year = 2024 WHERE number < 0"),
        table(&[
            &["Assets:Bank", "-165.00 USD"],
            &["Assets:Stock", "-1 X { 100 USD, 2023-07-01}"],
            &["Income:Salary", "-1550.00 USD"],
        ])
    );
    assert_eq!(
        rows(
            LEDGER,
            "BALANCES FROM has_account('Stock') WHERE number > 0"
        ),
        table(&[
            &["Assets:Bank", "150.00 USD"],
            &[
                "Assets:Stock",
                "2 X { 100 USD, 2023-07-01}, 1 X { 130 USD, 2024-03-01}"
            ],
        ])
    );
    // The bare-word pattern of a whole-filter `has_account` stays a pattern
    // once a WHERE is joined to it.
    assert_eq!(
        rows(LEDGER, "BALANCES FROM has_account(Stock) WHERE number > 0"),
        rows(
            LEDGER,
            "BALANCES FROM has_account('Stock') WHERE number > 0"
        ),
    );
    // After OPEN ON has summarized the earlier entries.
    assert_eq!(
        rows(
            LEDGER,
            "BALANCES FROM OPEN ON 2024-01-01 WHERE account ~ 'Bank|Stock'"
        ),
        table(&[
            &["Assets:Bank", "2265.00 USD"],
            &[
                "Assets:Stock",
                "1 X { 100 USD, 2023-07-01}, 1 X { 130 USD, 2024-03-01}"
            ],
        ])
    );
}

/// `BALANCES WHERE x` is `BALANCES FROM x`, and both are `sum(position)`
/// grouped by account.
#[test]
fn balances_where_equals_from_and_sum_position() {
    for (ledger, filter) in [
        (LEDGER, "year = 2024"),
        (LEDGER, "number < 0"),
        (LEDGER, "narration ~ 'buy|sell'"),
        (LEDGER, "account ~ 'Stock' OR payee = 'Shop'"),
        (AVERAGE, "number > 0"),
        (AVERAGE, "date < 2024-01-10"),
        (AVERAGE, "account ~ 'Broker'"),
        // A sale without the buys it sold from.
        (AVERAGE, "date > 2024-01-03"),
        (AVERAGE, "number < 0"),
        (AVERAGE, "year = 2024 AND narration ~ 'sell'"),
    ] {
        let balances = rows(ledger, &format!("BALANCES WHERE {filter}"));
        assert_eq!(
            balances,
            rows(ledger, &format!("BALANCES FROM {filter}")),
            "{filter}"
        );
        let sum = rows(
            ledger,
            &format!("SELECT account, sum(position) WHERE {filter} GROUP BY account"),
        );
        let mut sorted = balances.clone();
        sorted.sort();
        let mut sum_sorted = sum;
        sum_sorted.sort();
        assert_eq!(sorted, sum_sorted, "{filter}");
    }
}

/// An AVERAGE account on a filtered subset is shown as its pool (#2590):
/// the two buys alone are one 20 X pool at 150.
#[test]
fn an_average_account_on_a_filtered_subset_is_its_pool() {
    assert_eq!(
        rows(AVERAGE, "BALANCES WHERE number > 0"),
        table(&[
            &["Assets:Broker", "20 X { 150.00 USD}"],
            &["Assets:Cash", "900.00 USD"],
        ])
    );
    assert_eq!(
        rows(AVERAGE, "BALANCES WHERE date < 2024-01-10"),
        table(&[
            &["Assets:Broker", "20 X { 150.00 USD}"],
            &["Assets:Cash", "-3000.00 USD"],
        ])
    );
    // The whole account: booking's pool after the sale.
    assert_eq!(
        rows(AVERAGE, "BALANCES WHERE account ~ 'Broker'"),
        table(&[&["Assets:Broker", "15 X { 150.00 USD}"]])
    );
}

/// `balance` in BALANCES' WHERE used to be the account's total; filtering
/// postings, it is not, so it is refused rather than silently changed.
#[test]
fn balance_in_where_is_refused() {
    for query in [
        "BALANCES WHERE NOT empty(balance)",
        "BALANCES WHERE account_balance IS NULL",
    ] {
        let err = run(LEDGER, query).expect_err(query);
        assert!(err.contains("HAVING"), "{query}: {err}");
    }
}

const MERGE: &str = r#"
2020-01-01 open Assets:Broker AAPL "STRICT"
2020-01-01 open Assets:Cash

2020-01-01 * "lot a"
  Assets:Broker  10 AAPL {100.00 USD}
  Assets:Cash
2020-01-02 * "lot b"
  Assets:Broker  10 AAPL {120.00 USD}
  Assets:Cash
2020-01-03 * "buy, then merge-sell"
  Assets:Broker   5 AAPL {130.00 USD}
  Assets:Broker  -4 AAPL {*}
  Assets:Cash
"#;

/// A filtered `BALANCES` replays the WHOLE window as booking recorded it,
/// and sums only what the filter selects (#2630, #2730).
///
/// The `{*}` sale books from the pool the two lots before it make (20 @
/// 110); its own buy joins the pool only after. So the summed sale must read
/// 4 out of the 110 pool, exactly as `apply` realizes the booked ledger.
/// Every cheaper answer is a regression the filter could bring back:
/// replaying only the selected transaction sells from nothing ("No matching
/// lot", #2630); asking the booked posting again instead of reading its
/// recorded decision is the #2380 disagreement; and dropping the earlier
/// transactions from the replay would sell out of the buy's 5 @ 130. The
/// whole-ledger run is the same replay's cross-check: 16 left in the 110
/// pool beside the 130 buy, the bean-query holdings the report surface also
/// produces (#2380's parity case).
#[test]
fn a_filtered_balances_replays_the_window_as_booking_recorded_it() {
    let selected = table(&[
        &[
            "Assets:Broker",
            "-4 AAPL { 110.00 USD, 2020-01-03}, 5 AAPL { 130.00 USD, 2020-01-03}",
        ],
        &["Assets:Cash", "-210.00 USD"],
    ]);
    assert_eq!(
        rows(MERGE, "BALANCES WHERE narration = 'buy, then merge-sell'"),
        selected
    );
    assert_eq!(
        rows(MERGE, "BALANCES FROM narration = 'buy, then merge-sell'"),
        selected
    );
    assert_eq!(
        rows(MERGE, "BALANCES"),
        table(&[
            &[
                "Assets:Broker",
                "16 AAPL { 110.00 USD}, 5 AAPL { 130.00 USD, 2020-01-03}",
            ],
            &["Assets:Cash", "-2410.00 USD"],
        ])
    );
}
