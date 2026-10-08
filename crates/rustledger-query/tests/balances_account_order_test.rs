//! `BALANCES` orders rows by `account_sortkey` (#2409): account type first
//! (Assets, Liabilities, Equity, Income, Expenses, honoring `name_*` renames),
//! then name. bean-query's `BALANCES` is `... GROUP BY account ORDER BY
//! account_sortkey(account)`. Expected orders are bean-query's (beanquery
//! 0.2.0, beancount 3.2.3) on the same ledger.

use std::path::Path;

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
option "name_income" "Revenue"
2024-01-01 open Assets:Bank
2024-01-01 open Expenses:Food
2024-01-01 open Expenses:Rent
2024-01-01 open Revenue:Salary
2024-01-01 open Liabilities:Card
2024-01-01 open Equity:Opening

2024-01-02 * "x"
  Assets:Bank  100 USD
  Revenue:Salary  -100 USD
2024-01-03 * "x"
  Expenses:Food  10 USD
  Expenses:Rent  10 USD
  Liabilities:Card  -20 USD
2024-01-04 * "x"
  Assets:Bank  1 USD
  Equity:Opening  -1 USD
"#;

fn accounts(query: &str) -> Vec<String> {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", LEDGER);
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    let ledger = process(raw, &LoadOptions::default()).expect("processes");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    executor.set_account_types(ledger.options.to_account_types());
    executor
        .execute(&parse(query).expect("parses"))
        .unwrap_or_else(|e| panic!("{query}: {e}"))
        .rows
        .iter()
        .map(|row| match &row[0] {
            Value::String(s) => s.clone(),
            other => panic!("{query}: unexpected {other:?}"),
        })
        .collect()
}

const EXPECTED: [&str; 6] = [
    "Assets:Bank",
    "Liabilities:Card",
    "Equity:Opening",
    "Revenue:Salary",
    "Expenses:Food",
    "Expenses:Rent",
];

#[test]
fn balances_rows_follow_account_sortkey() {
    assert_eq!(accounts("BALANCES"), EXPECTED.to_vec());
}

#[test]
fn balances_order_holds_with_from_and_where() {
    assert_eq!(
        accounts("BALANCES FROM year = 2024 WHERE account ~ 'e'"),
        EXPECTED.to_vec()
    );
}
