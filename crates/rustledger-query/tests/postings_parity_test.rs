//! Parity harness for the posting-source paths (BR8 step 3 groundwork).
//!
//! The same "iterate postings, resolve cost -> Position, accumulate running and
//! per-account Inventory, project columns" concept is implemented twice: the
//! default `SELECT` path (`collect_postings` + per-column evaluation) and the
//! `#postings` table (`build_postings_table`, a parallel ~237-line loop with its
//! own accumulators). They are supposed to agree column-for-column.
//!
//! This test pins that equivalence *before* the two are unified onto one
//! `PostingRow` stream, so the unification can be proven behavior-preserving and
//! any future drift on a shared column (the structural root of the balance bug
//! #2 the audit flagged) is caught here.

use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, CostNumber, CostSpec, Directive, NaiveDate, Open, Posting, Transaction,
};
use rustledger_query::{Executor, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// A multi-account, multi-posting fixture so the running `balance` and
/// per-account `account_balance` columns accumulate non-trivially across rows.
fn fixture() -> Vec<Directive> {
    let txn = |d: u32,
               narr: &str,
               a: &str,
               an: rust_decimal::Decimal,
               b: &str,
               bn: rust_decimal::Decimal| {
        Directive::Transaction(
            Transaction::new(date(2024, 1, d), narr)
                .with_flag('*')
                .with_synthesized_posting(Posting::new(a, Amount::new(an, "USD")))
                .with_synthesized_posting(Posting::new(b, Amount::new(bn, "USD"))),
        )
    };
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        txn(
            10,
            "coffee",
            "Expenses:Food",
            dec!(5),
            "Assets:Cash",
            dec!(-5),
        ),
        txn(
            11,
            "groceries",
            "Expenses:Food",
            dec!(50),
            "Assets:Bank",
            dec!(-50),
        ),
        txn(
            12,
            "transfer",
            "Assets:Cash",
            dec!(100),
            "Assets:Bank",
            dec!(-100),
        ),
        txn(
            13,
            "lunch",
            "Expenses:Food",
            dec!(12),
            "Assets:Cash",
            dec!(-12),
        ),
        // A cost-bearing buy, so `position`, `cost_number`/`cost_currency`, and
        // the weight (`units * cost`) columns are exercised too.
        Directive::Transaction(
            Transaction::new(date(2024, 1, 14), "buy stock")
                .with_flag('*')
                .with_synthesized_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec {
                            number: Some(CostNumber::PerUnit { value: dec!(150) }),
                            currency: Some("USD".into()),
                            date: None,
                            label: None,
                            merge: false,
                        },
                    ),
                )
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ]
}

/// The columns where the default path and `#postings` could diverge: the
/// per-posting projections plus the two accumulated balances.
const COLUMNS: &str = "account, number, currency, position, weight, balance, account_balance, cost_number, cost_currency";

#[test]
fn default_select_matches_postings_table() {
    let dirs = fixture();
    let mut executor = Executor::new(&dirs);

    let direct = executor
        .execute(&parse(&format!("SELECT {COLUMNS}")).unwrap())
        .unwrap();
    let table = executor
        .execute(&parse(&format!("SELECT {COLUMNS} FROM #postings")).unwrap())
        .unwrap();

    assert_eq!(
        direct.columns, table.columns,
        "column headers diverge between default SELECT and #postings"
    );
    assert_eq!(
        direct.rows.len(),
        table.rows.len(),
        "row count diverges: default={} #postings={}",
        direct.rows.len(),
        table.rows.len()
    );
    assert_eq!(
        direct.rows, table.rows,
        "default SELECT and #postings produce different column VALUES — the two \
         posting-source implementations have drifted"
    );
}

/// Every `#postings` column the default `SELECT` path also computes. After the
/// `type`/`cost_date` reconciliation (both were the default path being wrong vs
/// the bean-query oracle), the two paths agree on ALL of these.
const ALL_COLUMNS: &str = "type, id, date, year, month, day, flag, payee, narration, \
     description, tags, links, posting_flag, account, other_accounts, number, currency, \
     cost_number, cost_currency, cost_date, cost_label, position, price, weight, balance, \
     account_balance";

fn columns_that_diverge(dirs: &[Directive]) -> Vec<String> {
    let mut executor = Executor::new(dirs);
    ALL_COLUMNS
        .split(',')
        .map(str::trim)
        .filter(|col| {
            let direct = executor
                .execute(&parse(&format!("SELECT {col}")).unwrap())
                .unwrap();
            let table = executor
                .execute(&parse(&format!("SELECT {col} FROM #postings")).unwrap())
                .unwrap();
            direct.rows != table.rows
        })
        .map(str::to_string)
        .collect()
}

/// No `#postings` column may diverge from the default `SELECT` path — proven
/// per-column so a failure names exactly which column drifted. This is the
/// regression net for the upcoming single-posting-source iterator unification.
#[test]
fn no_columns_diverge_from_default_select() {
    let diverge = columns_that_diverge(&fixture());
    assert!(
        diverge.is_empty(),
        "columns where default SELECT and #postings diverge: {diverge:?}"
    );
}

/// Full row-for-row parity across the entire projectable column set.
#[test]
fn all_columns_match_row_for_row() {
    let dirs = fixture();
    let mut executor = Executor::new(&dirs);
    let direct = executor
        .execute(&parse(&format!("SELECT {ALL_COLUMNS}")).unwrap())
        .unwrap();
    let table = executor
        .execute(&parse(&format!("SELECT {ALL_COLUMNS} FROM #postings")).unwrap())
        .unwrap();
    assert_eq!(direct.columns, table.columns, "headers diverge");
    assert_eq!(
        direct.rows, table.rows,
        "default SELECT and #postings diverge on a column value"
    );
}
