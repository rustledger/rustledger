//! Plugin-inserted entries with no source location sort before same-date,
//! same-type entries from the file, as beancount sorts them (#2553).
//!
//! Beancount's `entry_sortkey` is `(date, type order, lineno)`, and an entry a
//! plugin inserts carries `lineno` 0, so it comes first. rledger keyed on the
//! sentinel file id `u16::MAX` and put such entries last.

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

fn opens_in_order(source: &str) -> Vec<String> {
    let mut f = tempfile::Builder::new()
        .prefix("synth-order-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");
    ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Open(o) => Some(o.account.to_string()),
            _ => None,
        })
        .collect()
}

/// beancount 3.2.3 `PRINT` of this ledger:
///
/// ```text
/// 2024-01-01 open Expenses:Food
/// 2024-01-01 open Assets:Cash
/// ```
#[test]
fn auto_accounts_open_sorts_before_same_date_written_open() {
    let opens = opens_in_order(
        "plugin \"beancount.plugins.auto_accounts\"\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 * \"x\"\n  Assets:Cash  -1 USD\n  Expenses:Food\n",
    );
    assert_eq!(opens, ["Expenses:Food", "Assets:Cash"]);
}

/// Entries the file wrote keep their file order among themselves; only the
/// inserted one moves ahead of them.
#[test]
fn written_entries_keep_file_order_around_an_inserted_one() {
    let opens = opens_in_order(
        "plugin \"beancount.plugins.auto_accounts\"\n\
         2024-01-01 open Assets:Zeta\n\
         2024-01-01 open Assets:Alpha\n\
         2024-01-01 * \"x\"\n  Assets:Zeta  -1 USD\n  Expenses:Food\n",
    );
    assert_eq!(opens, ["Expenses:Food", "Assets:Zeta", "Assets:Alpha"]);
}
