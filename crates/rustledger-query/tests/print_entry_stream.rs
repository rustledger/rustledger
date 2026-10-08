//! BQL `PRINT` prints the entry stream the `FROM` clause gives (#2411), each
//! entry through the canonical formatter (#2426).
//!
//! It printed every directive of the ledger, whatever `OPEN ON` / `CLOSE` /
//! `CLEAR` said, through a formatter of its own that dropped costs, prices,
//! metadata and the booking method, and escaped nothing.
//!
//! Every expected text below is bean-query's (beanquery 0.2.0, beancount
//! 3.2.3) on the same ledger, byte for byte, except the column padding of the
//! `open`, `price` and `balance` lines: beancount's printer pads those to fixed
//! columns, and rledger prints them as `rledger format` writes them.

use std::path::Path;

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_query::executor::SummaryAccounts;
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
2024-01-01 open Assets:B USD,X "FIFO"
2024-01-01 open Assets:C USD
2024-01-01 open Assets:Old USD
2024-01-01 open Income:G USD
2024-01-01 open Expenses:Food USD
2024-01-01 commodity X
  name: "Ex"
2024-01-02 * "Broker" "buy \"quoted\"" #tag ^link
  key: "value"
  Assets:B  3 X {100 USD, "lot-a"}
    pmeta: 1
  Assets:C
2024-01-03 price X 110 USD
2024-01-03 price X 111 USD
2024-01-04 balance Assets:C  -300 USD
2024-01-05 note Assets:C "a note"
2024-01-06 close Assets:Old
2024-01-07 * "lunch"
  Expenses:Food  12.50 USD
  Assets:C
2024-01-08 balance Expenses:Food  12.50 USD
2024-02-01 * "sell"
  Assets:B  -1 X {} @ 120 USD
  Assets:C  120 USD
  Income:G
2024-02-03 price X 125 USD
2024-02-05 * "lunch2"
  Expenses:Food  7.25 USD
  Assets:C
2024-02-10 balance Expenses:Food  19.75 USD
"#;

/// `PRINT`.
const FULL: &str = r#"2024-01-01 open Assets:B USD,X "FIFO"
2024-01-01 open Assets:C USD
2024-01-01 open Assets:Old USD
2024-01-01 open Income:G USD
2024-01-01 open Expenses:Food USD

2024-01-01 commodity X
  name: "Ex"

2024-01-02 * "Broker" "buy \"quoted\"" #tag ^link
  key: "value"
  Assets:B     3 X {100 USD, 2024-01-02, "lot-a"}
    pmeta: 1
  Assets:C  -300 USD

2024-01-03 price X 110 USD
2024-01-03 price X 111 USD

2024-01-04 balance Assets:C -300 USD

2024-01-05 note Assets:C "a note"

2024-01-06 close Assets:Old

2024-01-07 * "lunch"
  Expenses:Food   12.50 USD
  Assets:C       -12.50 USD

2024-01-08 balance Expenses:Food 12.50 USD

2024-02-01 * "sell"
  Assets:B   -1 X {100 USD, 2024-01-02, "lot-a"} @ 120 USD
  Assets:C  120 USD
  Income:G  -20 USD

2024-02-03 price X 125 USD

2024-02-05 * "lunch2"
  Expenses:Food   7.25 USD
  Assets:C       -7.25 USD

2024-02-10 balance Expenses:Food 19.75 USD
"#;

/// `PRINT FROM OPEN ON 2024-02-01`.
const OPENED: &str = r#"2024-01-01 open Assets:B USD,X "FIFO"
2024-01-01 open Assets:C USD
2024-01-01 open Income:G USD
2024-01-01 open Expenses:Food USD

2024-01-03 price X 111 USD

2024-01-31 S "Opening balance for 'Assets:B' (Summarization)"
  Assets:B                    3 X {100 USD, 2024-01-02, "lot-a"}
  Equity:Opening-Balances  -300 USD

2024-01-31 S "Opening balance for 'Assets:C' (Summarization)"
  Assets:C                 -312.50 USD
  Equity:Opening-Balances   312.50 USD

2024-01-31 S "Opening balance for 'Equity:Earnings:Previous' (Summarization)"
  Equity:Earnings:Previous   12.50 USD
  Equity:Opening-Balances   -12.50 USD

2024-02-01 * "sell"
  Assets:B   -1 X {100 USD, 2024-01-02, "lot-a"} @ 120 USD
  Assets:C  120 USD
  Income:G  -20 USD

2024-02-03 price X 125 USD

2024-02-05 * "lunch2"
  Expenses:Food   7.25 USD
  Assets:C       -7.25 USD
"#;

/// `PRINT FROM CLOSE ON 2024-02-02 CLEAR`.
const CLOSED_CLEARED: &str = r#"2024-01-01 open Assets:B USD,X "FIFO"
2024-01-01 open Assets:C USD
2024-01-01 open Assets:Old USD
2024-01-01 open Income:G USD
2024-01-01 open Expenses:Food USD

2024-01-01 commodity X
  name: "Ex"

2024-01-02 * "Broker" "buy \"quoted\"" #tag ^link
  key: "value"
  Assets:B     3 X {100 USD, 2024-01-02, "lot-a"}
    pmeta: 1
  Assets:C  -300 USD

2024-01-03 price X 110 USD
2024-01-03 price X 111 USD

2024-01-04 balance Assets:C -300 USD

2024-01-05 note Assets:C "a note"

2024-01-06 close Assets:Old

2024-01-07 * "lunch"
  Expenses:Food   12.50 USD
  Assets:C       -12.50 USD

2024-01-08 balance Expenses:Food 12.50 USD

2024-02-01 * "sell"
  Assets:B   -1 X {100 USD, 2024-01-02, "lot-a"} @ 120 USD
  Assets:C  120 USD
  Income:G  -20 USD

2024-02-01 T "Transfer balance for 'Expenses:Food' (Transfer balance)"
  Expenses:Food            -12.50 USD
  Equity:Earnings:Current   12.50 USD

2024-02-01 T "Transfer balance for 'Income:G' (Transfer balance)"
  Income:G                  20 USD
  Equity:Earnings:Current  -20 USD
"#;

/// `PRINT FROM has_account('Assets:C')`.
const HAS_ACCOUNT: &str = r#"2024-01-01 open Assets:C USD

2024-01-02 * "Broker" "buy \"quoted\"" #tag ^link
  key: "value"
  Assets:B     3 X {100 USD, 2024-01-02, "lot-a"}
    pmeta: 1
  Assets:C  -300 USD

2024-01-04 balance Assets:C -300 USD

2024-01-05 note Assets:C "a note"

2024-01-07 * "lunch"
  Expenses:Food   12.50 USD
  Assets:C       -12.50 USD

2024-02-01 * "sell"
  Assets:B   -1 X {100 USD, 2024-01-02, "lot-a"} @ 120 USD
  Assets:C  120 USD
  Income:G  -20 USD

2024-02-05 * "lunch2"
  Expenses:Food   7.25 USD
  Assets:C       -7.25 USD
"#;

fn load(source: &str) -> rustledger_loader::Ledger {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", source);
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    process(raw, &LoadOptions::default()).expect("processes")
}

/// The PRINT rows concatenated, as the CLI writes them.
fn print(query: &str) -> String {
    let ledger = load(LEDGER);
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    executor.set_account_types(ledger.options.to_account_types());
    executor.set_booking_method(ledger.booking_method);
    executor.set_summary_accounts(SummaryAccounts::from_options(&ledger.options));
    let result = executor
        .execute(&parse(query).expect("parses"))
        .unwrap_or_else(|e| panic!("{query}: {e}"));
    assert_eq!(result.columns, ["directive"]);
    result
        .rows
        .iter()
        .map(|row| match row.as_slice() {
            [Value::String(text)] => text.as_str(),
            other => panic!("{query}: {other:?}"),
        })
        .collect()
}

/// Costs with their booked date and label, the price annotation, transaction,
/// posting and commodity metadata, the booking method, an escaped narration,
/// and every directive type, separated as beancount's printer separates them.
#[test]
fn print_renders_entries_through_the_canonical_formatter() {
    assert_eq!(print("PRINT"), FULL);
}

/// `OPEN ON`: the `open`s still active (not `Assets:Old`), the last price of
/// each pair, the summaries, then the entries from the date on, without the
/// `balance` on `Expenses:Food`, which the summary cleared.
#[test]
fn print_from_open_on_prints_the_summarized_stream() {
    assert_eq!(print("PRINT FROM OPEN ON 2024-02-01"), OPENED);
}

/// `CLOSE ON` truncates; `CLEAR` appends the transfers.
#[test]
fn print_from_close_on_and_clear_prints_the_truncated_stream() {
    assert_eq!(
        print("PRINT FROM CLOSE ON 2024-02-02 CLEAR"),
        CLOSED_CLEARED
    );
}

/// The filter reads every entry as beanquery's `entries` table does:
/// `has_account()` keeps the `open`, `balance` and `note` that name the
/// account, and `narration` is NULL on them.
#[test]
fn print_filters_every_entry_type() {
    assert_eq!(print("PRINT FROM has_account('Assets:C')"), HAS_ACCOUNT);
    let lunches = print("PRINT FROM narration ~ 'lunch'");
    assert!(lunches.starts_with("\n2024-01-07 * \"lunch\""), "{lunches}");
    assert_eq!(lunches.matches(" * ").count(), 2, "{lunches}");
    assert_eq!(
        print("PRINT FROM type = 'price' AND date < 2024-02-01"),
        "2024-01-03 price X 110 USD\n2024-01-03 price X 111 USD\n"
    );
    // A filter and OPEN ON together: the filter runs on the summarized stream.
    assert!(
        print("PRINT FROM narration ~ 'Summarization' OPEN ON 2024-02-01")
            .contains("Opening balance for 'Assets:B'")
    );
}

/// The printed ledger loads back to the same ledger.
#[test]
fn printed_text_loads_back_clean() {
    let printed = load(&print("PRINT"));
    assert!(printed.errors.is_empty(), "{:?}", printed.errors);
    assert_eq!(printed.directives.len(), load(LEDGER).directives.len());
}

/// `has_account()` on `#entries` is the same predicate PRINT filters with:
/// beanquery's `regex ~? any(accounts)`. It was an unknown function there.
#[test]
fn has_account_reads_the_accounts_of_an_entries_row() {
    let ledger = load(LEDGER);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    let result = executor
        .execute(&parse("SELECT type FROM #entries WHERE has_account('Assets:C')").expect("parses"))
        .expect("runs");
    let types: Vec<String> = result
        .rows
        .iter()
        .map(|row| match &row[0] {
            Value::String(s) => s.clone(),
            other => panic!("{other:?}"),
        })
        .collect();
    assert_eq!(
        types,
        [
            "open",
            "transaction",
            "balance",
            "note",
            "transaction",
            "transaction",
            "transaction"
        ]
    );
}

/// Each printed entry is already in `rledger format`'s canonical form: PRINT
/// renders through `canonicalize_directives`, the one function that turns a
/// typed directive into that form. Rendering with `rustledger_core::format`
/// directly printed its intermediate text instead (`price X  110 USD`, which
/// `rledger format` rewrites to `price X 110 USD`).
///
/// Entry by entry, because `rledger format` aligns the postings of a whole
/// file and PRINT, like bean-query, aligns each entry on its own.
#[test]
fn every_printed_entry_is_in_rledger_formats_canonical_form() {
    let ledger = load(LEDGER);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    executor.set_account_types(ledger.options.to_account_types());
    executor.set_booking_method(ledger.booking_method);
    executor.set_summary_accounts(SummaryAccounts::from_options(&ledger.options));
    for query in [
        "PRINT",
        "PRINT FROM OPEN ON 2024-02-01",
        "PRINT FROM CLOSE ON 2024-02-02 CLEAR",
    ] {
        let result = executor
            .execute(&parse(query).expect("parses"))
            .expect("runs");
        assert!(result.rows.len() > 5, "{query}: {} rows", result.rows.len());
        for row in &result.rows {
            let [Value::String(text)] = row.as_slice() else {
                panic!("{query}: {row:?}");
            };
            let entry = text.trim_start_matches('\n');
            assert_eq!(
                rustledger_parser::format::format_source(entry),
                entry,
                "{query}: not in canonical form",
            );
        }
    }
}
