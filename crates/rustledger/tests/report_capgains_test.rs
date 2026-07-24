//! `rledger report capgains` — end-to-end coverage of the realized
//! capital-gains / tax-lot report: the per-lot disposal rows, short vs long
//! term classification, exact `@@` (total-price) proceeds, the `--year` /
//! `--account` / `--long-term-days` filters, and the strict-booking refusal.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// FIFO ledger with a long-term disposal (8 units held 2020→2024) and a mixed
/// `@@` disposal that crosses a long-term and a short-term lot.
///
/// Hand-computed expectations:
/// - `2024-03-01` sell 8 @ 150: FIFO all from lot 1 (@100). basis 800, proceeds
///   1200, gain 400. Held > 1 year → LONG.
/// - `2024-04-01` sell 4 @@ 700 (total): FIFO 2 from lot 1 (@100, LONG) + 2 from
///   lot 2 (@120, SHORT). The 700 splits pro-rata 350 / 350. lot 1 gain
///   350 − 200 = 150 (LONG); lot 2 gain 350 − 240 = 110 (SHORT).
/// - Totals: long 550, short 110, net 660.
const LEDGER: &str = r#"option "booking_method" "FIFO"

2020-01-01 open Assets:Broker:Stock
2020-01-01 open Assets:Bank
2020-01-01 open Income:Gains

2020-01-01 * "Buy lot 1"
  Assets:Broker:Stock  10 AAPL {100 USD}
  Assets:Bank       -1000 USD

2023-06-01 * "Buy lot 2"
  Assets:Broker:Stock   5 AAPL {120 USD}
  Assets:Bank        -600 USD

2024-03-01 * "Sell 8 @ 150"
  Assets:Broker:Stock  -8 AAPL {} @ 150 USD
  Assets:Bank        1200 USD
  Income:Gains

2024-04-01 * "Sell 4 @@ 700"
  Assets:Broker:Stock  -4 AAPL {} @@ 700 USD
  Assets:Bank         700 USD
  Income:Gains
"#;

/// A STRICT-booked ledger (the default) where a bare-`{}` sale spans two
/// different-cost lots — an *ambiguous* reduction. The report must NOT silently
/// FIFO-match it (which would fabricate a gain `rledger check` rejects); it books
/// with the ledger's own method and produces no rows.
const LEDGER_AMBIGUOUS: &str = r#"2020-01-01 open Assets:Broker:Stock
2020-01-01 open Assets:Bank

2020-01-01 * "Buy lot 1"
  Assets:Broker:Stock  10 AAPL {100 USD}
  Assets:Bank       -1000 USD

2023-06-01 * "Buy lot 2"
  Assets:Broker:Stock   5 AAPL {120 USD}
  Assets:Bank        -600 USD

2024-03-01 * "Sell 8 — ambiguous under strict"
  Assets:Broker:Stock  -8 AAPL {} @ 150 USD
  Assets:Bank        1200 USD
"#;

fn write_fixture(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-capgains-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    f
}

fn run(binary: &PathBuf, args: &[&str]) -> String {
    let out = Command::new(binary)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("run rledger {args:?}: {e}"));
    assert!(
        out.status.success(),
        "rledger {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn csv_has_one_row_per_lot_with_exact_figures() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = run(&bin, &["report", path, "capgains", "--format", "csv"]);
    let rows: Vec<&str> = out.lines().collect();
    assert_eq!(rows.len(), 4, "header + 3 disposal rows: {out}");
    assert_eq!(
        rows[0],
        "sold,account,commodity,units,acquired,held_days,term,currency,proceeds,cost_basis,gain"
    );
    // 8 @ 150 from lot 1, long-term.
    assert_eq!(
        rows[1],
        "2024-03-01,Assets:Broker:Stock,AAPL,8,2020-01-01,1521,long,USD,1200,800,400"
    );
    // @@ 700 split: lot 1 long, lot 2 short — proceeds 350 each, summing to 700.
    assert_eq!(
        rows[2],
        "2024-04-01,Assets:Broker:Stock,AAPL,2,2020-01-01,1552,long,USD,350,200,150"
    );
    assert_eq!(
        rows[3],
        "2024-04-01,Assets:Broker:Stock,AAPL,2,2023-06-01,305,short,USD,350,240,110"
    );
}

#[test]
fn json_summaries_split_short_and_long_term() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = run(&bin, &["report", path, "capgains", "--format", "json"]);
    // Long-term total 550, short-term total 110.
    assert!(
        out.contains(r#""long_term": [{"currency": "USD", "disposals": 2, "proceeds": "1550", "cost_basis": "1000", "gain": "550"}]"#),
        "long-term summary: {out}"
    );
    assert!(
        out.contains(r#""short_term": [{"currency": "USD", "disposals": 1, "proceeds": "350", "cost_basis": "240", "gain": "110"}]"#),
        "short-term summary: {out}"
    );
}

#[test]
fn text_report_shows_net_realized_gain() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = run(&bin, &["report", path, "capgains", "--no-pager"]);
    assert!(out.contains("net realized gain          660 USD"), "{out}");
    assert!(out.contains("Long-term     2 disposals"), "{out}");
    assert!(out.contains("Short-term    1 disposals"), "{out}");
}

#[test]
fn long_term_days_override_reclassifies_everything_short() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    // A threshold larger than any holding here → all short-term.
    let out = run(
        &bin,
        &[
            "report",
            path,
            "capgains",
            "--long-term-days",
            "9000",
            "--format",
            "csv",
        ],
    );
    assert!(out.lines().skip(1).all(|l| l.contains(",short,")), "{out}");
    assert!(!out.contains(",long,"), "{out}");
}

#[test]
fn year_filter_keeps_only_that_years_disposals() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    // Both sales are in 2024; a 2023 filter (only a buy) yields no data rows.
    let y2024 = run(
        &bin,
        &[
            "report", path, "capgains", "--year", "2024", "--format", "csv",
        ],
    );
    assert_eq!(
        y2024.lines().count(),
        4,
        "2024 has all three disposals: {y2024}"
    );
    let y2023 = run(
        &bin,
        &[
            "report", path, "capgains", "--year", "2023", "--format", "csv",
        ],
    );
    assert_eq!(y2023.lines().count(), 1, "2023 header only: {y2023}");
}

#[test]
fn ambiguous_strict_reduction_yields_no_rows() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_AMBIGUOUS);
    let path = f.path().to_str().unwrap();
    // The report books with the ledger's STRICT method: the ambiguous bare-`{}`
    // sale does not book, so no disposal is fabricated.
    let out = run(&bin, &["report", path, "capgains", "--format", "csv"]);
    assert_eq!(
        out.lines().count(),
        1,
        "header only, no fabricated rows: {out}"
    );
}
