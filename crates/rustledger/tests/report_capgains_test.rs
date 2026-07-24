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

/// Closing a short: sold 5 @ 100 (received 500), covered 5 @ 80 (paid 400) → +100
/// gain, always short-term. The row's proceeds/basis are the short-open value and
/// the cover cost (the mirror of a long disposal).
const LEDGER_SHORT: &str = r#"option "booking_method" "FIFO"

2019-01-01 open Assets:Broker:Stock
2019-01-01 open Assets:Bank
2019-01-01 open Income:Gains

2020-01-01 * "open short"
  Assets:Broker:Stock  -5 AAPL {100 USD}
  Assets:Bank        500 USD

2022-06-01 * "cover"
  Assets:Broker:Stock   5 AAPL {} @ 80 USD
  Assets:Bank       -400 USD
  Income:Gains
"#;

/// AVERAGE booking merges lots and drops their acquisition dates, so the holding
/// period is unknown — the report must say `unknown`, not silently `short`. The
/// averaged basis (6 × 115 = 690) is still correct.
const LEDGER_AVERAGE: &str = r#"option "booking_method" "AVERAGE"

2019-01-01 open Assets:Broker:Stock
2019-01-01 open Assets:Bank
2019-01-01 open Income:Gains

2020-01-01 * "buy 10 @ 100"
  Assets:Broker:Stock  10 AAPL {100 USD}
  Assets:Bank       -1000 USD

2023-06-01 * "buy 10 @ 130"
  Assets:Broker:Stock  10 AAPL {130 USD}
  Assets:Bank       -1300 USD

2024-01-01 * "sell 6 @ 150"
  Assets:Broker:Stock  -6 AAPL {} @ 150 USD
  Assets:Bank        900 USD
  Income:Gains
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
    // Parse the whole payload — this also asserts the output is valid JSON.
    let v: serde_json::Value =
        serde_json::from_str(&out).unwrap_or_else(|e| panic!("invalid JSON ({e}): {out}"));

    // Three per-lot disposals.
    assert_eq!(v["disposals"].as_array().unwrap().len(), 3, "{out}");

    // Long-term summary: 2 disposals, proceeds 1550, gain 550 USD.
    let lt = &v["long_term"][0];
    assert_eq!(lt["currency"], "USD");
    assert_eq!(lt["disposals"], 2);
    assert_eq!(lt["proceeds"], "1550");
    assert_eq!(lt["cost_basis"], "1000");
    assert_eq!(lt["gain"], "550");

    // Short-term summary: 1 disposal, proceeds 350, gain 110 USD.
    let st = &v["short_term"][0];
    assert_eq!(st["currency"], "USD");
    assert_eq!(st["disposals"], 1);
    assert_eq!(st["proceeds"], "350");
    assert_eq!(st["gain"], "110");

    // Spot-check the first disposal row's fields.
    let d0 = &v["disposals"][0];
    assert_eq!(d0["commodity"], "AAPL");
    assert_eq!(d0["units"], "8");
    assert_eq!(d0["term"], "long");
    assert_eq!(d0["proceeds"], "1200");
    assert_eq!(d0["gain"], "400");
}

#[test]
fn text_report_shows_net_realized_gain() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = run(&bin, &["report", path, "capgains", "--no-pager"]);
    // Substring-based (robust to column-width tweaks): the net total and the
    // per-term disposal counts.
    assert!(out.contains("net realized gain"), "{out}");
    assert!(out.contains("660 USD"), "net total: {out}");
    assert!(
        out.contains("Long-term") && out.contains("2 disposals"),
        "{out}"
    );
    assert!(
        out.contains("Short-term") && out.contains("1 disposals"),
        "{out}"
    );
    // The row term abbreviations appear (LT for the long lots, ST for the short one).
    assert!(out.contains("    LT "), "long row abbr: {out}");
    assert!(out.contains("    ST "), "short row abbr: {out}");
}

#[test]
fn end_filter_is_inclusive_of_the_boundary_date() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    // `--end` on the first sale date INCLUDES that day's disposal.
    let incl = run(
        &bin,
        &[
            "report",
            path,
            "capgains",
            "--end",
            "2024-03-01",
            "--format",
            "csv",
        ],
    );
    assert!(
        incl.contains("2024-03-01,"),
        "boundary date included: {incl}"
    );
    assert!(
        !incl.contains("2024-04-01,"),
        "later disposal excluded: {incl}"
    );
    // One day before the first sale excludes everything.
    let before = run(
        &bin,
        &[
            "report",
            path,
            "capgains",
            "--end",
            "2024-02-29",
            "--format",
            "csv",
        ],
    );
    assert_eq!(before.lines().count(), 1, "header only: {before}");
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
fn short_sale_has_correct_sign_and_is_short_term() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_SHORT);
    let path = f.path().to_str().unwrap();
    let out = run(&bin, &["report", path, "capgains", "--format", "csv"]);
    let rows: Vec<&str> = out.lines().collect();
    assert_eq!(rows.len(), 2, "header + one disposal: {out}");
    // proceeds = short-open value 500, basis = cover cost 400, gain +100, short-term
    // (even though the short was open > 1 year).
    assert_eq!(
        rows[1],
        "2022-06-01,Assets:Broker:Stock,AAPL,5,2020-01-01,882,short,USD,500,400,100"
    );
}

#[test]
fn average_cost_disposal_has_unknown_term() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_AVERAGE);
    let path = f.path().to_str().unwrap();
    let out = run(&bin, &["report", path, "capgains", "--format", "csv"]);
    let rows: Vec<&str> = out.lines().collect();
    assert_eq!(rows.len(), 2, "header + one disposal: {out}");
    // Blank acquired/held_days, term=unknown, averaged basis 690 (6 × 115), gain 210.
    assert_eq!(
        rows[1],
        "2024-01-01,Assets:Broker:Stock,AAPL,6,,,unknown,USD,900,690,210"
    );
    // The text summary shows an Unknown-term bucket, not Short/Long, the row is
    // marked `??`, and the net total includes the unknown-term gain (210).
    let txt = run(&bin, &["report", path, "capgains", "--no-pager"]);
    assert!(txt.contains("Unknown-term"), "{txt}");
    assert!(!txt.contains("Short-term"), "{txt}");
    assert!(txt.contains("    ?? "), "unknown row abbr: {txt}");
    assert!(
        txt.contains("net realized gain") && txt.contains("210 USD"),
        "net includes the unknown-term gain: {txt}"
    );
}

#[test]
fn negative_long_term_days_is_rejected() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    // `=` form reaches the value; a bare `-1` is rejected by clap as a flag. Either
    // way a negative threshold must not be accepted (it would call everything long).
    let out = Command::new(&bin)
        .args(["report", path, "capgains", "--long-term-days=-1"])
        .output()
        .expect("run");
    assert!(!out.status.success(), "negative threshold must error");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("non-negative"),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
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
