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

/// Two closed round trips with DIFFERENT annualized rates, neither of which is
/// 10% — `xirr` seeds Newton at exactly 0.10, so a 10% fixture could be satisfied
/// by the seed at iteration 0 and would not prove the solver searched.
///
/// - A: 365 days, 1000 -> 1250 = 25%/yr.
/// - B: 730 days, 1000 -> 1440 = 1.44x over 2y = 20%/yr compounded.
///
/// Pooled over all four flows: 21.67%/yr (independently computed by bisection).
const LEDGER_IRR: &str = r#"option "booking_method" "FIFO"

2019-01-01 open Assets:Broker:Stock
2019-01-01 open Assets:Bank
2019-01-01 open Income:Gains

2020-01-01 * "buy A"
  Assets:Broker:Stock  10 AAA {100 USD}
  Assets:Bank       -1000 USD

2020-12-31 * "sell A"
  Assets:Broker:Stock  -10 AAA {} @ 125 USD
  Assets:Bank        1250 USD
  Income:Gains

2020-01-01 * "buy B"
  Assets:Broker:Stock  10 BBB {100 USD}
  Assets:Bank       -1000 USD

2021-12-31 * "sell B"
  Assets:Broker:Stock  -10 BBB {} @ 144 USD
  Assets:Bank        1440 USD
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
fn irr_annualizes_each_lot_and_pools_the_aggregate() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_IRR);
    let path = f.path().to_str().unwrap();

    // CSV: the rate is a 2-decimal PERCENT in an `irr_pct` column — the same unit
    // and name shape as `report returns`' money_weighted_return_pct.
    let csv = run(
        &bin,
        &["report", path, "capgains", "--irr", "--format", "csv"],
    );
    let rows: Vec<&str> = csv.lines().collect();
    assert_eq!(
        rows[0],
        "sold,account,commodity,units,acquired,held_days,term,currency,proceeds,cost_basis,gain,irr_pct"
    );
    // Assert the whole row, so the rate is pinned to its column and the two lots'
    // DIFFERENT rates cannot satisfy each other's assertion.
    assert_eq!(
        rows[1],
        "2020-12-31,Assets:Broker:Stock,AAA,10,2020-01-01,365,short,USD,1250,1000,250,25.00"
    );
    assert_eq!(
        rows[2],
        "2021-12-31,Assets:Broker:Stock,BBB,10,2020-01-01,730,long,USD,1440,1000,440,20.00"
    );

    // Text: per-row percent column plus pooled per-term and TOTAL rates.
    let txt = run(&bin, &["report", path, "capgains", "--irr", "--no-pager"]);
    assert!(txt.contains("25.00%"), "one-year lot: {txt}");
    assert!(txt.contains("20.00%"), "two-year lot: {txt}");
    assert!(
        txt.lines()
            .any(|l| l.starts_with("TOTAL") && l.contains("IRR 21.67%")),
        "pooled money-weighted TOTAL (not the 22.50% mean of 25 and 20): {txt}"
    );

    // JSON: numeric percent, plus the per-currency total block with coverage.
    let json = run(
        &bin,
        &["report", path, "capgains", "--irr", "--format", "json"],
    );
    let v: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert_eq!(v["disposals"][0]["irr_pct"], 25.00);
    assert_eq!(v["disposals"][1]["irr_pct"], 20.00);
    assert_eq!(v["total_irr_pct"][0]["currency"], "USD");
    assert_eq!(v["total_irr_pct"][0]["irr_pct"], 21.67);
    assert_eq!(v["total_irr_pct"][0]["irr_lots"], 2);
    assert_eq!(v["total_irr_pct"][0]["irr_lots_total"], 2);
}

#[test]
fn irr_is_absent_without_the_flag() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_IRR);
    let path = f.path().to_str().unwrap();
    // Default output schema is unchanged — no irr column/field anywhere.
    // Assert on the SCHEMA lines, not a substring of the whole output: a commodity
    // or payee containing "irr" must not be able to fail (or pass) these.
    let csv = run(&bin, &["report", path, "capgains", "--format", "csv"]);
    let header = csv.lines().next().expect("a header");
    assert!(
        !header.contains("irr"),
        "no irr column by default: {header}"
    );
    assert_eq!(
        header.split(',').count(),
        11,
        "pre-IRR column count: {header}"
    );
    let json = run(&bin, &["report", path, "capgains", "--format", "json"]);
    let v: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert!(
        v["disposals"][0].get("irr_pct").is_none(),
        "no irr field: {json}"
    );
    assert!(v.get("total_irr_pct").is_none(), "no total block: {json}");
    let txt = run(&bin, &["report", path, "capgains", "--no-pager"]);
    let thead = txt
        .lines()
        .find(|l| l.starts_with("Sold"))
        .expect("a table header");
    assert!(!thead.contains("IRR"), "no IRR column by default: {thead}");
}

#[test]
fn irr_is_na_for_short_sales_and_dateless_lots() {
    let bin = require_rledger!();
    // A short cover: money-in-then-out, so no conventional IRR.
    let fs = write_fixture(LEDGER_SHORT);
    let sp = fs.path().to_str().unwrap();
    // CSV: the irr_pct field is empty — asserted as the exact final field, not a
    // bare `ends_with(',')` which would also pass if a later column were dropped.
    let csv = run(
        &bin,
        &["report", sp, "capgains", "--irr", "--format", "csv"],
    );
    let cols: Vec<&str> = csv
        .lines()
        .nth(1)
        .expect("a disposal row")
        .split(',')
        .collect();
    assert_eq!(cols.len(), 12, "all columns present: {csv}");
    assert_eq!(cols[11], "", "short sale has no rate: {csv}");
    // Text renders `n/a`, and the pooled line reports 0-of-1 coverage.
    let txt = run(&bin, &["report", sp, "capgains", "--irr", "--no-pager"]);
    assert!(txt.contains("n/a"), "short sale renders n/a: {txt}");
    assert!(txt.contains("(0 of 1 lots)"), "coverage annotated: {txt}");
    // JSON renders null.
    let json = run(
        &bin,
        &["report", sp, "capgains", "--irr", "--format", "json"],
    );
    let v: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert_eq!(v["disposals"][0]["irr_pct"], serde_json::Value::Null);

    // An AVERAGE-cost lot has no acquisition date to run the clock from.
    let fa = write_fixture(LEDGER_AVERAGE);
    let ap = fa.path().to_str().unwrap();
    let avg = run(
        &bin,
        &["report", ap, "capgains", "--irr", "--format", "csv"],
    );
    let acols: Vec<&str> = avg
        .lines()
        .nth(1)
        .expect("a disposal row")
        .split(',')
        .collect();
    assert_eq!(acols[11], "", "dateless lot has no rate: {avg}");
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

/// An ambiguous STRICT reduction makes the report REFUSE, not return empty.
///
/// This test previously asserted the opposite — that the report succeeded with
/// a header-only CSV, on the reasoning that no disposal was fabricated. Not
/// fabricating a row was right; exiting 0 was not. A header-only capital-gains
/// CSV is indistinguishable from "you had no disposals this year", so the
/// failure mode was a confident, complete-looking answer over a ledger that
/// did not book — the exact hazard `bail_on_parse_errors` already exists to
/// prevent one phase earlier.
///
/// Changed by #1987, where the same unbooked directives made `report balances`
/// panic and `query BALANCES` print a negative holding. Booking failures are
/// now refused across the board rather than each report improvising.
#[test]
fn ambiguous_strict_reduction_is_refused() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_AMBIGUOUS);
    let path = f.path().to_str().unwrap();

    let out = Command::new(&bin)
        .args(["report", path, "capgains", "--format", "csv"])
        .output()
        .expect("run");
    let stderr = String::from_utf8_lossy(&out.stderr);

    assert!(
        !out.status.success(),
        "an unbooked ledger must not yield an exit-0 report: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert!(
        stderr.contains("could not be booked"),
        "the refusal must say why: {stderr}"
    );
    // And still no fabricated disposal, which was the original point.
    assert!(
        !String::from_utf8_lossy(&out.stdout).contains("AAPL"),
        "no disposal may be fabricated from an unbooked sale: {}",
        String::from_utf8_lossy(&out.stdout)
    );
}
