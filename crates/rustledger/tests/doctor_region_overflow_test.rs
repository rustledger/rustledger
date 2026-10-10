//! `rledger doctor region` must not panic on totals past `Decimal`'s range,
//! and must not print a clamped or rounded one (#2572).
//!
//! Two operators panicked on such ledgers: the lot cost total
//! `units × per-unit` under `--conversion cost` (`CostNumber::total_for`), and
//! the `+=` that nets each account over the region. Both now carry the exact
//! figure.

mod common;

use std::io::Write;

fn region(bin: &std::path::Path, source: &str, conversion: Option<&str>) -> String {
    let mut f = tempfile::Builder::new()
        .prefix("doctor-overflow-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let path = f.path().to_str().unwrap().to_string();
    let mut args = vec!["doctor", "region", &path, "1", "40"];
    if let Some(c) = conversion {
        args.extend(["--conversion", c]);
    }
    let out = std::process::Command::new(bin)
        .args(&args)
        .output()
        .expect("run doctor region");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success() && !stderr.contains("panicked"),
        "doctor region failed:\n{stdout}\n{stderr}"
    );
    stdout
}

/// `1e16` units at `1e13` per unit cost `1e29`, past `Decimal::MAX` (~7.9e28).
#[test]
fn a_cost_total_past_the_range_is_printed_exactly() {
    let bin = require_rledger!();
    let out = region(
        &bin,
        "2024-01-01 open Assets:Broker\n\
         2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"buy\"\n\
        \x20 Assets:Broker  10000000000000000 HOOL {10000000000000.00 USD}\n\
        \x20 Assets:Cash   -10000000000000000 CASHU\n",
        Some("cost"),
    );
    assert!(
        out.contains("Assets:Broker 100000000000000000000000000000.00 USD"),
        "{out}"
    );
    assert!(
        out.contains("Assets:Broker:USD: 100000000000000000000000000000.00"),
        "{out}"
    );
}

/// Two postings of `5e28` to one account net to `1e29`.
#[test]
fn a_net_change_past_the_range_is_printed_exactly() {
    let bin = require_rledger!();
    let out = region(
        &bin,
        "2024-01-01 open Assets:A\n\
         2024-01-01 open Equity:Opening\n\
         2024-02-01 * \"one\"\n\
        \x20 Assets:A  50000000000000000000000000000 X\n\
        \x20 Equity:Opening  -50000000000000000000000000000 X\n\
         2024-02-02 * \"two\"\n\
        \x20 Assets:A  50000000000000000000000000000 X\n\
        \x20 Equity:Opening  -50000000000000000000000000000 X\n",
        None,
    );
    assert!(
        out.contains("Assets:A:X: 100000000000000000000000000000"),
        "{out}"
    );
    assert!(
        out.contains("Equity:Opening:X: -100000000000000000000000000000"),
        "{out}"
    );
}

/// A net that leaves the range and comes back prints as an ordinary figure:
/// `4e28 + 4e28` is past `Decimal::MAX`, and less `39999999999999999999999999999`
/// it is back inside.
#[test]
fn a_net_change_back_in_range_prints_as_a_decimal() {
    let bin = require_rledger!();
    let out = region(
        &bin,
        "2024-01-01 open Assets:A\n\
         2024-01-01 open Equity:Opening\n\
         2024-02-01 * \"one\"\n\
        \x20 Assets:A  40000000000000000000000000000 X\n\
        \x20 Equity:Opening  -40000000000000000000000000000 X\n\
         2024-02-02 * \"two\"\n\
        \x20 Assets:A  40000000000000000000000000000 X\n\
        \x20 Equity:Opening  -40000000000000000000000000000 X\n\
         2024-02-03 * \"three\"\n\
        \x20 Assets:A  -39999999999999999999999999999 X\n\
        \x20 Equity:Opening  39999999999999999999999999999 X\n",
        None,
    );
    assert!(
        out.contains("Assets:A:X: 40000000000000000000000000001\n"),
        "{out}"
    );
}
