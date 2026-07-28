//! `rledger report networth --period` — bucketing and labeling.
//!
//! The weekly bucket used to be labeled from the ISO week NUMBER paired with
//! the CALENDAR year, and those disagree at a year boundary: 2024-12-31 is ISO
//! week 1 of 2025 but rendered `2024-W01`, colliding with the real 2024-W01 and
//! silently summing two different weeks into one row (#1864). Nothing on screen
//! said a merge had happened, so the reported net worth for early January was
//! simply wrong.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// Two transactions in ISO weeks that collide under the buggy label: one in
/// 2024-W01, one in 2025-W01 (which falls on 2024-12-31, a CALENDAR-2024 date).
const YEAR_BOUNDARY: &str = r#"option "operating_currency" "USD"

2024-01-01 open Assets:Cash
2024-01-01 open Equity:Opening

2024-01-03 * "early jan — ISO 2024-W01"
  Assets:Cash    100.00 USD
  Equity:Opening

2024-12-31 * "new year eve — ISO 2025-W01"
  Assets:Cash    200.00 USD
  Equity:Opening
"#;

fn write_fixture(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-networth-")
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

/// Weeks in different ISO years are different buckets.
#[test]
fn weeks_in_different_iso_years_do_not_share_a_bucket() {
    let bin = require_rledger!();
    let f = write_fixture(YEAR_BOUNDARY);
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report", path, "networth", "--period", "weekly", "--format", "csv",
        ],
    );

    let rows = csv.lines().filter(|l| l.starts_with("20")).count();
    assert_eq!(
        rows, 2,
        "the two dates are in different ISO weeks and must not merge; got:\n{csv}"
    );

    // 2024-12-31 is ISO week 1 of 2025 — labeled by the ISO week-YEAR, not the
    // calendar year it happens to fall in.
    assert!(csv.contains("2024-W01"), "missing the 2024-W01 row:\n{csv}");
    assert!(
        csv.contains("2025-W01"),
        "2024-12-31 belongs to ISO 2025-W01; a `2024-W01` label here is the \
         collision this test exists for:\n{csv}"
    );
}

/// The amounts land in the right buckets, not merely in separate rows.
///
/// A label fix that still bucketed by the old key would produce two rows with
/// the wrong contents, and a row-count assertion alone would pass.
#[test]
fn each_iso_week_carries_its_own_running_total() {
    let bin = require_rledger!();
    let f = write_fixture(YEAR_BOUNDARY);
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report", path, "networth", "--period", "weekly", "--format", "csv",
        ],
    );

    let row = |label: &str| -> String {
        csv.lines()
            .find(|l| l.starts_with(label))
            .unwrap_or_else(|| panic!("no {label} row in:\n{csv}"))
            .to_string()
    };
    // Net worth is cumulative: the first week holds 100, and by the last week
    // the running total is 300.
    assert!(
        row("2024-W01").contains("100.00"),
        "2024-W01 should hold only the early-January 100.00: {}",
        row("2024-W01")
    );
    assert!(
        row("2025-W01").contains("300.00"),
        "2025-W01 is cumulative and should hold 300.00: {}",
        row("2025-W01")
    );
}

/// The other periods are unaffected — they use calendar fields with no
/// week-year mismatch, and the fix must not disturb them.
#[test]
fn monthly_and_yearly_buckets_are_unchanged() {
    let bin = require_rledger!();
    let f = write_fixture(YEAR_BOUNDARY);
    let path = f.path().to_str().unwrap();

    let monthly = run(
        &bin,
        &[
            "report", path, "networth", "--period", "monthly", "--format", "csv",
        ],
    );
    assert!(monthly.contains("2024-01"), "monthly:\n{monthly}");
    assert!(monthly.contains("2024-12"), "monthly:\n{monthly}");

    let yearly = run(
        &bin,
        &[
            "report", path, "networth", "--period", "yearly", "--format", "csv",
        ],
    );
    // Both dates are in CALENDAR 2024, so yearly is a single bucket — the
    // calendar year is the right key here, unlike for ISO weeks.
    let rows = yearly.lines().filter(|l| l.starts_with("20")).count();
    assert_eq!(rows, 1, "both dates are calendar-2024:\n{yearly}");
}
