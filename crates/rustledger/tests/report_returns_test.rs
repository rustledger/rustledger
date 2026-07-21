//! `rledger report returns` — end-to-end coverage of the money-weighted
//! return report: the boundary model (the `--income` scope decides whether a
//! dividend-to-bank counts), the reporting-currency default, and the error
//! paths.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// Buy 10 AAPL for 1000, receive a 20 dividend to the bank, hold to a 130
/// close. With `--income` the dividend is a flow; without it, it is invisible
/// (its transaction touches no investment account).
const LEDGER: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Bank
2020-01-01 open Assets:Broker:Stock
2020-01-01 open Income:Dividends

2020-01-01 * "Buy AAPL"
  Assets:Broker:Stock  10 AAPL {100 USD}
  Assets:Bank         -1000 USD

2020-06-01 * "Dividend"
  Assets:Bank         20 USD
  Income:Dividends   -20 USD

2020-12-31 price AAPL 130 USD
"#;

/// A ledger with no `operating_currency` option, to exercise the
/// missing-reporting-currency error.
const LEDGER_NO_CCY: &str = r#"2020-01-01 open Assets:Bank
2020-01-01 open Assets:Broker:Stock

2020-01-01 * "Buy AAPL"
  Assets:Broker:Stock  10 AAPL {100 USD}
  Assets:Bank         -1000 USD

2020-12-31 price AAPL 130 USD
"#;

/// An investment position seeded by `pad` + `balance` (no explicit buy). The
/// returns report must value it, which only works if the pad-expanded
/// `balance_view` reaches extraction — i.e. `Report::Returns` is in the
/// `needs_balance_view` gate.
const LEDGER_PAD: &str = r#"option "operating_currency" "USD"

2019-12-31 open Assets:Broker:Cash
2019-12-31 open Equity:Opening-Balances

2019-12-31 pad Assets:Broker:Cash Equity:Opening-Balances
2020-01-01 balance Assets:Broker:Cash 500 USD
"#;

/// A flat first half then a big contribution right before a +20% second half:
/// the money-weighted and time-weighted returns diverge (good contribution
/// timing lifts MWR above the investments' own TWR).
const LEDGER_TIMING: &str = r#"option "operating_currency" "USD"

2021-01-01 open Assets:Bank
2021-01-01 open Assets:Broker:Stock

2021-01-01 * "Buy"
  Assets:Broker:Stock  10 AAPL {100 USD}
  Assets:Bank         -1000 USD

2021-07-01 price AAPL 100 USD
2021-07-01 * "Buy more before the rally"
  Assets:Broker:Stock  10 AAPL {100 USD}
  Assets:Bank         -1000 USD

2022-01-01 price AAPL 120 USD
"#;

/// Two `returns-group:`-tagged holdings; the Tech group also tags its dividend
/// income account, so Tech's return is dividend-inclusive.
const LEDGER_GROUPS: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Broker:AAPL
  returns-group: "Tech"
2020-01-01 open Assets:Broker:BND
  returns-group: "Bonds"
2020-01-01 open Assets:Bank
2020-01-01 open Income:Dividends
  returns-group: "Tech"

2020-01-01 * "buy aapl"
  Assets:Broker:AAPL  10 AAPL {100 USD}
  Assets:Bank        -1000 USD
2020-01-01 * "buy bnd"
  Assets:Broker:BND  10 BND {50 USD}
  Assets:Bank        -500 USD
2020-06-01 * "aapl dividend"
  Assets:Bank         20 USD
  Income:Dividends   -20 USD

2020-12-31 price AAPL 130 USD
2020-12-31 price BND 55 USD
"#;

/// Like `LEDGER_GROUPS` but only AAPL (+ its dividend account) is tagged; MSFT is
/// an in-scope holding left untagged, so it must collect into the `(ungrouped)`
/// residual and the group rows must still reconcile with the whole-scope TOTAL.
const LEDGER_GROUPS_PARTIAL: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Broker:AAPL
  returns-group: "Tech"
2020-01-01 open Assets:Broker:MSFT
2020-01-01 open Assets:Bank
2020-01-01 open Income:Dividends
  returns-group: "Tech"

2020-01-01 * "buy aapl"
  Assets:Broker:AAPL  10 AAPL {100 USD}
  Assets:Bank        -1000 USD
2020-01-01 * "buy msft"
  Assets:Broker:MSFT  10 MSFT {50 USD}
  Assets:Bank        -500 USD
2020-06-01 * "aapl dividend"
  Assets:Bank         20 USD
  Income:Dividends   -20 USD

2020-12-31 price AAPL 130 USD
2020-12-31 price MSFT 55 USD
"#;

fn write_fixture(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-returns-")
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

/// The value on a labeled text-report line (`"Label      value"`), trimmed.
/// The label is padded to a fixed width, so stripping the label prefix and
/// trimming yields exactly the value — a precise assertion, not a substring
/// that could match digits elsewhere in the output.
fn field<'a>(out: &'a str, label: &str) -> &'a str {
    out.lines()
        .find(|l| l.starts_with(label))
        .map_or("", |l| l[label.len()..].trim())
}

#[test]
fn money_weighted_return_with_dividend_scoped_as_income() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--income",
            "Income:Dividends",
            "--end",
            "2020-12-31",
            "--no-pager",
        ],
    );
    // Three flows: -1000 buy, +20 dividend, +1300 terminal.
    assert_eq!(field(&out, "Cash flows"), "3", "flow count: {out}");
    assert_eq!(field(&out, "Invested"), "1000 USD", "invested: {out}");
    assert_eq!(
        field(&out, "Distributions"),
        "20 USD",
        "distributions: {out}"
    );
    assert_eq!(
        field(&out, "Current value"),
        "1300 USD",
        "current value: {out}"
    );
    // XIRR ~32.36% with the dividend counted.
    assert!(
        field(&out, "Money-weighted return").starts_with("32.3"),
        "expected ~32.3% money-weighted return: {out}"
    );
}

#[test]
fn dividend_to_bank_is_excluded_without_income_scope() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--end",
            "2020-12-31",
            "--no-pager",
        ],
    );
    // No --income: the dividend transaction touches no investment account, so it
    // is not a flow. Two flows remain: -1000 buy, +1300 terminal → exactly 30%.
    assert_eq!(field(&out, "Cash flows"), "2", "flow count: {out}");
    assert_eq!(
        field(&out, "Distributions"),
        "0 USD",
        "distributions should be 0: {out}"
    );
    assert_eq!(
        field(&out, "Money-weighted return"),
        "30.00%",
        "expected exactly 30.00% without the dividend: {out}"
    );
}

#[test]
fn reporting_currency_defaults_to_operating_currency() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    // No --currency: falls back to option "operating_currency" "USD".
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--end",
            "2020-12-31",
            "--no-pager",
        ],
    );
    // Assert on the reporting-currency line specifically — a bare
    // `contains("USD")` would pass on the fixture's other USD literals even if
    // the default were wrong.
    assert_eq!(
        field(&out, "Reporting currency").split_whitespace().next(),
        Some("USD"),
        "reporting currency should default to the operating currency USD: {out}"
    );
}

#[test]
fn json_format_emits_the_expected_fields() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--income",
            "Income:Dividends",
            "--end",
            "2020-12-31",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    for key in [
        "reporting_currency",
        "as_of",
        "cash_flows",
        "invested",
        "distributions",
        "current_value",
        "money_weighted_return_pct",
        "time_weighted_return_pct",
    ] {
        assert!(out.contains(key), "json missing `{key}`: {out}");
    }
    assert!(out.contains("\"as_of\": \"2020-12-31\""), "as_of: {out}");
}

#[test]
fn missing_reporting_currency_is_an_actionable_error() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_NO_CCY);
    let path = f.path().to_str().unwrap();
    // No operating_currency option and no --currency → must fail with guidance.
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--end",
            "2020-12-31",
            "--no-pager",
        ])
        .output()
        .expect("spawn rledger");
    assert!(
        !out.status.success(),
        "expected failure without a reporting currency"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("reporting currency") && stderr.contains("--currency"),
        "error should name --currency / operating_currency: {stderr}",
    );
}

#[test]
fn pad_seeded_holding_is_valued() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_PAD);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--end",
            "2020-12-31",
            "--no-pager",
        ],
    );
    // The pad seeds 500 USD in the broker cash account: an opening -500 flow
    // paired with the +500 still held → 0% on untouched opening capital. This
    // only works because the pad-expanded balance_view reaches extraction.
    assert_eq!(
        field(&out, "Invested"),
        "500 USD",
        "pad-seeded capital: {out}"
    );
    assert_eq!(
        field(&out, "Current value"),
        "500 USD",
        "pad-seeded holding: {out}"
    );
    assert_eq!(
        field(&out, "Money-weighted return"),
        "0.00%",
        "untouched → 0%: {out}"
    );
}

#[test]
fn time_weighted_return_diverges_from_money_weighted_on_timing() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_TIMING);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--end",
            "2022-01-01",
            "--no-pager",
        ],
    );
    // The investments went flat (0%) then +20% → TWR is exactly 20%, regardless
    // of when money went in. MWR is higher because the second 1000 was invested
    // only for the winning half.
    assert_eq!(
        field(&out, "Time-weighted return"),
        "20.00%",
        "TWR should be 20% (flat then +20%, timing-independent): {out}"
    );
    let mwr: f64 = field(&out, "Money-weighted return")
        .trim_end_matches('%')
        .parse()
        .expect("parse MWR");
    assert!(
        mwr > 25.0,
        "MWR should exceed TWR given the good contribution timing: {out}"
    );
}

/// Extract a group object's field from the grouped JSON output. Naive but
/// sufficient for the test fixtures (no nested braces inside a group object).
fn json_group_field(out: &str, group: &str, field: &str) -> String {
    let marker = format!(r#""group": "{group}""#);
    let start = out
        .find(&marker)
        .unwrap_or_else(|| panic!("group {group} not in {out}"));
    let obj_end = out[start..].find('}').map_or(out.len(), |e| start + e);
    let obj = &out[start..obj_end];
    let key = format!(r#""{field}": "#);
    let fs = obj
        .find(&key)
        .unwrap_or_else(|| panic!("field {field} not in {obj}"))
        + key.len();
    obj[fs..]
        .split([',', '}'])
        .next()
        .unwrap()
        .trim()
        .trim_matches('"')
        .to_string()
}

#[test]
fn returns_group_metadata_breaks_down_dividend_inclusive() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_GROUPS);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--income",
            "Income:Dividends",
            "--by-group",
            "--end",
            "2020-12-31",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    // Tech: 1000 in, +20 dividend (its income account is tagged Tech →
    // dividend-INCLUSIVE), worth 1300 → 32.36%.
    assert_eq!(
        json_group_field(&out, "Tech", "money_weighted_return_pct"),
        "32.36",
        "{out}"
    );
    assert_eq!(
        json_group_field(&out, "Tech", "distributions"),
        "20",
        "dividend included: {out}"
    );
    assert_eq!(
        json_group_field(&out, "Tech", "current_value"),
        "1300",
        "{out}"
    );
    // Bonds: 500 in, worth 550 → 10%.
    assert_eq!(
        json_group_field(&out, "Bonds", "money_weighted_return_pct"),
        "10.00",
        "{out}"
    );
    // The whole-scope TOTAL is present too.
    assert_eq!(
        json_group_field(&out, "TOTAL", "current_value"),
        "1850",
        "{out}"
    );
}

#[test]
fn by_group_collects_untagged_holdings_into_reconciling_ungrouped_residual() {
    let bin = require_rledger!();
    // AAPL is tagged Tech; MSFT is an untagged in-scope holding.
    let f = write_fixture(LEDGER_GROUPS_PARTIAL);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--income",
            "Income:Dividends",
            "--by-group",
            "--end",
            "2020-12-31",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    // Tech: 1000 in, +20 dividend, worth 1300.
    assert_eq!(
        json_group_field(&out, "Tech", "current_value"),
        "1300",
        "{out}"
    );
    // MSFT, left untagged, lands in the residual — not silently dropped.
    assert_eq!(
        json_group_field(&out, "(ungrouped)", "current_value"),
        "550",
        "{out}"
    );
    // And the rows partition the total: 1300 + 550 = 1850, invested 1000 + 500 =
    // 1500. Every in-scope holding is in exactly one row.
    assert_eq!(
        json_group_field(&out, "TOTAL", "current_value"),
        "1850",
        "{out}"
    );
    assert_eq!(json_group_field(&out, "TOTAL", "invested"), "1500", "{out}");
}

#[test]
fn without_by_group_output_is_the_single_summary() {
    let bin = require_rledger!();
    // Even with `returns-group:` metadata present, the default (no --by-group)
    // output is the unchanged single summary — grouping is strictly opt-in.
    let f = write_fixture(LEDGER_GROUPS);
    let path = f.path().to_str().unwrap();
    let out = run(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--income",
            "Income:Dividends",
            "--end",
            "2020-12-31",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    // The single-summary schema has no "groups" array.
    assert!(
        !out.contains("\"groups\""),
        "default output must be the single summary, not grouped: {out}"
    );
}
