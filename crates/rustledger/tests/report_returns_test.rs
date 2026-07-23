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
/// an in-scope holding left untagged, so it is omitted from the breakdown while
/// still contributing to the whole-scope TOTAL.
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

/// Two groups funded from a shared in-scope settlement-cash account
/// (`Assets:Broker:Cash`, under `--investments Assets:Broker`). Each group's buy
/// draws on the pooled cash, so neither group is self-contained.
const LEDGER_SHARED_CASH: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Broker:Cash
2020-01-01 open Assets:Broker:AAPL
  returns-group: "Tech"
2020-01-01 open Assets:Broker:BND
  returns-group: "Bonds"
2020-01-01 open Equity:Opening

2020-01-01 * "fund the brokerage"
  Assets:Broker:Cash  1500 USD
  Equity:Opening     -1500 USD
2020-01-01 * "buy aapl"
  Assets:Broker:AAPL  10 AAPL {100 USD}
  Assets:Broker:Cash -1000 USD
2020-01-01 * "buy bnd"
  Assets:Broker:BND  10 BND {50 USD}
  Assets:Broker:Cash -500 USD

2020-12-31 price AAPL 130 USD
2020-12-31 price BND 55 USD
"#;

/// A real holding tagged `Tech`, plus two malformed tags: an Equity account
/// (out of scope) and a numeric (non-string) value.
const LEDGER_BAD_TAGS: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Broker:AAPL
  returns-group: "Tech"
2020-01-01 open Assets:Broker:MSFT
  returns-group: 5
2020-01-01 open Assets:Bank
2020-01-01 open Equity:Opening
  returns-group: "Tech"

2020-01-01 * "buy aapl"
  Assets:Broker:AAPL  10 AAPL {100 USD}
  Assets:Bank        -1000 USD

2020-12-31 price AAPL 130 USD
"#;

/// A group (`Payouts`) that tags only an income account — no holding, so its
/// investment scope is empty.
const LEDGER_INCOME_ONLY_GROUP: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Broker:AAPL
2020-01-01 open Assets:Bank
2020-01-01 open Income:Dividends
  returns-group: "Payouts"

2020-01-01 * "buy aapl"
  Assets:Broker:AAPL  10 AAPL {100 USD}
  Assets:Bank        -1000 USD
2020-06-01 * "dividend"
  Assets:Bank         20 USD
  Income:Dividends   -20 USD

2020-12-31 price AAPL 130 USD
"#;

/// A tagged parent account (`Assets:Broker`, group `All`) that is an ancestor of
/// a tagged child (`Assets:Broker:AAPL`, group `Tech`). Because `Scope` matches
/// by prefix, `All` also captures AAPL — a cross-group overlap that must warn.
const LEDGER_PREFIX_OVERLAP: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Broker
  returns-group: "All"
2020-01-01 open Assets:Broker:AAPL
  returns-group: "Tech"
2020-01-01 open Assets:Bank

2020-01-01 * "buy aapl"
  Assets:Broker:AAPL  10 AAPL {100 USD}
  Assets:Bank        -1000 USD

2020-12-31 price AAPL 130 USD
"#;

/// A `Tech` group active from 2020, plus a `Crypto` group whose account is opened
/// (and only transacts) in 2022. A report as of 2020 must not show Crypto.
const LEDGER_FUTURE_GROUP: &str = r#"option "operating_currency" "USD"

2020-01-01 open Assets:Broker:AAPL
  returns-group: "Tech"
2020-01-01 open Assets:Bank

2020-01-01 * "buy aapl"
  Assets:Broker:AAPL  10 AAPL {100 USD}
  Assets:Bank        -1000 USD

2022-01-01 open Assets:Broker:CRYPTO
  returns-group: "Crypto"
2022-06-01 * "buy crypto"
  Assets:Broker:CRYPTO  1 BTC {30000 USD}
  Assets:Bank          -30000 USD

2020-12-31 price AAPL 130 USD
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

/// Run and return `(stdout, stderr)` — the grouping warnings are on stderr.
fn run_split(binary: &PathBuf, args: &[&str]) -> (String, String) {
    let out = Command::new(binary)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("run rledger {args:?}: {e}"));
    assert!(
        out.status.success(),
        "rledger {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    (
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
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

/// #1850 §4 + review pass 2, finding [0]: a `--by-group` report where one group
/// cannot be valued (here Bonds holds BND priced only in EUR, with no EUR→USD
/// rate, so its boundary flow is unpriceable) must (a) still RENDER the computable
/// groups + `n/a` rows, and (b) exit NON-ZERO so a pipeline gating on exit status
/// does not treat the incomplete report as a full success. The Tech group is
/// fully priced and unaffected.
#[test]
fn by_group_partial_report_renders_but_exits_nonzero() {
    const LEDGER: &str = r#"option "operating_currency" "USD"
2020-01-01 open Assets:Bank
2020-01-01 open Assets:Broker:Tech
  returns-group: "Tech"
2020-01-01 open Assets:Broker:Bonds
  returns-group: "Bonds"
2020-01-02 * "buy tech"
  Assets:Broker:Tech  10 AAPL {100 USD}
  Assets:Bank
2020-01-03 * "buy bonds, priced only in EUR"
  Assets:Broker:Bonds  5 BND {100 EUR}
  Assets:Bank  -500 EUR
2020-12-31 price AAPL 130 USD
"#;
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--by-group",
            "--end",
            "2020-12-31",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");

    // (b) Non-zero exit — the incomplete-report signal for pipelines.
    assert!(
        !out.status.success(),
        "a partial by-group report must exit non-zero; stderr:\n{}",
        String::from_utf8_lossy(&out.stderr),
    );
    // (a) The partial report is still written to stdout: Tech's figures render,
    // and the unvaluable Bonds + TOTAL rows are `n/a`.
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("Tech"),
        "computable group rendered:\n{stdout}"
    );
    assert!(
        stdout
            .lines()
            .any(|l| l.starts_with("Bonds") && l.contains("n/a")),
        "unvaluable Bonds row is n/a:\n{stdout}"
    );
    // The reason and the incompleteness are on stderr.
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("incomplete") || stderr.contains("unavailable"),
        "stderr explains the incompleteness:\n{stderr}"
    );
}

#[test]
fn by_group_omits_untagged_holdings_no_residual() {
    let bin = require_rledger!();
    // AAPL is tagged Tech; MSFT is an untagged in-scope holding. Under the
    // independent-sub-portfolio model, MSFT is simply omitted from the breakdown
    // (no `(ungrouped)` residual) — it still contributes to the whole-scope TOTAL.
    let f = write_fixture(LEDGER_GROUPS_PARTIAL);
    let path = f.path().to_str().unwrap();
    let (out, _err) = run_split(
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
    // No residual row: untagged MSFT is omitted from the breakdown entirely.
    assert!(
        !out.contains("(ungrouped)"),
        "there must be no residual row: {out}"
    );
    // The TOTAL is still the whole portfolio (Tech's 1300 + MSFT's 550), NOT the
    // sum of the group rows — 1850 > the single Tech row, proving MSFT is counted
    // in the total though it has no group of its own.
    assert_eq!(
        json_group_field(&out, "TOTAL", "current_value"),
        "1850",
        "{out}"
    );
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
    // Positively pin the single-summary schema (a top-level object with the
    // return fields), AND that it is not the grouped schema (no `groups` array) —
    // a negative-only check could pass on truncated/altered output.
    assert!(
        out.contains("\"money_weighted_return_pct\"") && out.contains("\"reporting_currency\""),
        "default output must be the single-summary schema: {out}"
    );
    assert!(
        !out.contains("\"groups\""),
        "default output must not be the grouped schema: {out}"
    );
}

#[test]
fn by_group_warns_when_a_group_is_not_self_contained() {
    let bin = require_rledger!();
    // Both groups draw on a shared in-scope settlement-cash account, so each
    // group's return counts an intra-portfolio transfer as a flow. That can't be
    // attributed, so it must be surfaced as a warning (not silently misreported).
    let f = write_fixture(LEDGER_SHARED_CASH);
    let path = f.path().to_str().unwrap();
    let (out, err) = run_split(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--by-group",
            "--end",
            "2020-12-31",
            "--no-pager",
        ],
    );
    assert!(
        err.contains("Tech is not self-contained") && err.contains("Assets:Broker:Cash"),
        "expected a self-contained warning naming the shared account: {err}"
    );
    // The warning is advisory: the group's standalone figures are STILL rendered
    // on stdout (not suppressed or errored).
    assert!(
        out.contains("Tech") && out.contains("Bonds"),
        "warned groups must still appear in the report: {out}"
    );
}

#[test]
fn by_group_warns_on_cross_group_prefix_overlap() {
    let bin = require_rledger!();
    // A tagged parent (`Assets:Broker`, group All) is an ancestor of a tagged
    // child (`Assets:Broker:AAPL`, group Tech). `Scope` matches by prefix, so the
    // parent's group also values the child's holding — a double count that must
    // be surfaced.
    let f = write_fixture(LEDGER_PREFIX_OVERLAP);
    let path = f.path().to_str().unwrap();
    let (_out, err) = run_split(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--by-group",
            "--end",
            "2020-12-31",
            "--no-pager",
        ],
    );
    assert!(
        err.contains("overlap by prefix")
            && err.contains("Assets:Broker")
            && err.contains("Assets:Broker:AAPL"),
        "expected a prefix-overlap warning naming both accounts: {err}"
    );
}

#[test]
fn by_group_warns_on_out_of_scope_and_non_string_tags() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_BAD_TAGS);
    let path = f.path().to_str().unwrap();
    let (out, err) = run_split(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--by-group",
            "--end",
            "2020-12-31",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    // Equity account tagged → out of scope, dropped (never valued as a holding).
    assert!(
        err.contains("Equity:Opening ignored")
            && err.contains("not under --investments or --income"),
        "expected an out-of-scope warning: {err}"
    );
    // Numeric tag value → dropped with a distinct warning.
    assert!(
        err.contains("must be a quoted string"),
        "expected a non-string-value warning: {err}"
    );
    // The out-of-scope Equity account is not valued: only the real holding shows.
    assert_eq!(
        json_group_field(&out, "Tech", "current_value"),
        "1300",
        "{out}"
    );
}

#[test]
fn by_group_text_output_renders_rows_and_total() {
    let bin = require_rledger!();
    // Exercise the text (non-JSON) grouped path: it must print a group row and a
    // TOTAL row with aligned columns.
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
            "--no-pager",
        ],
    );
    assert!(out.contains("Tech") && out.contains("Bonds"), "{out}");
    // The text table carries the Distributions column (parity with single-scope
    // output), and Tech's $20 dividend shows in it.
    assert!(
        out.contains("Distributions"),
        "text table needs Distributions: {out}"
    );
    // TOTAL line present with the whole-portfolio current value.
    let total = out
        .lines()
        .find(|l| l.starts_with("TOTAL"))
        .unwrap_or_else(|| panic!("no TOTAL row: {out}"));
    assert!(total.contains("1850"), "TOTAL row: {total}");
    // A footnote makes clear the TOTAL is not the sum of the group rows.
    assert!(
        out.contains("not the sum of the groups"),
        "expected the non-sum TOTAL footnote: {out}"
    );
}

#[test]
fn by_group_income_only_group_is_valued_without_panicking() {
    let bin = require_rledger!();
    // A group with only an income account (no holding) has an empty investment
    // scope: current value 0, undefined MWR (only distributions, no outlay).
    let f = write_fixture(LEDGER_INCOME_ONLY_GROUP);
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
    assert_eq!(
        json_group_field(&out, "Payouts", "current_value"),
        "0",
        "{out}"
    );
    assert_eq!(
        json_group_field(&out, "Payouts", "money_weighted_return_pct"),
        "null",
        "income-only group has no outlay → undefined MWR: {out}"
    );
    // TWR is likewise undefined: with no invested capital there is no holding
    // period to weight. It must be null, not a fabricated flat 0.00%.
    assert_eq!(
        json_group_field(&out, "Payouts", "time_weighted_return_pct"),
        "null",
        "income-only group has no capital → undefined TWR (not 0%): {out}"
    );
}

#[test]
fn by_group_emits_grouped_schema_even_with_no_tags() {
    let bin = require_rledger!();
    // `--by-group` must yield ONE stable schema regardless of ledger content:
    // with no in-scope `returns-group:` tags the output is still the grouped
    // shape (an empty `groups` array plus `total`), not the single-summary
    // object — so a JSON consumer never has to branch on ledger content.
    let f = write_fixture(LEDGER); // no returns-group metadata
    let path = f.path().to_str().unwrap();
    let (out, _err) = run_split(
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
    assert!(
        out.contains("\"groups\": []") && out.contains("\"total\":"),
        "no-tags --by-group must still emit the grouped schema: {out}"
    );

    // The text path for the same no-groups case must not print two horizontal
    // rules back to back (there are no group rows to separate from the TOTAL).
    let (text, _err) = run_split(
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
            "--no-pager",
        ],
    );
    let rules: Vec<usize> = text
        .lines()
        .enumerate()
        .filter(|(_, l)| l.starts_with("---"))
        .map(|(i, _)| i)
        .collect();
    assert!(
        rules.windows(2).all(|w| w[1] != w[0] + 1),
        "no-groups text output must not have adjacent rules:\n{text}"
    );
}

#[test]
fn by_group_csv_output_has_header_group_and_total_rows() {
    let bin = require_rledger!();
    // Exercise the grouped CSV path (only JSON and text were covered).
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
            "csv",
            "--no-pager",
        ],
    );
    // Header row with the group column first.
    assert!(
        out.lines().next().unwrap_or_default().starts_with(
            "group,as_of,reporting_currency,cash_flows,invested,distributions,current_value,"
        ),
        "CSV header: {out}"
    );
    // A group data row and the TOTAL row (the whole-portfolio current value).
    assert!(
        out.lines().any(|l| l.starts_with("Tech,")),
        "expected a Tech group row: {out}"
    );
    let total = out
        .lines()
        .find(|l| l.starts_with("TOTAL,"))
        .unwrap_or_else(|| panic!("no TOTAL row: {out}"));
    assert!(total.contains(",1850,"), "TOTAL row current value: {total}");
}

#[test]
fn by_group_respects_the_end_horizon() {
    let bin = require_rledger!();
    // Grouping must be bounded by --end exactly as extraction is: a group whose
    // account opens after the horizon must not appear as a spurious row.
    let f = write_fixture(LEDGER_FUTURE_GROUP);
    let path = f.path().to_str().unwrap();
    let (out, _err) = run_split(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--by-group",
            "--end",
            "2020-12-31",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    assert_eq!(
        json_group_field(&out, "Tech", "current_value"),
        "1300",
        "{out}"
    );
    assert!(
        !out.contains("Crypto"),
        "a group opened after --end must not appear: {out}"
    );
}

#[test]
fn by_group_json_escapes_control_chars_in_a_label() {
    let bin = require_rledger!();
    // A returns-group value may carry a raw control byte the parser preserves;
    // the JSON label must be escaped (\uXXXX), not emitted raw, so the output
    // stays valid JSON. The label here contains an ESC (U+001B).
    let fixture = "option \"operating_currency\" \"USD\"\n\
        2020-01-01 open Assets:Broker:AAPL\n  returns-group: \"A\u{1b}B\"\n\
        2020-01-01 open Assets:Bank\n\
        2020-01-01 * \"buy\"\n  Assets:Broker:AAPL 10 AAPL {100 USD}\n  Assets:Bank -1000 USD\n\
        2020-12-31 price AAPL 130 USD\n";
    let f = write_fixture(fixture);
    let path = f.path().to_str().unwrap();
    let (out, _err) = run_split(
        &bin,
        &[
            "report",
            path,
            "returns",
            "--investments",
            "Assets:Broker",
            "--by-group",
            "--end",
            "2020-12-31",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    // The raw ESC byte must NOT appear; its  escape must.
    assert!(
        !out.contains('\u{1b}') && out.contains("\\u001b"),
        "control char in a group label must be JSON-escaped: {out:?}"
    );
}
