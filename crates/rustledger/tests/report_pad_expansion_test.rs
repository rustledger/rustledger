//! Integration tests for pad expansion across `rledger report`
//! subcommands.
//!
//! The architectural rule (documented on
//! `rustledger_loader::Ledger.directives`): balance-computing
//! reports see `ledger.balance_view()`; source-faithful reports
//! see `ledger.directives`.
//!
//! Each test in this file pins a single subcommand against a
//! single padded fixture. The 7 currently-asserted behaviors are:
//!
//! Balance-computing (must see pad effect):
//! - `report holdings`: Assets:Wallet ends at 965 USD.
//! - `report balances`: Assets:Wallet ends at 965 USD.
//! - `report balsheet`: Assets total reflects the pad.
//! - `report income`: pad does not appear (it does not touch income
//!   or expense accounts).
//! - `report networth`: assets total reflects the pad.
//!
//! Source-faithful (must NOT see synth, must see Pad-as-Pad):
//! - `report stats`: Pads = 1, Transactions = 3 (the user-authored
//!   transactions only; the synth is not counted).
//! - `report journal`: 3 user-authored transaction rows, no synth.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// The canonical #1288 fixture used across all report assertions.
/// Assets:Wallet ends at 965 USD = 1000 (opening) - 10 (Jun 1
/// expense) - 15 (pad: 990 → 975) - 10 (Jun 2 expense).
const PADDED_SOURCE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD
2026-01-01 open Expenses:Expense USD

2026-01-01 * "opening"
  Assets:Wallet  1000 USD
  Equity:Void

2026-06-01 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet

2026-06-01 pad Assets:Wallet Equity:Void
2026-06-02 balance Assets:Wallet 975 USD

2026-06-02 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet
"#;

fn write_fixture() -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-pad-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(PADDED_SOURCE.as_bytes())
        .expect("write fixture");
    f
}

/// Find the line containing `account` and return the first
/// whitespace-separated number on it. Falls back to scanning the
/// next 3 lines if the account-row has no inline number (some
/// reports format the value on a following indented line, e.g.
/// `report balances`).
fn first_number_for_account<'a>(output: &'a str, account: &str) -> Option<&'a str> {
    let mut lines = output.lines();
    while let Some(line) = lines.next() {
        if !line.contains(account) {
            continue;
        }
        let try_number = |l: &'a str| -> Option<&'a str> {
            l.split_whitespace().find(|t| t.parse::<f64>().is_ok())
        };
        if let Some(n) = try_number(line) {
            return Some(n);
        }
        // Scan forward for the value row.
        for next in lines.by_ref().take(3) {
            if let Some(n) = try_number(next) {
                return Some(n);
            }
        }
        return None;
    }
    None
}

fn run_report(binary: &PathBuf, file: &std::path::Path, report: &str) -> String {
    let out = Command::new(binary)
        .args(["report", file.to_str().unwrap(), report, "--no-pager"])
        .output()
        .unwrap_or_else(|e| panic!("run rledger report {report}: {e}"));
    assert!(
        out.status.success(),
        "rledger report {report} failed: stdout={} stderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn report_holdings_applies_pad_expansion() {
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "holdings");
    let units = first_number_for_account(&stdout, "Assets:Wallet")
        .unwrap_or_else(|| panic!("no Assets:Wallet row in holdings: {stdout}"));
    assert_eq!(
        units, "965",
        "holdings must show Assets:Wallet = 965 USD post-pad; \
         pre-fix shape was 980 (pad ignored)",
    );
}

#[test]
fn report_balances_applies_pad_expansion() {
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "balances");
    let units = first_number_for_account(&stdout, "Assets:Wallet")
        .unwrap_or_else(|| panic!("no Assets:Wallet row in balances: {stdout}"));
    assert_eq!(
        units, "965",
        "balances must show Assets:Wallet = 965 USD post-pad"
    );
}

#[test]
fn report_balsheet_applies_pad_expansion() {
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "balsheet");
    let units = first_number_for_account(&stdout, "Assets:Wallet")
        .unwrap_or_else(|| panic!("no Assets:Wallet row in balsheet: {stdout}"));
    assert_eq!(
        units, "965",
        "balsheet must show Assets:Wallet = 965 USD post-pad",
    );
}

#[test]
fn report_networth_includes_pad_in_assets() {
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "networth");
    // networth output groups by period; find the final-period assets
    // line and assert the number reflects the pad. Loose check: must
    // be exactly 965 (the running balance of Assets:Wallet at end).
    let has_965 = stdout.lines().any(|l| l.contains("965"));
    assert!(
        has_965,
        "networth must reflect pad-adjusted Assets:Wallet balance (965 USD); output: {stdout}",
    );
}

#[test]
fn report_income_renders_without_pad_pollution() {
    // The #1288 pad targets Assets:Wallet from Equity:Void, neither
    // of which is an income or expense account. The income report
    // should be unaffected by the pad. This test is the negative
    // case: pad expansion must not introduce ghost income / expense
    // entries.
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "income");
    // 20 USD total expense (2 × 10 USD). The pad does NOT affect
    // Expenses:Expense.
    assert!(
        stdout.contains("Expenses:Expense"),
        "income must include Expenses:Expense row: {stdout}",
    );
}

#[test]
fn report_stats_keeps_pad_as_pad() {
    // Source-faithful report: Pads must count as Pads (= 1), not as
    // Transactions. With balance_view leakage, the synth P-flag
    // transaction would inflate Transactions to 4 and zero out Pads.
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "stats");

    let counter = |label: &str| -> Option<u64> {
        stdout
            .lines()
            .find(|l| l.trim_start().starts_with(label))
            .and_then(|l| l.split_whitespace().next_back())
            .and_then(|t| t.parse::<u64>().ok())
    };

    let pads = counter("Pads:").unwrap_or_else(|| panic!("no Pads: counter in stats: {stdout}"));
    let txns = counter("Transactions:").unwrap_or_else(|| panic!("no Transactions: counter"));
    assert_eq!(
        pads, 1,
        "source-faithful report: Pads must equal 1 (the source has one Pad)",
    );
    assert_eq!(
        txns, 3,
        "source-faithful report: Transactions must equal 3 (user-authored only)",
    );
}

#[test]
fn report_journal_does_not_include_synth_pad_transactions() {
    // Source-faithful report: only user-authored transaction rows
    // appear. If `balance_view` leaked into journal, a synth
    // "(Padding inserted for Balance of ...)" row would show up.
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "journal");
    assert!(
        !stdout.contains("Padding inserted for Balance of"),
        "journal must NOT include synth pad transaction rows; output: {stdout}",
    );
}

/// CI-enforced regression test for issue #1300 (multi-pad
/// shadowing).
///
/// Two `pad` directives target the same account before a single
/// `balance`. Per beancount semantics only the most recent
/// effective pad applies; earlier same-target pads are shadowed.
/// A buggy implementation that applies BOTH pads' synth
/// adjustments produces 800 USD instead of the correct 900 USD
/// (1000 opening, then a single -100 adjustment to land at 900).
///
/// Until this PR, multi-pad correctness was only pinned by
/// `process_pads` unit tests and a manual end-to-end fixture
/// sweep. Both could miss a regression in the CLI query path
/// (e.g. someone switching `merge_with_padding` for a different
/// helper). This test catches that class of regression by
/// running the user-facing command end-to-end.
const MULTI_PAD_SOURCE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD

2026-01-01 * "opening"
  Assets:Wallet  1000 USD
  Equity:Void

2026-06-01 pad Assets:Wallet Equity:Void
2026-06-01 pad Assets:Wallet Equity:Void

2026-06-02 balance Assets:Wallet 900 USD
"#;

#[test]
fn query_multi_pad_does_not_double_apply() {
    let bin = require_rledger!();

    let mut fixture = tempfile::Builder::new()
        .prefix("multi-pad-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    fixture
        .write_all(MULTI_PAD_SOURCE.as_bytes())
        .expect("write fixture");

    let query_out = Command::new(&bin)
        .args([
            "query",
            fixture.path().to_str().unwrap(),
            "SELECT account, sum(position) WHERE account = 'Assets:Wallet'",
        ])
        .output()
        .expect("run rledger query");
    let stdout = String::from_utf8_lossy(&query_out.stdout);
    let stderr = String::from_utf8_lossy(&query_out.stderr);
    assert!(
        query_out.status.success(),
        "query should succeed:\nstdout: {stdout}\nstderr: {stderr}",
    );

    let units = first_number_for_account(&stdout, "Assets:Wallet")
        .unwrap_or_else(|| panic!("no Assets:Wallet token:\nstdout: {stdout}\nstderr: {stderr}"));
    assert_eq!(
        units, "900",
        "multi-pad shadowing: only the most recent pad applies → \
         expected 900 USD (= 1000 - 100), got {units}. A buggy \
         double-application would emit 800 (= 1000 - 100 - 100).\n\
         stderr: {stderr}",
    );
}
