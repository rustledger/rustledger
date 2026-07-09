//! Regression tests for #1726: `report balances` and `report balsheet`
//! must NET a held-commodity reduction against its augmentation, rather
//! than listing the augmenting and reducing positions as separate rows.
//!
//! Before the fix, a buy of `10 AAPL {150}` followed by a sell of
//! `-5 AAPL {150} @ 180` printed two rows (`10 AAPL` and `-5 AAPL`) —
//! the reduction resolved to a different lot-key than the augmentation,
//! so `Inventory.add` could not cancel them. These reports render only
//! units (never cost), so the correct output is a single `5 AAPL` row.
//! Verified against beancount 3.2.3: `sum(position)` = `5 AAPL {150.00 USD}`.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// Buy 10 AAPL at cost, then sell 5 back at a price. Net holding is 5.
const REDUCTION_SOURCE: &str = r#"option "operating_currency" "USD"

2024-01-01 open Assets:Broker
2024-01-01 open Assets:Cash
2024-01-01 open Income:PnL

2024-01-05 * "buy"
  Assets:Broker   10 AAPL {150.00 USD}
  Assets:Cash  -1500.00 USD

2024-06-10 * "sell half"
  Assets:Broker   -5 AAPL {150.00 USD} @ 180.00 USD
  Assets:Cash    900.00 USD
  Income:PnL    -150.00 USD
"#;

fn write_fixture() -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-reduction-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(REDUCTION_SOURCE.as_bytes())
        .expect("write fixture");
    f
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

/// Every AAPL figure must be the netted `5` — never the pre-fix split of
/// a `10 AAPL` augmentation row and a separate `-5 AAPL` reduction row.
/// (`balsheet` legitimately repeats the holding across the account line,
/// the assets total, and net worth; all must agree on 5.)
fn assert_netted_to_5(stdout: &str, report: &str) {
    let aapl_numbers: Vec<&str> = stdout
        .lines()
        .filter(|l| l.contains("AAPL"))
        .filter_map(|l| l.split_whitespace().find(|t| t.parse::<f64>().is_ok()))
        .collect();
    assert!(
        !aapl_numbers.is_empty(),
        "report {report} shows no AAPL holding at all: {stdout}",
    );
    for n in &aapl_numbers {
        assert_eq!(
            *n, "5",
            "report {report} must net the reduction to 5 AAPL everywhere; \
             pre-fix showed separate 10 and -5 rows. Got {n:?} in: {stdout}",
        );
    }
}

/// Pull the first number that appears on the line mentioning `needle`.
fn number_on_line_with<'a>(stdout: &'a str, needle: &str) -> Option<&'a str> {
    stdout
        .lines()
        .find(|l| l.contains(needle))
        .and_then(|l| l.split_whitespace().find(|t| t.parse::<f64>().is_ok()))
}

/// The drift guard: `balances` and `balsheet` read one shared source
/// (`report_cmd::account_balances`), so they must report the *same* figure
/// for the same account. If a future change re-forks the balance
/// computation, this fails. (This is the invariant the #1726 class violated:
/// the reports each re-derived balances and disagreed.)
#[test]
fn balances_and_balsheet_agree_per_account() {
    let bin = require_rledger!();
    let f = write_fixture();
    let bal = run_report(&bin, f.path(), "balances");
    let bs = run_report(&bin, f.path(), "balsheet");
    // The netted holding must read identically in both reports.
    let bal_aapl = bal
        .lines()
        .filter(|l| l.contains("AAPL"))
        .find_map(|l| l.split_whitespace().find(|t| t.parse::<f64>().is_ok()));
    let bs_aapl = number_on_line_with(&bs, "AAPL");
    assert_eq!(
        bal_aapl, bs_aapl,
        "balances and balsheet must agree on Assets:Broker AAPL \
         (single source of truth); balances={bal_aapl:?} balsheet={bs_aapl:?}",
    );
    assert_eq!(bal_aapl, Some("5"), "both must show the netted 5 AAPL");
}

#[test]
fn report_balances_nets_reduction() {
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "balances");
    assert_netted_to_5(&stdout, "balances");
}

/// The AAPL number on the single line that contains all of `needles`.
fn aapl_number_on_line_with<'a>(stdout: &'a str, needles: &[&str]) -> Option<&'a str> {
    stdout
        .lines()
        .filter(|l| l.contains("AAPL"))
        .find(|l| needles.iter().all(|n| l.contains(n)))
        .and_then(|l| l.split_whitespace().find(|t| t.parse::<f64>().is_ok()))
}

#[test]
fn report_balsheet_nets_reduction() {
    let bin = require_rledger!();
    let f = write_fixture();
    let stdout = run_report(&bin, f.path(), "balsheet");
    // Every AAPL figure is the netted 5 (never the pre-fix 10 / -5 split)...
    assert_netted_to_5(&stdout, "balsheet");
    // ...AND the holding must actually propagate into the assets total and
    // net worth, not just the account row. A regression that dropped AAPL
    // from the totals could otherwise still print a lone `5 AAPL` account
    // row and pass assert_netted_to_5 (Copilot review on #1727).
    assert_eq!(
        aapl_number_on_line_with(&stdout, &["Total Assets"]),
        Some("5"),
        "balsheet must carry the 5 AAPL holding into Total Assets: {stdout}",
    );
    // Net Worth section: the AAPL figure appears after the "Net Worth"
    // header. Take the tail of the output and find its AAPL line.
    let net_worth_tail = stdout.split_once("Net Worth").map_or("", |(_, tail)| tail);
    assert!(
        net_worth_tail
            .lines()
            .any(|l| l.contains("AAPL") && l.split_whitespace().any(|t| t == "5")),
        "balsheet must carry the 5 AAPL holding into Net Worth: {stdout}",
    );
}
