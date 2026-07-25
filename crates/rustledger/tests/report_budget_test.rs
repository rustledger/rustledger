//! `rledger report budget` — end-to-end coverage of budgeted-vs-actual reporting
//! over Fava-compatible `custom "budget"` directives.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// A monthly and a weekly budget, with the monthly one superseded from June.
/// February 2024 is a LEAP February (29 days) — the case where a naive 30-day
/// or per-day-summed denominator gives the wrong answer.
const LEDGER: &str = r#"option "operating_currency" "USD"

2024-01-01 open Expenses:Food
2024-01-01 open Expenses:Food:Restaurant
2024-01-01 open Expenses:Transport
2024-01-01 open Assets:Cash

2024-01-01 custom "budget" Expenses:Food      "monthly" 400.00 USD
2024-01-01 custom "budget" Expenses:Transport "weekly"   70.00 USD
2024-06-01 custom "budget" Expenses:Food      "monthly" 450.00 USD

2024-02-05 * "groceries"
  Expenses:Food     120.00 USD
  Assets:Cash

2024-02-14 * "dinner out"
  Expenses:Food:Restaurant  80.00 USD
  Assets:Cash

2024-02-10 * "bus pass"
  Expenses:Transport  60.00 USD
  Assets:Cash
"#;

/// A budget on `Expenses:Food` must NOT capture `Expenses:FoodCourt`, which only
/// shares a name prefix. (Fava's `startswith` test gets this wrong.)
const LEDGER_PREFIX: &str = r#"2024-01-01 open Expenses:Food
2024-01-01 open Expenses:FoodCourt
2024-01-01 open Assets:Cash

2024-01-01 custom "budget" Expenses:Food "monthly" 300.00 USD

2024-03-10 * "not a subaccount"
  Expenses:FoodCourt  99.00 USD
  Assets:Cash
"#;

fn write_fixture(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-budget-")
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
fn whole_leap_february_accrues_the_exact_monthly_amount() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
            "--format",
            "csv",
        ],
    );
    let rows: Vec<&str> = csv.lines().collect();
    assert_eq!(
        rows[0],
        "account,currency,budgeted,actual,remaining,used_pct"
    );
    // 29-day February still budgets exactly 400 — not 386.67 (400/30*29) and not
    // 399.99…97 (the residue from summing 400/29 twenty-nine times).
    // Actual excludes the 80.00 child-account dinner (exact-match default).
    assert_eq!(rows[1], "Expenses:Food,USD,400.00,120.00,280.00,30.0");
    // weekly 70 over 29 days = 29 * 10.
    assert_eq!(rows[2], "Expenses:Transport,USD,290.00,60.00,230.00,20.7");
}

#[test]
fn partial_window_prorates_by_real_calendar_days() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-02-15",
            "--format",
            "csv",
        ],
    );
    let food = csv.lines().nth(1).expect("a Food row");
    let budgeted: f64 = food.split(',').nth(2).unwrap().parse().unwrap();
    // 14 of February 2024's 29 days.
    let want = 400.0 * 14.0 / 29.0;
    assert!(
        (budgeted - want).abs() < 1e-9,
        "14/29 of the monthly budget: got {budgeted}, want {want}"
    );
}

#[test]
fn a_later_directive_supersedes_from_its_own_date() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    // May at the old rate + June at the new one.
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-05-01",
            "--to",
            "2024-07-01",
            "--format",
            "csv",
        ],
    );
    assert!(
        csv.lines()
            .nth(1)
            .is_some_and(|l| l.starts_with("Expenses:Food,USD,850.00,")),
        "400 (May) + 450 (June): {csv}"
    );
    // A whole year: Jan-May at 400, Jun-Dec at 450.
    let year = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2025-01-01",
            "--format",
            "csv",
        ],
    );
    assert!(
        year.lines()
            .nth(1)
            .is_some_and(|l| l.starts_with("Expenses:Food,USD,5150.00,")),
        "5*400 + 7*450 = 5150: {year}"
    );
}

#[test]
fn children_are_excluded_by_default_and_included_on_request() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let args = [
        "report",
        path,
        "budget",
        "--from",
        "2024-02-01",
        "--to",
        "2024-03-01",
        "--format",
        "csv",
    ];
    // Default: only Expenses:Food itself -> 120.00, not 200.00.
    let plain = run(&bin, &args);
    assert!(
        plain
            .lines()
            .nth(1)
            .is_some_and(|l| l.contains(",400.00,120.00,")),
        "child spend excluded by default: {plain}"
    );
    // --children: adds the 80.00 restaurant posting.
    let mut with_children = args.to_vec();
    with_children.push("--children");
    let kids = run(&bin, &with_children);
    assert!(
        kids.lines()
            .nth(1)
            .is_some_and(|l| l.contains(",400.00,200.00,")),
        "child spend included with --children: {kids}"
    );
}

#[test]
fn a_name_prefix_is_not_a_subaccount() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER_PREFIX);
    let path = f.path().to_str().unwrap();
    // Even with --children, Expenses:FoodCourt is a DIFFERENT account.
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-03-01",
            "--to",
            "2024-04-01",
            "--children",
            "--format",
            "csv",
        ],
    );
    let row = csv.lines().nth(1).expect("a Food row");
    let actual = row.split(',').nth(3).unwrap();
    assert_eq!(
        actual, "0",
        "Expenses:FoodCourt must not count toward Expenses:Food: {csv}"
    );
}

#[test]
fn an_invalid_interval_is_reported_not_silently_zeroed() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:X\n2024-01-01 custom \"budget\" Expenses:X \"fortnightly\" 10.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
        ])
        .output()
        .expect("run");
    assert!(
        out.status.success(),
        "a bad interval warns, it does not abort"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("invalid interval") && stderr.contains("fortnightly"),
        "the skipped directive is named: {stderr}"
    );
}

#[test]
fn json_carries_the_window_and_one_object_per_budget() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let json = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
            "--format",
            "json",
        ],
    );
    let v: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert_eq!(v["from"], "2024-02-01");
    assert_eq!(v["to"], "2024-03-01");
    let budgets = v["budgets"].as_array().expect("an array");
    assert_eq!(budgets.len(), 2);
    assert_eq!(budgets[0]["account"], "Expenses:Food");
    assert_eq!(budgets[0]["budgeted"], "400.00");
    assert_eq!(budgets[0]["actual"], "120.00");
    assert_eq!(budgets[0]["remaining"], "280.00");
}

#[test]
fn an_inverted_window_is_rejected() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-06-01",
            "--to",
            "2024-01-01",
        ])
        .output()
        .expect("run");
    assert!(!out.status.success(), "an empty window must error");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("after"),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// An earning target on a credit-normal account compares in the same direction as
/// a spending budget: earning exactly the target is 100% used with nothing
/// remaining — NOT `actual -5000, remaining 10000, used -100%`, which is what a
/// raw (unnormalized) posting sum produces for income.
#[test]
fn income_budgets_compare_in_the_right_direction() {
    let bin = require_rledger!();
    let f = write_fixture(
        r#"2024-01-01 open Income:Salary
2024-01-01 open Assets:Cash

2024-01-01 custom "budget" Income:Salary "monthly" 5000.00 USD

2024-03-05 * "paycheck"
  Assets:Cash     5000.00 USD
  Income:Salary
"#,
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-03-01",
            "--to",
            "2024-04-01",
            "--format",
            "csv",
        ],
    );
    assert_eq!(
        csv.lines().nth(1).expect("a row"),
        "Income:Salary,USD,5000.00,5000.00,0.00,100.0"
    );
}

/// Under `--children`, a parent row and a child row BOTH include the child, so the
/// TOTAL must be derived from the underlying budgets and postings rather than by
/// summing the rendered rows — otherwise the child is counted twice.
#[test]
fn children_totals_do_not_double_count_the_child() {
    let bin = require_rledger!();
    let f = write_fixture(
        r#"2024-01-01 open Expenses:Food
2024-01-01 open Expenses:Food:Restaurant
2024-01-01 open Assets:Cash

2024-01-01 custom "budget" Expenses:Food            "monthly" 300.00 USD
2024-01-01 custom "budget" Expenses:Food:Restaurant "monthly" 100.00 USD

2024-03-05 * "restaurant spend"
  Expenses:Food:Restaurant  50.00 USD
  Assets:Cash
"#,
    );
    let path = f.path().to_str().unwrap();
    let txt = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-03-01",
            "--to",
            "2024-04-01",
            "--children",
            "--no-pager",
        ],
    );
    // Rows overlap by design (the parent row includes its child).
    assert!(
        txt.contains("Expenses:Food                        400.00        50.00"),
        "{txt}"
    );
    assert!(
        txt.contains("Expenses:Food:Restaurant             100.00        50.00"),
        "{txt}"
    );
    // The TOTAL counts each budget and each posting once: 300+100 and one 50.
    let total = txt
        .lines()
        .find(|l| l.starts_with("TOTAL"))
        .expect("a TOTAL line");
    assert!(
        total.contains("400.00") && total.contains("50.00"),
        "TOTAL must not double-count the child (would be 500.00/100.00): {total}"
    );
}
