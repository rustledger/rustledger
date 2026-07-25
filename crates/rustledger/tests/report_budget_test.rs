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
    let budgeted = food.split(',').nth(2).unwrap();
    // 14 of February 2024's 29 days: 400 x 14/29 = 193.1034..., rendered at the
    // ledger's USD precision like every other report's CSV (the U4 invariant).
    // The exact unrounded accrual is pinned in `budget::tests`; what this asserts
    // is that the denominator really is February's 29 days and not 28 or 30.
    assert_eq!(budgeted, "193.10", "14/29 of the monthly budget: {csv}");
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
        actual, "0.00",
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
        String::from_utf8_lossy(&out.stderr).contains("the window is empty"),
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
    // Rows overlap by design (the parent row includes its child). Assert on the
    // fields, not on column positions: the currency column is sized to the widest
    // commodity present, so a literal-spacing match breaks on unrelated changes
    // while still not pinning the numbers.
    let fields = |prefix: &str| -> Vec<String> {
        txt.lines()
            .find(|l| l.starts_with(prefix))
            .unwrap_or_else(|| panic!("a {prefix} row in:\n{txt}"))
            .split_whitespace()
            .map(str::to_string)
            .collect()
    };
    assert_eq!(
        fields("Expenses:Food "),
        vec!["Expenses:Food", "USD", "400.00", "50.00", "350.00", "12.5%"]
    );
    assert_eq!(
        fields("Expenses:Food:Restaurant"),
        vec![
            "Expenses:Food:Restaurant",
            "USD",
            "100.00",
            "50.00",
            "50.00",
            "50.0%"
        ]
    );
    // The TOTAL counts each budget and each posting once: 300+100 and one 50.
    // Assert the WHOLE line, not substrings: with a wrong budgeted total of
    // 450.00 the line reads `TOTAL USD 450.00 50.00 400.00 11.1%`, and a
    // `contains("400.00")` guard is satisfied by the Remaining column — a guard
    // the divergence cannot trip is decoration.
    let total = txt
        .lines()
        .find(|l| l.starts_with("TOTAL"))
        .expect("a TOTAL line");
    assert_eq!(
        total.split_whitespace().collect::<Vec<_>>(),
        vec!["TOTAL", "USD", "400.00", "50.00", "350.00", "12.5%"],
        "TOTAL must not double-count the child (would be 500.00/100.00)"
    );
}

/// A budget amount large enough that `amount × days` overflows `Decimal` must
/// not panic: budget amounts come from the ledger, and ledger input never aborts
/// the CLI. The multiply-before-divide accrual (which keeps a whole interval
/// exact) falls back to divide-first here.
#[test]
fn an_enormous_budget_amount_does_not_panic() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Big\n\
         2024-01-01 custom \"budget\" Expenses:Big \"monthly\" 79228162514264337593543950335 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-02-15",
            "--format",
            "csv",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    assert!(
        out.status.success(),
        "an out-of-range budget amount must warn or degrade, not abort: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// Spending booked in another currency with a price still counts against a
/// budget denominated in the price currency. Keying purely on the posting's
/// units currency made foreign spending vanish from the report entirely.
#[test]
fn foreign_currency_spending_counts_against_the_budgeted_currency() {
    let bin = require_rledger!();
    let f = write_fixture(
        "option \"operating_currency\" \"USD\"\n\
         2024-01-01 open Expenses:Travel\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Travel \"monthly\" 500.00 USD\n\
         2024-02-10 * \"hotel\"\n  \
           Expenses:Travel  100.00 EUR @ 1.10 USD\n  \
           Assets:Cash     -110.00 USD\n",
    );
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
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("Expenses:Travel,USD,500.00,110.00,390.00,22.0"),
        "the 110 USD the hotel really cost must count against the USD budget: {csv}"
    );
}

/// Pad-synthesized postings are spending like any other. Reading the
/// source-faithful stream made the budget report disagree with `balances` and
/// `income` on the very same ledger.
#[test]
fn pad_synthesized_postings_count_as_spending() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2026-01-01 open Expenses:Food\n\
         2026-01-01 open Assets:Cash\n\
         2026-01-01 open Equity:Void\n\
         2026-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2026-06-01 * \"expense\"\n  Expenses:Food   10.00 USD\n  Assets:Cash    -10.00 USD\n\
         2026-06-05 pad Expenses:Food Equity:Void\n\
         2026-06-06 balance Expenses:Food 200 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2026-06-01",
            "--to",
            "2026-07-01",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("Expenses:Food,USD,400.00,200.00,200.00,50.0"),
        "the pad-realized 190 must count, matching `report balances`: {csv}"
    );
}

/// Fava's reader is duck-typed, so real ledgers write the account as a quoted
/// string as well as a bare token. Rejecting the quoted form would drop budgets
/// from a ledger Fava renders fine.
#[test]
fn a_quoted_account_is_accepted_like_fava() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Travel\n\
         2024-01-01 custom \"budget\" \"Expenses:Travel\" \"monthly\" 100.00 USD\n",
    );
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
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("Expenses:Travel,USD,100.00"),
        "the quoted-account spelling must parse: {csv}"
    );
}

/// A budget written today does not apply retroactively to a period before it
/// existed. Emitting a row anyway reported the whole earlier window as overspend
/// against a `0.00` budget.
#[test]
fn a_budget_does_not_apply_before_it_was_declared() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 open Assets:Cash\n\
         2023-06-01 * \"food last year\"\n  \
           Expenses:Food   5200.00 USD\n  Assets:Cash    -5200.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2023-01-01",
            "--to",
            "2024-01-01",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    assert!(
        !csv.contains("Expenses:Food"),
        "no budget existed in 2023, so there is no budget row to report: {csv}"
    );
}

/// A currency the ledger never posts in has no display convention to infer, so
/// a pro-rated (repeating) figure is rounded for display rather than printed to
/// 28 digits. It is deliberately NOT rounded to the declared amount's scale:
/// that scale is a stylistic choice about the declaration, and using it rounded
/// a 0.22580645 BTC accrual to `0.2`.
#[test]
fn a_budget_only_currency_is_rounded_for_display() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let txt = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-01-20",
            "--no-pager",
        ],
    );
    assert!(txt.contains("245.16129032"), "rounded to 8 dp: {txt}");
    assert!(
        !txt.contains("245.1612903225"),
        "the raw 28-digit decimal must not reach the report: {txt}"
    );
}

/// Machine output carries the same numbers the text report shows (the U4
/// display-context invariant), including a TOTAL row consumers cannot re-derive
/// by summing rows.
#[test]
fn csv_uses_display_precision_and_carries_a_total() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-01-20",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("Expenses:Food,USD,245.16129032,0,245.16129032,0.0"),
        "{csv}"
    );
    assert!(csv.contains("TOTAL,USD,245.16129032"), "{csv}");
}

/// Two currencies on one account must be distinguishable in the default output.
#[test]
fn text_output_names_the_currency_of_each_row() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 100.00 EUR\n",
    );
    let path = f.path().to_str().unwrap();
    let txt = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
            "--no-pager",
        ],
    );
    // Each row names its own currency, and the two rows carry DIFFERENT figures —
    // a `contains` on the label alone would pass even if both rows showed the
    // same numbers, which is the ambiguity this column exists to remove.
    let row = |ccy: &str| -> Vec<String> {
        txt.lines()
            .find(|l| l.starts_with("Expenses:Food ") && l.contains(ccy))
            .unwrap_or_else(|| panic!("a {ccy} row in:\n{txt}"))
            .split_whitespace()
            .map(str::to_string)
            .collect()
    };
    assert_eq!(row("EUR")[1], "EUR");
    assert_eq!(row("USD")[1], "USD");
    assert_ne!(
        row("EUR")[2],
        row("USD")[2],
        "the two currencies' budgeted figures must be distinguishable: {txt}"
    );
}

/// An `--account` filter that excludes everything must not claim the ledger has
/// no budgets — that sends the user hunting a parsing bug that isn't there.
#[test]
fn an_empty_result_says_which_reason_applies() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let filtered = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
            "--account",
            "Expenses:Nonexistent",
            "--no-pager",
        ],
    );
    assert!(
        filtered.contains("No budgets match --account"),
        "{filtered}"
    );
    assert!(!filtered.contains("No budgets declared"), "{filtered}");

    let before = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2023-01-01",
            "--to",
            "2024-01-01",
            "--no-pager",
        ],
    );
    assert!(
        before.contains("No budgets were in force in this period"),
        "{before}"
    );
}

/// A budget naming an account the ledger never opens is almost always a typo,
/// and renders as a real row at 0% used while the true spending sits elsewhere.
#[test]
fn a_budget_on_an_unopened_account_warns() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Foood \"monthly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("Expenses:Foood") && stderr.contains("no such account is opened"),
        "a typo'd budget account must be reported: {stderr}"
    );
}

/// Spending from before the budget was declared must not be charged against it.
/// `accrue` already refuses to credit a budget before its own date; summing the
/// whole window on the actual side reported someone exactly on budget as 400%
/// used — on the DEFAULT year-to-date window.
#[test]
fn spending_before_the_budget_existed_is_not_charged_to_it() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 open Assets:Cash\n\
         2024-06-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2024-01-15 * \"a\"\n  Expenses:Food 400.00 USD\n  Assets:Cash\n\
         2024-02-15 * \"b\"\n  Expenses:Food 400.00 USD\n  Assets:Cash\n\
         2024-03-15 * \"c\"\n  Expenses:Food 400.00 USD\n  Assets:Cash\n\
         2024-06-15 * \"d\"\n  Expenses:Food 400.00 USD\n  Assets:Cash\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-07-01",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("Expenses:Food,USD,400.00,400.00,0.00,100.0"),
        "June's budget is compared with June's spending, not the whole year's: {csv}"
    );
}

/// A budget declared for one account must not change how another account's
/// spending is counted. Choosing the counted currency from a ledger-global set of
/// budgeted currencies made adding an unrelated budget zero an existing row.
#[test]
fn an_unrelated_budget_does_not_move_another_accounts_spend() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Travel\n\
         2024-01-01 open Expenses:Groceries\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Travel \"monthly\" 1000.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Groceries \"monthly\" 300.00 EUR\n\
         2024-01-10 * \"flight\"\n  \
           Expenses:Travel  500.00 EUR @ 1.10 USD\n  Assets:Cash     -550.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("Expenses:Travel,USD,1000.00,550.00,450.00,55.0"),
        "the 550 USD flight counts against the USD travel budget: {csv}"
    );
}

/// A budget account is written as a quoted string in some Fava ledgers, so it can
/// carry arbitrary text — including a newline, which would split the fixed-width
/// text row and forge an extra table line (a fake TOTAL).
#[test]
fn a_quoted_account_cannot_forge_a_table_row() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" \"Expenses:Food\nTOTAL      USD  999.00\" \"monthly\" 400.00 USD\n",
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
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        !text.contains("999.00"),
        "a newline in a quoted account must not produce a forged row: {text}"
    );
}

/// Two accounts sharing a long prefix must stay distinguishable: truncating the
/// tail rendered both as `Expenses:Home:Improvements:…`.
#[test]
fn long_account_names_stay_distinguishable() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Home:Improvements:Kitchen\n\
         2024-01-01 open Expenses:Home:Improvements:Bathroom\n\
         2024-01-01 custom \"budget\" Expenses:Home:Improvements:Kitchen \"monthly\" 100.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Home:Improvements:Bathroom \"monthly\" 200.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let txt = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
            "--no-pager",
        ],
    );
    assert!(txt.contains("Kitchen"), "{txt}");
    assert!(txt.contains("Bathroom"), "{txt}");
}

/// `--to` is exclusive, so `--from X --to X` is an empty window. Rendering it
/// produced a table of authoritative all-zero rows.
#[test]
fn an_empty_window_is_rejected_not_rendered_as_zeros() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-03-05",
            "--to",
            "2024-03-05",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    assert!(!out.status.success(), "an empty window must be an error");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("EXCLUSIVE"),
        "the error should explain the exclusive end"
    );
}

/// A budget whose currency the account never posts in is a typo, and rendered a
/// tidy 0%-used row while the real spending sat one keystroke away.
#[test]
fn a_budget_in_a_currency_the_account_never_posts_warns() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Assets:Cash\n\
         2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USF\n\
         2024-03-05 * \"groceries\"\n  Expenses:Food 380.00 USD\n  Assets:Cash\n",
    );
    let path = f.path().to_str().unwrap();
    let out = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-03-01",
            "--to",
            "2024-04-01",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("USF") && stderr.contains("only posts USD"),
        "a currency typo must be reported: {stderr}"
    );
}

/// An accrual too large to represent is reported as `n/a`, never as a clamped
/// number: saturating made a one-month and a two-month window print the same
/// figure, each looking authoritative.
#[test]
fn an_unrepresentable_accrual_reports_na_not_a_clamped_number() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 79228162514264337593543950335 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-03-01",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    // Machine output reports an absent number the way the other reports do — an
    // empty CSV cell and a JSON `null` — so a consumer parsing decimals is never
    // handed the literal "n/a". Only the text report says `n/a`.
    assert!(
        csv.contains("Expenses:Food,USD,,"),
        "two months of a MAX budget is not representable: {csv}"
    );
    let json = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-03-01",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    assert!(json.contains(r#""budgeted": null"#), "{json}");
    let txt = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-03-01",
            "--no-pager",
        ],
    );
    assert!(txt.contains("n/a"), "{txt}");
}

/// Machine consumers must be able to tell "no budgets" from "all budgets
/// rejected" — both produced an empty `budgets` array and exit 0.
#[test]
fn json_reports_rejected_directives_in_band() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"fortnightly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let json = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    assert!(json.contains("\"errors\""), "{json}");
    assert!(
        json.contains("fortnightly"),
        "the rejected directive is named: {json}"
    );
}

/// Under `--children` a row covers budgets with DIFFERENT declaration dates. The
/// clip that excludes pre-budget spending must be applied per posting-account, or
/// an early child budget drags the parent's window backwards and charges the
/// parent row with spending that predates the parent's own budget — while the
/// TOTAL, which had the rule written the other way, disagrees.
#[test]
fn a_child_budget_does_not_drag_the_parents_clip_window_backwards() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 open Expenses:Food:Restaurant\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Food:Restaurant \"monthly\" 100.00 USD\n\
         2024-06-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2024-02-15 * \"groceries on the parent, before the parent budget exists\"\n  \
           Expenses:Food   50.00 USD\n  Assets:Cash    -50.00 USD\n\
         2024-07-20 * \"restaurant, after both budgets exist\"\n  \
           Expenses:Food:Restaurant  30.00 USD\n  Assets:Cash              -30.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--children",
            "--from",
            "2024-01-01",
            "--to",
            "2024-12-31",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    let parent = csv
        .lines()
        .find(|l| l.starts_with("Expenses:Food,"))
        .expect("a parent row");
    let total = csv
        .lines()
        .find(|l| l.starts_with("TOTAL,"))
        .expect("a TOTAL row");
    let parent_actual = parent.split(',').nth(3).unwrap();
    let total_actual = total.split(',').nth(3).unwrap();
    // The Feb 50.00 predates the parent's June budget and must be excluded; the
    // Jul 30.00 postdates both and must be counted. Asserting a NON-ZERO figure
    // matters: comparing 0.00 to 0.00 would also be satisfied by a rule that
    // clipped rows and totals identically-wrongly.
    assert_eq!(
        parent_actual, "30.00",
        "excludes the pre-budget Feb spend, includes the Jul spend: {csv}"
    );
    assert_eq!(
        parent_actual, total_actual,
        "the row and the TOTAL must agree on actual: {csv}"
    );
}

/// A second amount on one directive is a user declaring two budgets on one line.
/// Silently keeping the first drops the other with no diagnostic anywhere; a
/// trailing NOTE, which Fava allows, must still parse.
#[test]
fn a_second_amount_is_reported_but_a_trailing_note_is_not() {
    let bin = require_rledger!();
    let two = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD 300.00 EUR\n",
    );
    let out = Command::new(&bin)
        .args([
            "report",
            two.path().to_str().unwrap(),
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("malformed budget directive"),
        "two amounts on one line must be reported, not half-parsed"
    );

    let note = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD \"groceries only\"\n",
    );
    let csv = run(
        &bin,
        &[
            "report",
            note.path().to_str().unwrap(),
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    assert!(csv.contains("Expenses:Food,USD,400.00"), "{csv}");
}

/// A commodity name longer than the default column must widen the column rather
/// than be truncated: truncating re-creates the misattribution bug the currency
/// column was added to fix, since two 24-character commodities can share a
/// suffix. Columns must stay aligned and both names must appear in full.
#[test]
fn a_long_commodity_name_keeps_the_columns_aligned() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 300.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 300.00 VACATION-FUND\n",
    );
    let path = f.path().to_str().unwrap();
    let txt = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-04-01",
            "--no-pager",
        ],
    );
    let rows: Vec<&str> = txt
        .lines()
        .filter(|l| l.starts_with("Expenses:Food "))
        .collect();
    assert_eq!(rows.len(), 2, "{txt}");
    assert!(
        txt.contains("VACATION-FUND"),
        "the full commodity name: {txt}"
    );
    // Compare CHARACTER offsets: the truncation marker `…` is three bytes, so a
    // byte index differs between the rows even when the columns line up.
    let col = |l: &str| {
        l.chars()
            .collect::<Vec<_>>()
            .windows(6)
            .position(|w| w.iter().collect::<String>() == "900.00")
            .expect("a budgeted figure")
    };
    assert_eq!(
        col(rows[0]),
        col(rows[1]),
        "both rows put Budgeted in the same column: {txt}"
    );
}

/// Narrowing to one account must not emit warnings about accounts the user
/// explicitly excluded — they belong to a report the user did not ask for.
#[test]
fn warnings_respect_the_account_filter() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Typo \"monthly\" 100.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let filtered = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
            "--account",
            "Expenses:Food",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    assert!(
        !String::from_utf8_lossy(&filtered.stderr).contains("Expenses:Typo"),
        "an excluded account must not warn: {}",
        String::from_utf8_lossy(&filtered.stderr)
    );
    let unfiltered = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
            "--no-pager",
        ])
        .output()
        .expect("run rledger");
    assert!(
        String::from_utf8_lossy(&unfiltered.stderr).contains("Expenses:Typo"),
        "without the filter it still warns"
    );
}

/// An integer `custom "budget"` amount must not pin a whole currency to 0 dp: a
/// pro-rated figure then renders as a whole token (0.5172 BTC as `1`).
#[test]
fn an_integer_budget_amount_does_not_pin_the_currency_to_zero_dp() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Crypto\n\
         2024-01-01 custom \"budget\" Expenses:Crypto \"monthly\" 1 BTC\n",
    );
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
            "2024-02-16",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    // Assert the EXACT field. `contains("...,0.5")` is satisfied both by the
    // correct value and by the 28-digit `0.5172413793103448275862068966` that a
    // previous attempt produced — a guard the regression can satisfy is not one.
    let budgeted = csv
        .lines()
        .nth(1)
        .expect("a row")
        .split(',')
        .nth(2)
        .expect("the budgeted field")
        .to_string();
    assert_eq!(
        budgeted, "0.51724138",
        "15/29 of 1 BTC, rounded for display and not pinned to the declared \
         integer's scale: {csv}"
    );
}

/// A yearly budget near the end of the representable date range must not
/// accrue a full year's amount per day. The period's next start does not
/// exist there; saturating made the interval look one day long.
#[test]
fn a_period_past_the_representable_range_is_not_treated_as_one_day() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"yearly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "9999-01-01",
            "--to",
            "9999-12-31",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    assert!(
        !csv.contains("145600"),
        "a 400/yr budget must not accrue ~364x: {csv}"
    );
}

/// A posting whose canonical weight differs from its units in NUMBER but not
/// currency (`90.00 USD @@ 95.00 USD`) spends the weight. Recording the units
/// made the report disagree with BQL's `weight` column on the same posting.
#[test]
fn a_same_currency_weight_is_what_counts_as_spent() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Fees\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Fees \"monthly\" 400.00 USD\n\
         2024-02-10 * \"fee\"\n  \
           Expenses:Fees  90.00 USD @@ 95.00 USD\n  Assets:Cash   -95.00 USD\n",
    );
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
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("Expenses:Fees,USD,400.00,95.00,305.00,23.8"),
        "the posting moved 95.00, which is what BQL `weight` reports: {csv}"
    );
}

/// An earning target and a spending budget must not be added together: the sum
/// is meaningless and its `Used` percentage reads far healthier than the
/// spending actually is.
#[test]
fn income_and_expense_budgets_total_separately() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Travel\n\
         2024-01-01 open Income:Salary\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Travel \"monthly\" 400.00 USD\n\
         2024-01-01 custom \"budget\" Income:Salary \"monthly\" 5000.00 USD\n\
         2024-02-05 * \"trip\"\n  Expenses:Travel  99.00 USD\n  Assets:Cash\n\
         2024-02-06 * \"pay\"\n  Assets:Cash  5000.00 USD\n  Income:Salary\n",
    );
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
            "--no-pager",
        ],
    );
    assert!(
        csv.contains("TOTAL,USD,400.00,99.00,301.00,24.8"),
        "the spending total covers only spending budgets: {csv}"
    );
    assert!(
        csv.contains("TOTAL (earned),USD,5000.00,5000.00,0.00,100.0"),
        "the earning target totals separately: {csv}"
    );
    assert!(
        !csv.contains("5400.00"),
        "the two must never be summed: {csv}"
    );
}

/// The unopened-account warning is exempted for an aggregate parent budget only
/// under `--children`, which is what makes the children answer it. In the
/// default mode that budget really does report nothing.
#[test]
fn an_aggregate_parent_budget_warns_only_when_children_are_not_counted() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food:Groceries\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2024-02-05 * \"g\"\n  Expenses:Food:Groceries 120.00 USD\n  Assets:Cash\n",
    );
    let path = f.path().to_str().unwrap();
    let args = [
        "report",
        path,
        "budget",
        "--from",
        "2024-02-01",
        "--to",
        "2024-03-01",
        "--no-pager",
    ];
    let default_mode = Command::new(&bin).args(args).output().expect("run");
    assert!(
        String::from_utf8_lossy(&default_mode.stderr).contains("no such account is opened"),
        "without --children the budget reports nothing, so it must warn"
    );
    let mut with_children = args.to_vec();
    with_children.push("--children");
    let kids = Command::new(&bin)
        .args(&with_children)
        .output()
        .expect("run");
    assert!(
        !String::from_utf8_lossy(&kids.stderr).contains("no such account is opened"),
        "with --children it works, so it must not warn"
    );
}

/// `--account` narrows which warnings are shown, but must not change the
/// diagnosis of an empty report: a ledger whose budgets were all rejected is
/// not a ledger with no budgets.
#[test]
fn an_account_filter_does_not_turn_rejected_budgets_into_none_declared() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"fortnightly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let txt = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
            "--account",
            "Assets",
            "--no-pager",
        ],
    );
    assert!(txt.contains("every `custom \"budget\"` directive"), "{txt}");
    assert!(!txt.contains("No budgets declared"), "{txt}");
}

/// Under `--children` a row is live when a budget it COVERS is live, which is
/// not the same as the account's own declarations being live. A parent whose
/// own budget starts next year still aggregates a child budget running now, and
/// dropping that row lost the aggregate the flag exists to provide.
///
/// Found by `scripts/compat-budget-fuzz.py`, not by hand: it needs a parent and
/// a child budget in one currency with declaration dates straddling the window.
#[test]
fn a_parent_row_survives_when_only_a_child_budget_is_live() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2019-01-01 open Expenses:Food\n\
         2019-01-01 open Expenses:Food:Grocery\n\
         2021-05-18 custom \"budget\" Expenses:Food:Grocery \"daily\" 614.77 GBP\n\
         2022-05-22 custom \"budget\" Expenses:Food \"monthly\" 4274.21 GBP\n",
    );
    let path = f.path().to_str().unwrap();
    let csv = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--children",
            "--from",
            "2021-10-17",
            "--to",
            "2021-10-24",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    // 7 days x 614.77, aggregated onto the parent even though the parent's own
    // GBP budget does not start until 2022.
    assert!(
        csv.contains("Expenses:Food,GBP,4303.39"),
        "the parent row must aggregate the live child budget: {csv}"
    );
    assert!(csv.contains("Expenses:Food:Grocery,GBP,4303.39"), "{csv}");
}
