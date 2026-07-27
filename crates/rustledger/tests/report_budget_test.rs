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
        csv.contains("Expenses:Food,USD,245.16129032,0.00000000,245.16129032,0.0"),
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
    // Reported AND read. Fava takes the first three values and ignores the
    // rest, so this really is a 400/month budget there; discarding it would
    // cost a migrating user the budget and — since only budgeted accounts get
    // rows — the account's entire line. The warning is the whole remedy.
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("carries a second figure"),
        "a second figure must be reported: {stderr}"
    );
    let kept = run(
        &bin,
        &[
            "report",
            two.path().to_str().unwrap(),
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
        kept.lines()
            .any(|l| l.starts_with("Expenses:Food,USD,400.00")),
        "...and the first figure is still the budget: {kept}"
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
    // Asserted as a VALUE, not as the absence of one wrong number. The
    // predecessor of this assertion was `!csv.contains("145600")`, which the
    // silently-zero output satisfied just as well as the correct one — it could
    // not fail on the defect it was written for. 400/yr over 364 of 365 days is
    // 398.90410958904109589041095890.
    let row = csv
        .lines()
        .find(|l| l.starts_with("Expenses:Food,"))
        .unwrap_or_else(|| panic!("no Expenses:Food row: {csv}"));
    let budgeted: f64 = row
        .split(',')
        .nth(2)
        .expect("budgeted column")
        .parse()
        .expect("a numeric budgeted figure");
    assert!(
        (budgeted - 398.904_109_6).abs() < 1e-6,
        "a 400/yr budget over the final calendar year must accrue its pro-rata \
         share (~398.90), not 145600 (a 364x inflation) and not 0.00 (the \
         period dropped): {csv}"
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
        csv.contains("TOTAL (Income),USD,5000.00,5000.00,0.00,100.0"),
        "the income target totals separately, under its own account type: {csv}"
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

/// The empty-report diagnosis must be made over the budgets the user asked
/// about. Testing "is anything in force" across the whole ledger let an
/// unrelated account's live budget mask the real reason, so a report filtered
/// to an account whose budget starts later blamed the `--account` prefix and
/// sent the user to debug a name that was in fact matching.
#[test]
fn an_empty_filtered_report_diagnoses_the_filtered_accounts() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Rent\n\
         2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Rent \"monthly\" 1000.00 USD\n\
         2026-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let starts_later = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--account",
            "Expenses:Food",
            "--from",
            "2024-01-01",
            "--to",
            "2025-01-01",
            "--no-pager",
        ],
    );
    assert!(
        starts_later.contains("No budgets were in force in this period")
            && starts_later.contains("2026-01-01"),
        "the budget starts later; the prefix is not the problem: {starts_later}"
    );

    // A filter that genuinely matches nothing still says so.
    let no_match = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--account",
            "Expenses:Zzz",
            "--from",
            "2024-01-01",
            "--to",
            "2025-01-01",
            "--no-pager",
        ],
    );
    assert!(
        no_match.contains("No budgets match --account"),
        "{no_match}"
    );
}

/// Every text column is sized to its content. A fixed width either truncates
/// (so two distinct values render identically and their figures are
/// misattributed) or lets a wide cell fuse with its neighbor (so the reader
/// cannot tell where Actual ends and Remaining begins). Both were shipped here
/// before this was applied uniformly.
#[test]
fn text_columns_never_truncate_or_fuse() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:AlphaDivision:Operations:Facilities:Utilities\n\
         2024-01-01 open Expenses:BetaDivision:Operations:Facilities:Utilities\n\
         2020-01-01 open Expenses:Mining\n\
         2024-01-01 custom \"budget\" Expenses:AlphaDivision:Operations:Facilities:Utilities \"monthly\" 100.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:BetaDivision:Operations:Facilities:Utilities \"monthly\" 900.00 USD\n\
         2020-01-01 custom \"budget\" Expenses:Mining \"monthly\" 12345.50000000 BTC\n",
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
    // Both long accounts appear in full, so their figures are attributable.
    assert!(
        txt.contains("Expenses:AlphaDivision:Operations:Facilities:Utilities"),
        "{txt}"
    );
    assert!(
        txt.contains("Expenses:BetaDivision:Operations:Facilities:Utilities"),
        "{txt}"
    );
    // Every data row splits into exactly the six columns; a fused cell would
    // yield fewer fields.
    for l in txt
        .lines()
        .filter(|l| l.starts_with("Expenses:") || l.starts_with("TOTAL"))
    {
        assert_eq!(
            l.split_whitespace().count(),
            6,
            "row must have six separable columns: {l:?}"
        );
    }
}

/// The four numeric fields of a row must be mutually consistent. Computing the
/// percentage from unrounded figures while showing rounded ones printed
/// `budgeted 0, actual 0, remaining 0, used_pct 2033.3`.
#[test]
fn a_rows_fields_agree_with_each_other() {
    let bin = require_rledger!();
    let f = write_fixture(
        "option \"display_precision\" \"USD:1\"\n\
         2024-01-01 open Expenses:Tiny\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Tiny \"yearly\" 0.02 USD\n\
         2024-01-02 * \"t\"\n  Expenses:Tiny 0.01 USD\n  Assets:Cash\n",
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
            "2024-01-10",
            "--format",
            "csv",
            "--no-pager",
        ],
    );
    let row = csv.lines().nth(1).expect("a row");
    let f: Vec<&str> = row.split(',').collect();
    assert_eq!(f[2], "0", "budgeted rounds to zero: {row}");
    assert_eq!(
        f[5], "",
        "a percentage of a zero budget is undefined, not a finite number: {row}"
    );
}

/// `--account` is user input echoed into a fixed-width table that does no
/// quoting of its own, so it must be sanitized like any other label.
#[test]
fn the_account_filter_echo_cannot_forge_a_row() {
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
            "2024-04-01",
            "--account",
            "Zzz\n2024-01-01 TOTAL   USD  9999",
            "--no-pager",
        ],
    );
    assert!(
        !txt.lines()
            .any(|l| l.trim_start().starts_with("2024-01-01 TOTAL")),
        "a newline in --account must not produce a forged line: {txt}"
    );
}

/// The `Used` column must be sized to its content like the others. It was the
/// one left at a constant, so an overspent placeholder budget rendered
/// `-4999.00500000.0%` and the reader could read the remaining figure as
/// `-4999.00500000`.
#[test]
fn a_wide_percentage_does_not_fuse_with_remaining() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Misc\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Misc \"monthly\" 1.00 USD\n\
         2024-02-05 * \"big\"\n  Expenses:Misc 5000.00 USD\n  Assets:Cash\n",
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
    let row = txt
        .lines()
        .find(|l| l.starts_with("Expenses:Misc"))
        .expect("a row");
    assert_eq!(
        row.split_whitespace().count(),
        6,
        "Remaining and Used must stay separable: {row:?}"
    );
}

/// A TOTAL can overflow even when every row it sums is representable, so the
/// in-band error must cover totals too — otherwise a consumer sees a null total
/// with an empty `errors` array and cannot tell an overflow from its own bug.
#[test]
fn an_unrepresentable_total_is_reported_in_band() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:A\n\
         2024-01-01 open Expenses:B\n\
         2024-01-01 custom \"budget\" Expenses:A \"yearly\" 50000000000000000000000000000 USD\n\
         2024-01-01 custom \"budget\" Expenses:B \"yearly\" 50000000000000000000000000000 USD\n",
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
            "2025-01-01",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    assert!(json.contains(r#""budgeted": null"#), "{json}");
    assert!(
        json.contains("too large to represent"),
        "the null total must be explained in `errors`: {json}"
    );
}

/// `close` means no further postings are possible, so a budget still accruing
/// past it contributes amounts nothing can ever be spent against and the row
/// reads as a large underspend. The accrual is deliberately unchanged — a
/// budget is a declaration in its own right, and Fava does not consider `close`
/// either — but the report says so.
#[test]
fn a_budget_accruing_past_a_close_is_reported() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Sub\n\
         2024-01-01 open Assets:Cash\n\
         2024-01-01 custom \"budget\" Expenses:Sub \"monthly\" 300.00 USD\n\
         2024-01-10 * \"spend\"\n  Expenses:Sub  100.00 USD\n  Assets:Cash\n\
         2024-02-01 close Expenses:Sub\n",
    );
    let path = f.path().to_str().unwrap();
    let past = Command::new(&bin)
        .args([
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-04-01",
            "--no-pager",
        ])
        .output()
        .expect("run");
    assert!(
        String::from_utf8_lossy(&past.stderr).contains("after the account was closed"),
        "a budget running past the close must be reported: {}",
        String::from_utf8_lossy(&past.stderr)
    );

    // A window that ends at the close is unremarkable and must stay quiet.
    let upto = Command::new(&bin)
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
        .expect("run");
    assert!(
        !String::from_utf8_lossy(&upto.stderr).contains("after the account was closed"),
        "no warning when the window ends at the close"
    );
}

/// A budget declared AFTER its account was closed can never see a single
/// posting — strictly worse than one that merely runs past the close — and an
/// earlier guard excluded exactly that case from the warning.
#[test]
fn a_budget_declared_after_a_close_is_reported() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Old\n\
         2024-03-01 close Expenses:Old\n\
         2024-04-01 custom \"budget\" Expenses:Old \"monthly\" 400.00 USD\n",
    );
    let out = Command::new(&bin)
        .args([
            "report",
            f.path().to_str().unwrap(),
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-07-01",
            "--no-pager",
        ])
        .output()
        .expect("run");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("no spending can ever be booked"),
        "a budget starting after the close must be reported: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// stderr and the JSON `errors` array must report the same set. The
/// un-representable-figure errors are discovered only once rows and totals
/// exist, and emitting warnings before that sent them to JSON alone — so a text
/// or CSV user saw `n/a` cells with nothing explaining them.
#[test]
fn an_overflow_is_explained_on_stderr_not_only_in_json() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 79228162514264337593543950335 USD\n",
    );
    let path = f.path().to_str().unwrap();
    for fmt in ["text", "csv"] {
        let out = Command::new(&bin)
            .args([
                "report",
                path,
                "budget",
                "--from",
                "2024-01-01",
                "--to",
                "2024-06-01",
                "--format",
                fmt,
                "--no-pager",
            ])
            .output()
            .expect("run");
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("too large to represent"),
            "{fmt} output must explain its n/a cells on stderr"
        );
    }
}

/// "See the warnings above" must not be printed when `--account` filtered every
/// warning away, leaving the user hunting for diagnostics that are not there.
#[test]
fn an_all_rejected_report_does_not_promise_absent_warnings() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 custom \"budget\" Expenses:Food \"fortnightly\" 400.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let filtered = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-06-01",
            "--account",
            "Expenses:Zzz",
            "--no-pager",
        ],
    );
    assert!(filtered.contains("Re-run without --account"), "{filtered}");
    assert!(!filtered.contains("warnings above"), "{filtered}");

    let unfiltered = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-06-01",
            "--no-pager",
        ],
    );
    // Says that each rejection IS reported, without promising WHERE. Warnings
    // go to stderr, which a terminal shows above this line but the `ag-rledger`
    // JSON envelope discards — the old "see the warnings above" pointed an
    // agent at something its transport had already dropped.
    assert!(unfiltered.contains("reported as a warning"), "{unfiltered}");
}

/// Coverage, not identity: under `--children` a parent budget is answered by its
/// children, so a parent whose covering accounts are all closed can no longer
/// see spending either. This was the one diagnostic of the three that did not
/// take the flag, so it silently excluded the subtree case.
#[test]
fn a_closed_child_reports_against_the_parent_budget() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2019-01-01 open Expenses:Food:Groceries\n\
         2019-01-01 open Assets:Cash\n\
         2019-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2024-03-01 close Expenses:Food:Groceries\n",
    );
    let out = Command::new(&bin)
        .args([
            "report",
            f.path().to_str().unwrap(),
            "budget",
            "--children",
            "--from",
            "2024-01-01",
            "--to",
            "2025-01-01",
            "--no-pager",
        ])
        .output()
        .expect("run");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("closed on"),
        "a parent budget whose only covering account is closed must be reported: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// A total whose component is unknown is itself unknown. It must say WHY, rather
/// than reusing the per-budget phrasing, so a consumer can tell an overflowing
/// aggregate from an overflowing single budget.
#[test]
fn an_absent_total_explains_that_a_component_overflowed() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food\n\
         2024-01-01 open Expenses:Gas\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 7000000000000000000000000000.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Gas \"monthly\" 100.00 USD\n",
    );
    let json = run(
        &bin,
        &[
            "report",
            f.path().to_str().unwrap(),
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2025-01-01",
            "--format",
            "json",
            "--no-pager",
        ],
    );
    assert!(
        json.contains("is absent because at least one budget in it"),
        "the absent total must name its cause: {json}"
    );
    // The well-formed row is still reported in full.
    assert!(json.contains(r#""account": "Expenses:Gas""#), "{json}");
}

/// The text report draws two horizontal rules — one under the column headers and
/// one above the totals — whose width is computed from the content
/// (`RULE.max(acct_w + 1 + ccy_w + bw + aw + rw + uw)`). Nothing asserted the
/// computed width agreed with what was actually rendered, so every arithmetic
/// operator in that expression could be corrupted without a test noticing: a
/// rule shorter than its rows reads as a truncated table, and one longer reads
/// as a stray line. Assert the relationship directly — the rules span exactly
/// the widest line they separate — with content wide enough to beat the
/// constant floor.
#[test]
fn the_rules_span_the_widest_rendered_line() {
    let bin = require_rledger!();
    // A long account and a wide figure push every column past its header, so the
    // computed width (not the 84-column floor) decides.
    let f = write_fixture(
        "2024-01-01 open Expenses:AlphaDivision:Operations:Facilities:Utilities USD\n\
         2024-01-01 open Assets:Cash USD\n\
         2024-01-01 custom \"budget\" Expenses:AlphaDivision:Operations:Facilities:Utilities \"monthly\" 1234567.89 USD\n\
         2024-02-05 * \"power\"\n  \
           Expenses:AlphaDivision:Operations:Facilities:Utilities  987654.32 USD\n  \
           Assets:Cash\n",
    );
    let path = f.path().to_str().unwrap();
    let text = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
        ],
    );

    let rules: Vec<&str> = text
        .lines()
        .filter(|l| !l.is_empty() && l.chars().all(|c| c == '-'))
        .collect();
    assert_eq!(rules.len(), 2, "expected two dashed rules:\n{text}");
    assert_eq!(
        rules[0].chars().count(),
        rules[1].chars().count(),
        "the two rules must be the same width:\n{text}"
    );
    let rule_w = rules[0].chars().count();
    assert!(
        rule_w > 84,
        "this fixture must exceed the 84-column floor so the computed width is \
         what is under test, got {rule_w}:\n{text}"
    );

    // Every line of the table proper — headers, rows, totals — is exactly as
    // wide as the rule. Trailing spaces are not emitted, so compare against the
    // widest line rather than each one.
    let widest = text
        .lines()
        .filter(|l| l.contains(" USD") || l.starts_with("Account") || l.starts_with("TOTAL"))
        .map(|l| l.chars().count())
        .max()
        .expect("table lines");
    assert_eq!(
        rule_w, widest,
        "the rule must span the widest table line, not fall short or overhang:\n{text}"
    );
}

/// The currency-mismatch scan windows postings to `[from, to)`, the same window
/// the report itself uses, so that a currency the account stopped posting years
/// ago cannot suppress the warning. Both ends of that window need pinning: a
/// posting on `from` counts, and one on `to` does not.
#[test]
fn the_currency_mismatch_scan_uses_the_half_open_window() {
    let bin = require_rledger!();
    let ledger = |date: &str| {
        format!(
            "2020-01-01 open Expenses:Gear USD,EUR\n\
             2020-01-01 open Assets:Cash USD,EUR\n\
             2020-01-01 custom \"budget\" Expenses:Gear \"monthly\" 100.00 EUR\n\
             {date} * \"kit\"\n  \
               Expenses:Gear  50.00 USD\n  \
               Assets:Cash\n"
        )
    };
    let warns = |source: String| -> bool {
        let f = write_fixture(&source);
        let path = f.path().to_str().unwrap().to_string();
        let out = Command::new(&bin)
            .args([
                "report",
                &path,
                "budget",
                "--from",
                "2024-02-01",
                "--to",
                "2024-03-01",
            ])
            .output()
            .expect("run rledger");
        String::from_utf8_lossy(&out.stderr).contains("EUR")
    };

    // A USD posting on the first day of the window is in scope: the EUR budget
    // is a mismatch and must be reported.
    assert!(
        warns(ledger("2024-02-01")),
        "a posting on `from` is inside the window"
    );
    // The day before the window, and the exclusive end, are both out of scope —
    // with no in-window posting there is nothing to contradict the EUR budget.
    assert!(
        !warns(ledger("2024-01-31")),
        "a posting the day before `from` is outside the window"
    );
    assert!(
        !warns(ledger("2024-03-01")),
        "a posting on `to` is outside the window — `to` is exclusive"
    );
}

/// The mismatch warning fires only when the covered accounts posted SOMETHING
/// and none of it was the budgeted currency. An account that posted nothing at
/// all in the window is not a currency mismatch — it is simply unspent, and
/// warning there would name an empty list of currencies ("posts , not EUR").
#[test]
fn an_account_with_no_postings_is_not_a_currency_mismatch() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2020-01-01 open Expenses:Gear EUR\n\
         2020-01-01 custom \"budget\" Expenses:Gear \"monthly\" 100.00 EUR\n",
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
        ])
        .output()
        .expect("run rledger");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stderr.contains("posts"),
        "an unspent budget must not be reported as a currency mismatch: {stderr}"
    );
}

/// `close` on the window's exclusive end means the account was open for every
/// day the report covers, so there is nothing to warn about. Only a close
/// landing exactly on `to` separates the `when < to` bound from `when <= to`.
#[test]
fn an_account_closed_on_the_windows_exclusive_end_is_not_warned_about() {
    let bin = require_rledger!();
    let warns_for = |close: &str| -> bool {
        let f = write_fixture(&format!(
            "2024-01-01 open Expenses:Food USD\n\
             2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
             {close} close Expenses:Food\n"
        ));
        let path = f.path().to_str().unwrap().to_string();
        let out = Command::new(&bin)
            .args([
                "report",
                &path,
                "budget",
                "--from",
                "2024-02-01",
                "--to",
                "2024-03-01",
            ])
            .output()
            .expect("run rledger");
        String::from_utf8_lossy(&out.stderr).contains("closed")
    };
    assert!(
        !warns_for("2024-03-01"),
        "closing on the exclusive end leaves the account open all window"
    );
    assert!(
        warns_for("2024-02-15"),
        "closing mid-window really does strand the rest of the budget"
    );
}

/// The un-representable-figure warning fires when EITHER side is absent, not
/// only when both are. An overflowing budget beside ordinary spending is the
/// common shape and must still be explained.
#[test]
fn one_absent_figure_is_enough_to_explain_itself() {
    let bin = require_rledger!();
    // A budget large enough to overflow `Decimal` when pro-rated, against an
    // account with perfectly ordinary (representable) spending.
    // A single interval always fits (the accrual is at most the declared
    // amount), so the overflow has to come from SUMMING intervals: 1e28 a month
    // for twelve months is 1.2e29, past `Decimal`'s ~7.9e28 ceiling.
    let f = write_fixture(
        "2024-01-01 open Expenses:Huge USD\n\
         2024-01-01 open Assets:Cash USD\n\
         2024-01-01 custom \"budget\" Expenses:Huge \"monthly\" \
         10000000000000000000000000000 USD\n\
         2024-02-10 * \"ordinary\"\n  \
           Expenses:Huge  25.00 USD\n  \
           Assets:Cash\n",
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
            "2025-01-01",
            "--format",
            "json",
        ])
        .output()
        .expect("run rledger");
    let json = String::from_utf8_lossy(&out.stdout);
    // Exactly one side is absent: the budget overflowed, the actual did not.
    assert!(json.contains(r#""budgeted": null"#), "{json}");
    assert!(json.contains(r#""actual": "25.00""#), "{json}");
    // The ROW's own message, not the substring it shares with the TOTAL's.
    // `too large to represent` appears in both, so asserting it alone was
    // satisfied by the totals warning even with the row check disabled — a
    // proxy that could not fail on the defect it names.
    assert!(
        json.contains("budget for Expenses:Huge in USD is too large to represent"),
        "an absent figure must be explained even when its neighbor is fine: {json}"
    );
}

/// Numeric columns are content-width PLUS EXACTLY TWO — one space of gutter and
/// one of breathing room. Asserting only that the rules span the widest line
/// leaves the padding free: doubling it widens the rule and the rows together,
/// so the table stays self-consistent while wasting a screenful of space.
#[test]
fn numeric_columns_carry_exactly_two_spaces_of_padding() {
    let bin = require_rledger!();
    // Every numeric cell is NARROWER than its header here ("0.00" < "Budgeted",
    // "n/a" < "Used"), so each column is exactly its header plus the padding —
    // which is what makes the padding itself observable.
    let f = write_fixture(
        "2024-01-01 open Expenses:A USD\n\
         2024-01-01 open Assets:Cash USD\n\
         2024-01-01 custom \"budget\" Expenses:A \"monthly\" 0.00 USD\n\
         2024-02-05 * \"x\"\n  \
           Expenses:A  0.50 USD\n  \
           Assets:Cash\n",
    );
    let path = f.path().to_str().unwrap();
    let text = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
        ],
    );
    let header = text
        .lines()
        .find(|l| l.trim_start().starts_with("Account"))
        .unwrap_or_else(|| panic!("no header: {text}"));
    // Each numeric header is right-aligned in a column two wider than the
    // widest thing in it — here the header itself — so exactly two spaces
    // precede each. Doubling the padding instead of adding it widens the rule
    // and the rows together, leaving the table self-consistent and the earlier
    // "rules span the widest line" check satisfied.
    for head in ["Budgeted", "Actual", "Remaining", "Used"] {
        let at = header
            .find(head)
            .unwrap_or_else(|| panic!("{head}: {text}"));
        let before = &header[..at];
        let gutter = before.len() - before.trim_end().len();
        assert_eq!(
            gutter, 2,
            "the {head} column must be content width + 2, got {gutter} spaces \
             of gutter:\n{text}"
        );
    }
}

/// The window bound the three diagnostics share is EXCLUSIVE at `to`. A budget
/// declared exactly on the window's end contributes no row, so it must not be
/// judged against that window's postings either.
#[test]
fn a_budget_declared_on_the_windows_end_is_not_diagnosed() {
    let bin = require_rledger!();
    let warns = |budget_date: &str| -> bool {
        let f = write_fixture(&format!(
            "2020-01-01 open Expenses:Gear USD,EUR\n\
             2020-01-01 open Assets:Cash USD,EUR\n\
             {budget_date} custom \"budget\" Expenses:Gear \"monthly\" 100.00 EUR\n\
             2024-02-10 * \"kit\"\n  \
               Expenses:Gear  50.00 USD\n  \
               Assets:Cash\n"
        ));
        let path = f.path().to_str().unwrap().to_string();
        let out = Command::new(&bin)
            .args([
                "report",
                &path,
                "budget",
                "--from",
                "2024-02-01",
                "--to",
                "2024-03-01",
            ])
            .output()
            .expect("run rledger");
        String::from_utf8_lossy(&out.stderr).contains("only posts USD")
    };
    assert!(
        !warns("2024-03-01"),
        "a budget starting on the exclusive end is outside the window"
    );
    assert!(
        warns("2024-02-28"),
        "one day inside it, the mismatch is real and must be reported"
    );
}

/// None of the three diagnostics may judge a budget declared exactly ON the
/// window's exclusive end, because none of them can show it: `to` is exclusive,
/// so such a budget contributes no row, no total and no figure.
///
/// All three carry the same `b.from < to` bound, and each was verified to
/// survive `<=` on its own — a budget dated on the bound is the only input that
/// separates them.
#[test]
fn no_diagnostic_judges_a_budget_declared_on_the_exclusive_end() {
    let bin = require_rledger!();
    // One ledger, one date knob, three latent complaints: an unopened account,
    // a closed account, and a currency the account never posts.
    let stderr_for = |budget_date: &str| -> String {
        let f = write_fixture(&format!(
            "2020-01-01 open Expenses:Gear USD\n\
             2020-01-01 open Assets:Cash USD\n\
             2024-02-20 close Expenses:Gear\n\
             {budget_date} custom \"budget\" Expenses:Gear \"monthly\" 100.00 EUR\n\
             {budget_date} custom \"budget\" Expenses:Nosuch \"monthly\" 100.00 USD\n\
             2024-02-10 * \"kit\"\n  \
               Expenses:Gear  50.00 USD\n  \
               Assets:Cash\n"
        ));
        let path = f.path().to_str().unwrap().to_string();
        let out = Command::new(&bin)
            .args([
                "report",
                &path,
                "budget",
                "--from",
                "2024-02-01",
                "--to",
                "2024-03-01",
            ])
            .output()
            .expect("run rledger");
        String::from_utf8_lossy(&out.stderr).into_owned()
    };

    let on_the_bound = stderr_for("2024-03-01");
    assert!(
        !on_the_bound.contains("no such account is opened"),
        "unopened: {on_the_bound}"
    );
    assert!(!on_the_bound.contains("closed"), "closed: {on_the_bound}");
    assert!(
        !on_the_bound.contains("only posts"),
        "currency: {on_the_bound}"
    );

    // One day inside it, all three are real and must be reported — otherwise
    // the assertions above would pass on a report that never diagnoses anything.
    let inside = stderr_for("2024-02-28");
    assert!(
        inside.contains("no such account is opened"),
        "unopened: {inside}"
    );
    assert!(inside.contains("closed"), "closed: {inside}");
    assert!(inside.contains("only posts"), "currency: {inside}");
}

/// The `empty` object's `code` is the stable tag a dashboard branches on, so
/// each diagnosis must carry its own. Asserting only that the field exists let
/// every diagnosis answer with the same string.
#[test]
fn each_empty_diagnosis_carries_its_own_code() {
    let bin = require_rledger!();
    let budgeted = write_fixture(
        "2024-01-01 open Expenses:Food USD\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let empty_ledger = write_fixture("2024-01-01 open Expenses:Food USD\n");
    let code_of = |path: &str, args: &[&str]| -> String {
        let mut argv = vec!["report", path, "budget", "--format", "json"];
        argv.extend_from_slice(args);
        let json = run(&bin, &argv);
        let at = json
            .find(r#""empty": "#)
            .unwrap_or_else(|| panic!("no empty field: {json}"));
        let rest = &json[at..];
        rest.find(r#""code": ""#).map_or_else(
            || "null".to_string(),
            |c| {
                let tail = &rest[c + r#""code": ""#.len()..];
                tail[..tail.find('"').expect("closing quote")].to_string()
            },
        )
    };
    let budgeted_path = budgeted.path().to_str().unwrap();
    assert_eq!(
        code_of(
            budgeted_path,
            &[
                "--from",
                "2024-02-01",
                "--to",
                "2024-03-01",
                "--account",
                "Nope"
            ]
        ),
        "filtered_out"
    );
    assert_eq!(
        code_of(
            budgeted_path,
            &["--from", "2020-01-01", "--to", "2020-03-01"]
        ),
        "none_in_window"
    );
    assert_eq!(
        code_of(
            empty_ledger.path().to_str().unwrap(),
            &["--from", "2020-01-01", "--to", "2020-03-01"]
        ),
        "none_declared"
    );
    // And a report WITH rows says `null`, not a code.
    assert_eq!(
        code_of(
            budgeted_path,
            &["--from", "2024-02-01", "--to", "2024-03-01"]
        ),
        "null"
    );
}

/// A budget too small to survive display rounding is announced, and a budget
/// that is genuinely zero is not — the report would otherwise explain a zero it
/// was asked for.
#[test]
fn a_budget_below_display_precision_says_so() {
    let bin = require_rledger!();
    let stderr_for = |amount: &str| -> String {
        let f = write_fixture(&format!(
            "2024-01-01 open Expenses:Fees USD\n\
             2024-01-01 open Assets:Cash USD\n\
             2024-01-01 custom \"budget\" Expenses:Fees \"monthly\" {amount} USD\n\
             2024-02-10 * \"x\"\n  \
               Expenses:Fees  500.00 USD\n  \
               Assets:Cash\n"
        ));
        let path = f.path().to_str().unwrap().to_string();
        let out = Command::new(&bin)
            .args([
                "report",
                &path,
                "budget",
                "--from",
                "2024-02-01",
                "--to",
                "2024-03-01",
            ])
            .output()
            .expect("run rledger");
        String::from_utf8_lossy(&out.stderr).into_owned()
    };
    let tiny = stderr_for("0.004");
    assert!(
        tiny.contains("smaller than the display precision"),
        "a real budget hidden by rounding must be announced: {tiny}"
    );
    // Zero is not "hidden by rounding" — it renders as exactly what it is.
    let zero = stderr_for("0.00");
    assert!(
        !zero.contains("smaller than the display precision"),
        "a genuinely zero budget needs no explanation: {zero}"
    );
    // Nor does an ordinary one.
    let ordinary = stderr_for("400.00");
    assert!(
        !ordinary.contains("smaller than the display precision"),
        "{ordinary}"
    );
}

/// The bare `TOTAL` — the expenses bucket, the line a budget report exists for
/// — leads its currency's totals, ahead of any secondary bucket.
///
/// Not free: the crate hands totals over in beancount STATEMENT order (assets,
/// liabilities, equity, income, expenses), which puts the headline last. That
/// ordering is right for a general-purpose type and wrong for this reader, so
/// the renderer reorders — and nothing asserted it until a type change silently
/// moved `TOTAL (Income)` above `TOTAL`.
#[test]
fn the_headline_total_leads_its_currency() {
    let bin = require_rledger!();
    let f = write_fixture(
        "2024-01-01 open Expenses:Food USD\n\
         2024-01-01 open Income:Salary USD\n\
         2024-01-01 open Liabilities:Card USD\n\
         2024-01-01 open Assets:Cash USD\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n\
         2024-01-01 custom \"budget\" Income:Salary \"monthly\" 5000.00 USD\n\
         2024-01-01 custom \"budget\" Liabilities:Card \"monthly\" 100.00 USD\n",
    );
    let path = f.path().to_str().unwrap();
    let text = run(
        &bin,
        &[
            "report",
            path,
            "budget",
            "--from",
            "2024-02-01",
            "--to",
            "2024-03-01",
        ],
    );
    let totals: Vec<&str> = text
        .lines()
        .filter(|l| l.starts_with("TOTAL"))
        .map(|l| l.split_whitespace().next().unwrap_or(""))
        .collect();
    assert_eq!(
        totals.first(),
        Some(&"TOTAL"),
        "the expenses total must lead:\n{text}"
    );
    assert_eq!(totals.len(), 3, "all three buckets present:\n{text}");
}

/// Which `custom "budget"` directives rledger claims, in both directions.
///
/// `custom` is beancount's OPEN extension point and the name "budget" is not
/// rledger's alone, so ownership is one rule: a real interval KEYWORD in the
/// interval slot, or an ACCOUNT and an AMOUNT in theirs.
///
/// Table-driven because this rule has been got wrong in both directions, twice.
/// Tightening it to stop warning on beancount's documented example disowned
/// real budgets with a mistyped account; reordering to fix that started
/// claiming an envelope tool's config. Every row below is a case one of those
/// attempts got wrong — a test that pins only the cases you happened to think
/// of is how a guard ends up weaker than its name.
#[test]
fn ownership_of_the_custom_budget_namespace() {
    let bin = require_rledger!();
    // (should rledger claim it, directive, why)
    let cases: &[(bool, &str, &str)] = &[
        // OURS — a real interval keyword.
        (
            true,
            "Expenses:Food \"fortnight\" 400.00 USD",
            "unsupported interval keyword",
        ),
        (
            true,
            "\"Expenses:food\" \"monthly\" 400.00 USD",
            "unlexable account",
        ),
        (true, "Expenses:Food \"monthly\" 400.00", "missing currency"),
        (
            true,
            "Expenses:Food \"monthly\" 400.00 USD 23",
            "trailing figure",
        ),
        (
            true,
            "Expenses:Food 400.00 USD",
            "interval forgotten: account + amount, no room in two values for another schema",
        ),
        // NOT OURS — no keyword, and no account-plus-amount.
        (
            false,
            "\"envelope-groceries\" \"rollover\" 250.00 USD",
            "another tool's config: no account, no keyword",
        ),
        (
            false,
            "\"weekly < 1000.00 USD\" 2016-02-28 TRUE 43.03 USD 23",
            "beancount's own documented example",
        ),
        (
            false,
            "Assets:Bank:Checking 1000.00 USD TRUE \"monthly\"",
            "four values is another tool's schema, not Fava's three",
        ),
        (
            true,
            "Expenses:Food 400.00 USD \"monthly\"",
            "transposed, but still recognizably a budget",
        ),
    ];
    for (ours, directive, why) in cases {
        let f = write_fixture(&format!(
            "2020-01-01 open Assets:Bank:Checking\n\
             2020-01-01 open Expenses:Food USD\n\
             2024-01-01 custom \"budget\" {directive}\n"
        ));
        let out = Command::new(&bin)
            .args(["check", f.path().to_str().unwrap()])
            .output()
            .expect("run rledger check");
        let combined = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(
            combined.contains("E11001"),
            *ours,
            "{why}: `custom \"budget\" {directive}`\n{combined}"
        );
    }

    // A well-formed budget is claimed and silent — the rule must not be
    // satisfied merely by never claiming anything.
    let good = write_fixture(
        "2020-01-01 open Expenses:Food USD\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let out = Command::new(&bin)
        .args(["check", good.path().to_str().unwrap()])
        .output()
        .expect("run rledger check");
    assert!(
        !String::from_utf8_lossy(&out.stdout).contains("E11001"),
        "a valid budget must be silent"
    );
}

/// JSON totals carry the account TYPE and the ledger's own root as separate
/// fields, not just a rendered label.
///
/// One string cannot hold both. A ledger with `option "name_income" "Revenue"`
/// renders `TOTAL (Revenue)`: a consumer keying on that cannot tell it is the
/// income total, and one keying on `TOTAL` cannot tell it from the expenses
/// total. The WIT surface was split for exactly this reason; the CLI's machine
/// format needed the same treatment.
#[test]
fn json_totals_carry_the_type_and_the_ledgers_own_root() {
    let bin = require_rledger!();
    let f = write_fixture(
        "option \"name_income\" \"Revenue\"\n\
         2024-01-01 open Revenue:Salary USD\n\
         2024-01-01 open Expenses:Food USD\n\
         2024-01-01 custom \"budget\" Revenue:Salary \"monthly\" 5000.00 USD\n\
         2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD\n",
    );
    let json = run(
        &bin,
        &[
            "report",
            f.path().to_str().unwrap(),
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
    // The income total is identifiable as income even though the ledger never
    // uses that word, and still renders under the name the ledger chose.
    assert!(
        json.contains(r#""kind": "income", "root": "Revenue""#),
        "{json}"
    );
    assert!(
        json.contains(r#""account": "TOTAL (Revenue)""#),
        "the rendered label is still there for humans: {json}"
    );
    // ...and the expenses total keeps the bare label AND a usable type.
    assert!(
        json.contains(r#""kind": "expenses", "root": "Expenses""#),
        "{json}"
    );
}

/// The agent surface carries diagnostics as RECORDS, with the fields the report
/// already knew.
///
/// It used to receive formatted lines and rebuild records by splitting on
/// newlines, which discarded the date and the account outright and broke any
/// message carrying its own newline into two entries — and the "no budgets
/// declared" note quotes an example directive on a second line.
#[test]
fn the_agent_envelope_carries_structured_diagnostics() {
    let Some(bin) = option_env!("CARGO_BIN_EXE_ag-rledger").map(std::path::PathBuf::from) else {
        eprintln!("skip: ag-rledger not built (needs --features ag-rledger)");
        return;
    };
    if !bin.exists() {
        eprintln!("skip: ag-rledger not built");
        return;
    }
    let f = write_fixture(
        "2024-01-01 open Expenses:Food USD\n\
         2024-01-01 custom \"budget\" Expenses:Fodo \"monthly\" 400.00 USD\n",
    );
    let out = Command::new(&bin)
        .args([
            "report",
            f.path().to_str().unwrap(),
            "budget",
            "--from",
            "2024-01-01",
            "--to",
            "2024-02-01",
        ])
        .output()
        .expect("run ag-rledger");
    let body = String::from_utf8_lossy(&out.stdout);
    // Field-by-field, not substring: the envelope is compact JSON, and matching
    // on `"account": "..."` with a space would pass or fail on the serializer's
    // whitespace rather than on the contract.
    let envelope: serde_json::Value = serde_json::from_str(&body)
        .unwrap_or_else(|e| panic!("envelope must be JSON: {e}\n{body}"));
    let warnings = envelope["result"]["warnings"]
        .as_array()
        .unwrap_or_else(|| panic!("the warning must reach the envelope at all: {body}"));
    assert_eq!(warnings.len(), 1, "{warnings:?}");
    // The date and the account are their own fields, not buried in prose.
    assert_eq!(warnings[0]["account"], "Expenses:Fodo");
    assert_eq!(warnings[0]["date"], "2024-01-01");
    assert!(
        warnings[0]["message"]
            .as_str()
            .is_some_and(|m| m.contains("no such account is opened")),
        "{warnings:?}"
    );
}
