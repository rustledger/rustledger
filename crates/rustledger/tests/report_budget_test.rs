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
    // Rows overlap by design (the parent row includes its child).
    assert!(
        txt.contains("Expenses:Food                USD         400.00        50.00"),
        "{txt}"
    );
    assert!(
        txt.contains("Expenses:Food:Restaurant     USD         100.00        50.00"),
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

/// A currency that appears only in a `custom "budget"` directive still has a
/// display precision, so a pro-rated (repeating) figure renders as money rather
/// than a 28-digit Decimal that overruns the columns.
#[test]
fn a_budget_only_currency_still_gets_display_precision() {
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
    assert!(txt.contains("245.16"), "{txt}");
    assert!(
        !txt.contains("245.1612903"),
        "the raw repeating decimal must not reach the report: {txt}"
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
        csv.contains("Expenses:Food,USD,245.16,0.00,245.16,0.0"),
        "{csv}"
    );
    assert!(csv.contains("TOTAL,USD,245.16"), "{csv}");
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
    assert!(txt.contains("Expenses:Food                EUR"), "{txt}");
    assert!(txt.contains("Expenses:Food                USD"), "{txt}");
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
    assert!(
        csv.contains("Expenses:Food,USD,n/a"),
        "two months of a MAX budget is not representable: {csv}"
    );
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
