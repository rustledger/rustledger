//! `rledger report ... --from/--to/--year/--time` (#2643): the shared date
//! window, applied by CLAMPING the ledger (`rustledger_ops::clamp`), never by
//! filtering it.
//!
//! The expected figures are beancount's. Each window's per-account balances
//! were produced from this exact ledger by beancount 3.2.3's
//! `summarize.clamp_opt` (the clamp Fava's time filter runs) and cross-checked
//! with bean-query, e.g.
//!
//! ```text
//! bean-query window.beancount "SELECT account, sum(position)
//!     FROM OPEN ON 2023-01-01 CLOSE ON 2024-01-01 GROUP BY account"
//! ```
//!
//! Every asset, liability, income and expense account must match beancount
//! exactly, lot by lot. Equity is compared at cost: beancount and rledger
//! split the same opening equity differently between accounts (rledger's
//! clamp keeps a held lot's cost on its opening contra, #1656; bean-query's
//! `OPEN ON` books pre-window conversions to `Equity:Conversions:Previous`),
//! and rledger's clamp books no end-of-window conversions entry, so
//! `Equity:Conversions:Current` is left out of that comparison and checked
//! on the balance sheet instead, where rledger computes it.

mod common;

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use rust_decimal::Decimal;
use serde_json::Value;

/// Two-and-a-bit years: salary, spending on a card, shares bought at two
/// costs and partly sold FIFO, an `@` and an `@@` currency conversion, a
/// pad, and prices.
const LEDGER: &str = r#"option "operating_currency" "USD"

2022-01-01 open Assets:Bank USD
2022-01-01 open Assets:Wallet USD
2022-01-01 open Assets:Euro EUR
2022-01-01 open Assets:Broker:Cash USD
2022-01-01 open Assets:Broker:AAPL AAPL "FIFO"
2022-01-01 open Liabilities:Card USD
2022-01-01 open Equity:Opening-Balances
2022-01-01 open Income:Salary USD
2022-01-01 open Income:Gains USD
2022-01-01 open Expenses:Food USD
2022-01-01 open Expenses:Travel EUR

2022-01-01 * "opening"
  Assets:Bank  5000.00 USD
  Equity:Opening-Balances

2022-03-15 * "salary"
  Assets:Bank  3000.00 USD
  Income:Salary

2022-04-01 * "groceries"
  Expenses:Food  120.00 USD
  Liabilities:Card

2022-05-01 * "buy shares"
  Assets:Broker:AAPL  10 AAPL {150.00 USD}
  Assets:Bank  -1500.00 USD

2022-06-01 * "fx"
  Assets:Euro  900.00 EUR @ 1.10 USD
  Assets:Bank  -990.00 USD

2022-07-01 price AAPL 170.00 USD
2022-07-01 price EUR 1.05 USD

2022-12-01 pad Assets:Wallet Equity:Opening-Balances
2022-12-02 balance Assets:Wallet  40.00 USD

2023-01-10 * "salary"
  Assets:Bank  3100.00 USD
  Income:Salary

2023-02-01 * "buy more shares"
  Assets:Broker:AAPL  5 AAPL {180.00 USD}
  Assets:Bank  -900.00 USD

2023-03-01 * "trip"
  Expenses:Travel  300.00 EUR
  Assets:Euro

2023-04-01 * "sell shares"
  Assets:Broker:AAPL  -12 AAPL {} @ 200.00 USD
  Assets:Broker:Cash  2400.00 USD
  Income:Gains

2023-05-01 * "fx back"
  Assets:Bank  330.00 USD @@ 300.00 EUR
  Assets:Euro  -300.00 EUR

2023-06-01 * "pay card"
  Liabilities:Card  120.00 USD
  Assets:Bank

2023-06-15 * "groceries"
  Expenses:Food  80.00 USD
  Assets:Wallet

2023-07-01 price AAPL 210.00 USD

2023-12-31 * "year end groceries"
  Expenses:Food  45.00 USD
  Assets:Bank

2024-01-05 * "salary"
  Assets:Bank  3200.00 USD
  Income:Salary

2024-02-01 price AAPL 220.00 USD
"#;

fn write_fixture(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-window-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    f
}

fn run_raw(binary: &PathBuf, args: &[&str]) -> std::process::Output {
    Command::new(binary)
        .args(args)
        .arg("--no-pager")
        .output()
        .unwrap_or_else(|e| panic!("run rledger {args:?}: {e}"))
}

fn run(binary: &PathBuf, args: &[&str]) -> String {
    let out = run_raw(binary, args);
    assert!(
        out.status.success(),
        "rledger {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn json(binary: &PathBuf, args: &[&str]) -> Value {
    let stdout = run(binary, args);
    serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("not JSON ({e}): {stdout}"))
}

fn dec(s: &str) -> Decimal {
    s.replace(',', "")
        .parse()
        .unwrap_or_else(|_| panic!("number {s:?}"))
}

/// A lot's per-unit cost and currency from a rendered cost annotation such as
/// `{ 180.00 USD, 2023-02-01}` or `{180.00 USD, 2023-02-01}`; `None` for an
/// empty one.
fn parse_cost(cost: &str) -> Option<(Decimal, String)> {
    let inner = cost.trim().strip_prefix('{')?.strip_suffix('}')?;
    let mut tokens = inner.split([' ', ',']).filter(|t| !t.is_empty());
    let number = dec(tokens.next()?);
    let currency = tokens.next()?.to_string();
    Some((number, currency))
}

/// `account -> {"CUR" or "CUR {cost CUR}" -> units}`, from rows carrying
/// `account`, an amount field, `currency` and `cost`.
type Balances = BTreeMap<String, BTreeMap<String, Decimal>>;

fn balances_from_rows(rows: &[Value], amount_field: &str) -> Balances {
    let mut out: Balances = BTreeMap::new();
    for row in rows {
        let account = row["account"].as_str().unwrap().to_string();
        let currency = row["currency"].as_str().unwrap();
        let key = match parse_cost(row["cost"].as_str().unwrap_or("")) {
            Some((n, c)) => format!("{currency} {{{n} {c}}}"),
            None => currency.to_string(),
        };
        *out.entry(account).or_default().entry(key).or_default() +=
            dec(row[amount_field].as_str().unwrap());
    }
    out
}

/// Per-currency total at cost of the accounts selected by `pick`.
fn at_cost(balances: &Balances, pick: impl Fn(&str) -> bool) -> BTreeMap<String, Decimal> {
    let mut out: BTreeMap<String, Decimal> = BTreeMap::new();
    for (account, positions) in balances {
        if !pick(account) {
            continue;
        }
        for (key, units) in positions {
            let (amount, currency) = match key.split_once(" {") {
                Some((_, cost)) => {
                    let (n, c) = parse_cost(&format!("{{{cost}")).unwrap();
                    (*units * n, c)
                }
                None => (*units, key.clone()),
            };
            *out.entry(currency).or_default() += amount;
        }
    }
    out.retain(|_, v| !v.is_zero());
    out
}

/// beancount's `clamp_opt` balances for a window, as `(account, key, units)`.
fn oracle(rows: &[(&str, &str, &str)]) -> Balances {
    let mut out: Balances = BTreeMap::new();
    for (account, key, units) in rows {
        out.entry((*account).to_string())
            .or_default()
            .insert((*key).to_string(), dec(units));
    }
    out
}

/// beancount 3.2.3 `clamp_opt(entries, 2023-01-01, 2024-01-01)`.
fn oracle_2023() -> Balances {
    oracle(&[
        ("Assets:Bank", "USD", "7875.00"),
        ("Assets:Broker:AAPL", "AAPL {180.00 USD}", "3"),
        ("Assets:Broker:Cash", "USD", "2400.00"),
        ("Assets:Euro", "EUR", "300.00"),
        ("Assets:Wallet", "USD", "-40.00"),
        ("Equity:Conversions:Current", "USD", "-330.00"),
        ("Equity:Conversions:Current", "EUR", "300.00"),
        ("Equity:Earnings:Previous", "USD", "-2880.00"),
        ("Equity:Opening-Balances", "USD", "-4050.00"),
        ("Equity:Opening-Balances", "EUR", "-900.00"),
        ("Expenses:Food", "USD", "125.00"),
        ("Expenses:Travel", "EUR", "300.00"),
        ("Income:Gains", "USD", "-540.00"),
        ("Income:Salary", "USD", "-3100.00"),
    ])
}

/// beancount 3.2.3 `clamp_opt(entries, 2022-01-01, 2023-01-01)`.
fn oracle_2022() -> Balances {
    oracle(&[
        ("Assets:Bank", "USD", "5510.00"),
        ("Assets:Broker:AAPL", "AAPL {150.00 USD}", "10"),
        ("Assets:Euro", "EUR", "900.00"),
        ("Assets:Wallet", "USD", "40.00"),
        ("Equity:Conversions:Current", "USD", "990.00"),
        ("Equity:Conversions:Current", "EUR", "-900.00"),
        ("Equity:Opening-Balances", "USD", "-5040.00"),
        ("Expenses:Food", "USD", "120.00"),
        ("Income:Salary", "USD", "-3000.00"),
        ("Liabilities:Card", "USD", "-120.00"),
    ])
}

/// beancount 3.2.3 `clamp_opt(entries, 2023-02-01, 2023-05-01)`.
fn oracle_feb_to_apr_2023() -> Balances {
    oracle(&[
        ("Assets:Bank", "USD", "7710.00"),
        ("Assets:Broker:AAPL", "AAPL {180.00 USD}", "3"),
        ("Assets:Broker:Cash", "USD", "2400.00"),
        ("Assets:Euro", "EUR", "600.00"),
        ("Assets:Wallet", "USD", "40.00"),
        ("Equity:Earnings:Previous", "USD", "-5980.00"),
        ("Equity:Opening-Balances", "USD", "-4050.00"),
        ("Equity:Opening-Balances", "EUR", "-900.00"),
        ("Expenses:Travel", "EUR", "300.00"),
        ("Income:Gains", "USD", "-540.00"),
        ("Liabilities:Card", "USD", "-120.00"),
    ])
}

fn is_equity(account: &str) -> bool {
    account.starts_with("Equity:")
}

const CONVERSIONS: &str = "Equity:Conversions:Current";

/// Non-equity accounts match beancount lot for lot; equity matches at cost,
/// leaving out the conversions entry rledger's clamp does not book.
fn assert_matches_oracle(got: &Balances, want: &Balances, label: &str) {
    let non_equity = |b: &Balances| -> Balances {
        b.iter()
            .filter(|(a, _)| !is_equity(a))
            .map(|(a, p)| (a.clone(), p.clone()))
            .collect()
    };
    assert_eq!(
        non_equity(got),
        non_equity(want),
        "{label}: non-equity accounts"
    );
    let equity = |a: &str| is_equity(a) && a != CONVERSIONS;
    assert_eq!(
        at_cost(got, equity),
        at_cost(want, equity),
        "{label}: equity at cost"
    );
}

fn balances_report(bin: &PathBuf, path: &Path, window: &[&str]) -> Balances {
    let mut args = vec!["report", path.to_str().unwrap(), "-f", "json", "balances"];
    args.extend_from_slice(window);
    let v = json(bin, &args);
    balances_from_rows(v.as_array().unwrap(), "amount")
}

#[test]
fn windowed_balances_match_beancounts_clamp() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    for (window, want, label) in [
        (vec!["--year", "2023"], oracle_2023(), "--year 2023"),
        (vec!["--time", "2023"], oracle_2023(), "--time 2023"),
        (
            vec!["--from", "2023-01-01", "--to", "2024-01-01"],
            oracle_2023(),
            "--from/--to 2023",
        ),
        (vec!["--time", "fy2022"], oracle_2022(), "--time fy2022"),
        (
            vec!["--time", "2023-02 - 2023-04"],
            oracle_feb_to_apr_2023(),
            "--time 2023-02 - 2023-04",
        ),
    ] {
        let got = balances_report(&bin, f.path(), &window);
        assert_matches_oracle(&got, &want, label);
    }
}

/// The window CLAMPS: earlier income is not lost, it moves to equity, so the
/// windowed balances still sum to zero at cost once the conversion residual
/// is accounted for (rledger's clamp leaves it unbooked).
#[test]
fn windowed_balances_carry_earlier_activity_into_equity() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let got = balances_report(&bin, f.path(), &["--year", "2023"]);
    assert_eq!(
        got["Equity:Earnings:Previous"]["USD"],
        dec("-2880.00"),
        "2022's net income must be carried in as previous earnings"
    );
    // Nothing from 2024 survives the window's end.
    assert_eq!(got["Income:Salary"]["USD"], dec("-3100.00"));
    // All accounts at cost: zero except the unbooked conversion residual.
    let total = at_cost(&got, |_| true);
    let mut want = BTreeMap::new();
    want.insert("EUR".to_string(), dec("-300.00"));
    want.insert("USD".to_string(), dec("330.00"));
    assert_eq!(total, want);
}

#[test]
fn windowed_income_covers_only_the_window() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let v = json(
        &bin,
        &["report", path, "-f", "json", "income", "--year", "2023"],
    );
    let rows = v["accounts"].as_array().unwrap();
    let got: BTreeMap<(String, String), Decimal> = rows
        .iter()
        .map(|r| {
            (
                (
                    r["account"].as_str().unwrap().to_string(),
                    r["currency"].as_str().unwrap().to_string(),
                ),
                dec(r["amount"].as_str().unwrap()),
            )
        })
        .collect();
    // bean-query: SELECT account, sum(position) FROM OPEN ON 2023-01-01
    //   CLOSE ON 2024-01-01 WHERE account ~ '^(Income|Expenses)' GROUP BY account
    let want: BTreeMap<(String, String), Decimal> = [
        ("Expenses:Food", "USD", "125.00"),
        ("Expenses:Travel", "EUR", "300.00"),
        ("Income:Gains", "USD", "-540.00"),
        ("Income:Salary", "USD", "-3100.00"),
    ]
    .into_iter()
    .map(|(a, c, n)| ((a.to_string(), c.to_string()), dec(n)))
    .collect();
    assert_eq!(got, want);
    assert_eq!(
        v["net_income"]["USD"].as_str().map(dec),
        Some(dec("3515.00"))
    );
    assert_eq!(
        v["net_income"]["EUR"].as_str().map(dec),
        Some(dec("-300.00"))
    );
}

/// A balance sheet over a window balances: at cost, assets + liabilities +
/// equity (including the window's earnings and conversion residual) is zero
/// in every currency.
#[test]
fn windowed_balance_sheet_balances() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    for window in [
        vec!["--year", "2023"],
        vec!["--year", "2022"],
        vec!["--time", "2023-02 - 2023-04"],
        vec!["--from", "2023-03-01"],
        vec!["--to", "2023-03-01"],
        vec![],
    ] {
        let mut args = vec!["report", path, "-f", "json", "balsheet"];
        args.extend_from_slice(&window);
        let v = json(&bin, &args);
        let sheet = balances_from_rows(v["accounts"].as_array().unwrap(), "amount");
        let total = at_cost(&sheet, |_| true);
        assert!(
            total.is_empty(),
            "balance sheet {window:?} does not balance at cost: off by {total:?}\n{sheet:#?}"
        );
    }

    // The 2023 sheet's two capping lines are beancount's: the window's net
    // income, and clamp_opt's `Equity:Conversions:Current`.
    let v = json(
        &bin,
        &["report", path, "-f", "json", "balsheet", "--year", "2023"],
    );
    let sheet = balances_from_rows(v["accounts"].as_array().unwrap(), "amount");
    let mut earnings = BTreeMap::new();
    earnings.insert("USD".to_string(), dec("-3515.00"));
    earnings.insert("EUR".to_string(), dec("300.00"));
    assert_eq!(sheet["Equity:Earnings:Current"], earnings);
    assert_eq!(sheet[CONVERSIONS], oracle_2023()[CONVERSIONS]);
    // The balance-sheet accounts themselves are the clamped state.
    assert_matches_oracle(
        &sheet
            .iter()
            .filter(|(a, _)| !a.ends_with(":Current"))
            .map(|(a, p)| (a.clone(), p.clone()))
            .collect(),
        &oracle_2023()
            .into_iter()
            .filter(|(a, _)| !a.starts_with("Income:") && !a.starts_with("Expenses:"))
            .collect(),
        "balsheet --year 2023",
    );
}

#[test]
fn windowed_holdings_are_the_holdings_at_the_windows_end() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    for (year, units, basis) in [("2022", "10", "1500.00"), ("2023", "3", "540.00")] {
        let v = json(
            &bin,
            &["report", path, "-f", "json", "holdings", "--year", year],
        );
        let aapl = v
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["currency"] == "AAPL")
            .unwrap_or_else(|| panic!("no AAPL holding for {year}: {v}"));
        assert_eq!(dec(aapl["units"].as_str().unwrap()), dec(units), "{year}");
        assert_eq!(
            dec(aapl["cost_basis"].as_str().unwrap()),
            dec(basis),
            "{year}"
        );
    }
    // Before any purchase there is nothing to hold.
    let v = json(
        &bin,
        &[
            "report",
            path,
            "-f",
            "json",
            "holdings",
            "--to",
            "2022-05-01",
        ],
    );
    assert!(
        !v.as_array()
            .unwrap()
            .iter()
            .any(|r| r["currency"] == "AAPL"),
        "{v}"
    );
}

#[test]
fn windowed_journal_lists_openings_then_the_window() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    let v = json(
        &bin,
        &["report", path, "-f", "json", "journal", "--year", "2023"],
    );
    let txns = v.as_array().unwrap();
    let narrations: Vec<&str> = txns
        .iter()
        .map(|t| t["narration"].as_str().unwrap())
        .collect();
    // The window's own transactions, in order, and nothing outside it.
    let own: Vec<&str> = txns
        .iter()
        .filter(|t| t["flag"] != "S")
        .map(|t| t["narration"].as_str().unwrap())
        .collect();
    assert_eq!(
        own,
        [
            "salary",
            "buy more shares",
            "trip",
            "sell shares",
            "fx back",
            "pay card",
            "groceries",
            "year end groceries",
        ],
        "{narrations:?}"
    );
    for t in txns {
        let date = t["date"].as_str().unwrap();
        assert!(date.starts_with("2023-"), "{date} is outside the window");
    }
    // The opening balances come first and carry the pad's 40 USD into the
    // wallet: the clamp runs over the pad-expanded ledger.
    assert_eq!(txns[0]["flag"], "S");
    let wallet = txns
        .iter()
        .filter(|t| t["flag"] == "S")
        .flat_map(|t| t["postings"].as_array().unwrap())
        .find(|p| p["account"] == "Assets:Wallet")
        .expect("an opening balance for the padded wallet");
    assert_eq!(dec(wallet["amount"].as_str().unwrap()), dec("40.00"));

    // A window that contains the pad still does not list the pad's
    // synthesized transaction, as the unwindowed journal does not.
    let v = json(
        &bin,
        &["report", path, "-f", "json", "journal", "--year", "2022"],
    );
    assert!(
        v.as_array().unwrap().iter().all(|t| t["flag"] != "P"),
        "{v}"
    );
}

#[test]
fn conflicting_window_flags_are_rejected() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    for (args, needle) in [
        (
            vec!["balances", "--time", "2023", "--year", "2023"],
            "--time cannot be combined with --year",
        ),
        (
            vec!["income", "--year", "2023", "--from", "2023-01-01"],
            "--year cannot be combined with --from",
        ),
        (
            vec!["journal", "--time", "2023-13"],
            "failed to parse --time",
        ),
        (vec!["holdings", "--time", "2024 - 2023"], "is empty"),
        (
            vec!["balsheet", "--from", "2023-01-01", "--to", "2023-01-01"],
            "the window is empty",
        ),
        (
            vec!["budget", "--time", "2023", "--to", "2024-01-01"],
            "--time cannot",
        ),
    ] {
        let mut argv = vec!["report", path];
        argv.extend_from_slice(&args);
        let out = run_raw(&bin, &argv);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(!out.status.success(), "{args:?} must fail");
        assert!(stderr.contains(needle), "{args:?}: {stderr}");
    }
}

/// `budget` reads the same flags: `--year`/`--time` name the window its
/// `--from`/`--to` always could.
#[test]
fn budget_accepts_the_shared_window() {
    let bin = require_rledger!();
    let src =
        format!("{LEDGER}\n2022-01-01 custom \"budget\" Expenses:Food \"monthly\" 100.00 USD\n");
    let f = write_fixture(&src);
    let path = f.path().to_str().unwrap();
    let explicit = run(
        &bin,
        &[
            "report",
            path,
            "-f",
            "csv",
            "budget",
            "--from",
            "2023-01-01",
            "--to",
            "2024-01-01",
        ],
    );
    let year = run(
        &bin,
        &["report", path, "-f", "csv", "budget", "--year", "2023"],
    );
    let time = run(
        &bin,
        &["report", path, "-f", "csv", "budget", "--time", "2023"],
    );
    assert_eq!(year, explicit);
    assert_eq!(time, explicit);
    assert!(explicit.contains("125.00"), "{explicit}");
}

/// The clamp books into the ledger's OWN equity accounts.
#[test]
fn window_uses_the_ledgers_summary_accounts() {
    let bin = require_rledger!();
    let src = "option \"name_equity\" \"Eigen\"\n\
               option \"account_previous_earnings\" \"Winst:Vorig\"\n\
               2022-01-01 open Assets:Bank\n\
               2022-01-01 open Income:Pay\n\
               2022-06-01 * \"pay\"\n  Assets:Bank  100.00 USD\n  Income:Pay\n\
               2023-06-01 * \"pay\"\n  Assets:Bank  50.00 USD\n  Income:Pay\n";
    let f = write_fixture(src);
    let got = balances_report(&bin, f.path(), &["--year", "2023"]);
    assert_eq!(got["Eigen:Winst:Vorig"]["USD"], dec("-100.00"), "{got:#?}");
    assert_eq!(got["Income:Pay"]["USD"], dec("-50.00"));
    let v = json(
        &bin,
        &[
            "report",
            f.path().to_str().unwrap(),
            "-f",
            "json",
            "balsheet",
            "--year",
            "2023",
        ],
    );
    let sheet = balances_from_rows(v["accounts"].as_array().unwrap(), "amount");
    assert_eq!(
        sheet["Eigen:Earnings:Current"]["USD"],
        dec("-50.00"),
        "{sheet:#?}"
    );
}

/// `ag-rledger report` reads the same window flags and answers the same
/// figures, and rejects the same conflicts.
#[cfg(feature = "ag-rledger")]
#[test]
fn ag_rledger_takes_the_same_window() {
    let bin = require_rledger!();
    let ag = PathBuf::from(env!("CARGO_BIN_EXE_ag-rledger"));
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();
    for report in ["balances", "balsheet", "income", "journal", "holdings"] {
        let want = json(
            &bin,
            &[
                "report",
                path,
                "-f",
                "json",
                report,
                "--time",
                "2023-02 - 2023-04",
            ],
        );
        let out = Command::new(&ag)
            .args([
                "report",
                path,
                report,
                "--format",
                "json",
                "--time",
                "2023-02 - 2023-04",
            ])
            .output()
            .expect("spawn ag-rledger");
        let env: Value = serde_json::from_slice(&out.stdout).expect("envelope is JSON");
        assert_eq!(env["ok"], Value::Bool(true), "{report}: {env}");
        assert_eq!(env["result"]["data"], want, "{report}");
    }
    let out = Command::new(&ag)
        .args([
            "report",
            path,
            "income",
            "--year",
            "2023",
            "--to",
            "2024-01-01",
        ])
        .output()
        .expect("spawn ag-rledger");
    let env: Value = serde_json::from_slice(&out.stdout).expect("envelope is JSON");
    assert_eq!(env["ok"], Value::Bool(false), "{env}");
    assert!(
        env.to_string()
            .contains("--year cannot be combined with --to"),
        "{env}"
    );
}
