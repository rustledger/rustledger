//! Regression tests for L5: report routing and BQL classification must honor
//! the `name_*` root-rename options (a documented beancount feature), not
//! hardcoded "Assets:"/"Income:" prefixes.
//!
//! Pre-fix, `option "name_income" "Revenue"` produced an EMPTY income
//! statement, and `POSSIGN` failed to flip renamed credit-normal roots
//! (diverging from beanquery, which returns +100.00 for the fixture below).

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

const RENAMED_SOURCE: &str = r#"option "name_income" "Revenue"
option "name_assets" "Activa"

2024-01-01 open Activa:Cash
2024-01-01 open Revenue:Sales

2024-03-01 * "sale"
  Activa:Cash    100.00 USD
  Revenue:Sales -100.00 USD
"#;

fn write_fixture() -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-rename-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(RENAMED_SOURCE.as_bytes())
        .expect("write fixture");
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
fn income_report_includes_renamed_income_root() {
    let bin = require_rledger!();
    let f = write_fixture();
    let path = f.path().to_str().unwrap();
    let stdout = run(&bin, &["report", path, "income", "--no-pager"]);
    assert!(
        stdout.contains("Revenue:Sales"),
        "renamed income root must appear in the income statement \
         (pre-fix: empty statement): {stdout}",
    );
    assert!(
        stdout.contains("Total Income"),
        "income section must total the renamed accounts: {stdout}",
    );
}

#[test]
fn balsheet_includes_renamed_assets_root() {
    let bin = require_rledger!();
    let f = write_fixture();
    let path = f.path().to_str().unwrap();
    let stdout = run(&bin, &["report", path, "balsheet", "--no-pager"]);
    assert!(
        stdout.contains("Activa:Cash"),
        "renamed assets root must appear on the balance sheet: {stdout}",
    );
}

#[test]
fn possign_flips_renamed_income_root_like_beanquery() {
    let bin = require_rledger!();
    let f = write_fixture();
    let path = f.path().to_str().unwrap();
    let stdout = run(
        &bin,
        &[
            "query",
            path,
            "SELECT account, possign(number, account) WHERE account ~ \"Revenue\"",
        ],
    );
    // beanquery 3.2.3 on this fixture: Revenue:Sales -100.00 -> +100.00
    assert!(
        stdout.contains("100.00") && !stdout.contains("-100.00"),
        "POSSIGN must flip the renamed credit-normal root (beanquery \
         parity; pre-fix returned -100.00): {stdout}",
    );
}

#[test]
fn account_sortkey_classifies_renamed_root_like_beanquery() {
    let bin = require_rledger!();
    let f = write_fixture();
    let path = f.path().to_str().unwrap();
    let stdout = run(
        &bin,
        &[
            "query",
            path,
            "SELECT account_sortkey(account) WHERE account ~ \"Revenue\"",
        ],
    );
    // beanquery: renamed Income root sorts with index 3, not custom/5.
    assert!(
        stdout.contains("3-Revenue"),
        "ACCOUNT_SORTKEY must classify the renamed Income root as index 3 \
         (beanquery parity; pre-fix sorted it as custom): {stdout}",
    );
}
