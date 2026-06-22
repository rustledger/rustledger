//! Integration tests comparing rustledger against Python beancount.
//!
//! These tests verify that rustledger produces the same results as
//! the reference Python implementation.

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;

use common::{project_root, test_fixtures_dir};

fn rledger_binary() -> Option<PathBuf> {
    // Use CARGO_BIN_EXE_rledger if available (set by cargo test)
    if let Ok(path) = std::env::var("CARGO_BIN_EXE_rledger") {
        return Some(PathBuf::from(path));
    }

    // Check target/release first (for --release and nix builds)
    let release = project_root().join("target/release/rledger");
    if release.exists() {
        return Some(release);
    }

    // Fall back to target/debug
    let debug = project_root().join("target/debug/rledger");
    if debug.exists() {
        return Some(debug);
    }

    // Binary not found
    None
}

/// Check if Python beancount is available.
fn python_beancount_available() -> bool {
    Command::new("bean-check")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Run Python bean-check on a file.
fn python_bean_check(path: &Path) -> (bool, String) {
    let output = Command::new("bean-check")
        .arg(path)
        .output()
        .expect("Failed to run bean-check");

    let success = output.status.success();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (success, stderr)
}

/// Run rledger check on a file.
fn rust_bean_check(path: &Path) -> Option<(bool, String)> {
    let binary = rledger_binary()?;
    let output = Command::new(binary)
        .args(["check", path.to_str().unwrap()])
        .output()
        .expect("Failed to run rledger check");

    let success = output.status.success();
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    Some((success, combined))
}

#[test]
fn test_valid_ledger_parses_with_both() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    let path = test_fixtures_dir().join("valid-ledger.beancount");

    let (py_success, py_output) = python_bean_check(&path);
    let Some((rs_success, rs_output)) = rust_bean_check(&path) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    assert!(
        py_success,
        "Python beancount failed on valid file: {py_output}"
    );
    assert!(
        rs_success,
        "Rust beancount failed on valid file: {rs_output}"
    );
}

#[test]
fn test_directive_count_matches() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");

    // Parse with Rust and count
    let source = std::fs::read_to_string(&path).expect("Failed to read file");
    let result = rustledger_parser::parse(&source);

    // Count open directives
    let rs_open_count = result
        .directives
        .iter()
        .filter(|d| matches!(&d.value, rustledger_core::Directive::Open(_)))
        .count();

    // We expect 11 open directives
    assert_eq!(rs_open_count, 11, "Expected 11 open directives");

    // Count transactions
    let rs_txn_count = result
        .directives
        .iter()
        .filter(|d| matches!(&d.value, rustledger_core::Directive::Transaction(_)))
        .count();

    // We expect 8 transactions
    assert_eq!(rs_txn_count, 8, "Expected 8 transactions");

    // Verify no parse errors
    assert!(
        result.errors.is_empty(),
        "Unexpected parse errors: {:?}",
        result.errors
    );
}

#[test]
fn test_error_detection_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // Create a file with a known error (duplicate open)
    let content = r#"
option "title" "Error Test"

2020-01-01 open Assets:Bank
2020-01-01 open Assets:Bank  ; Duplicate!

2020-01-15 * "Test"
  Assets:Bank  100 USD
  Equity:Opening
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("error-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, _py_output) = python_bean_check(&temp_file);
    let Some((rs_success, _rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should report errors
    assert!(!py_success, "Python should detect duplicate open error");
    assert!(!rs_success, "Rust should detect duplicate open error");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_balance_assertion_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with failing balance assertion
    let content = r#"
option "title" "Balance Test"

2020-01-01 open Assets:Bank USD
2020-01-01 open Equity:Opening

2020-01-01 * "Opening"
  Assets:Bank  1000 USD
  Equity:Opening

2020-01-15 balance Assets:Bank  500 USD  ; Wrong amount!
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("balance-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, _) = python_bean_check(&temp_file);
    let Some((rs_success, _)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should fail on balance assertion
    assert!(
        !py_success,
        "Python should detect balance assertion failure"
    );
    assert!(!rs_success, "Rust should detect balance assertion failure");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_currency_constraint_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with currency constraint violation
    let content = r#"
option "title" "Currency Test"

2020-01-01 open Assets:USDOnly USD
2020-01-01 open Equity:Opening

2020-01-01 * "Wrong currency"
  Assets:USDOnly  100 EUR  ; EUR not allowed!
  Equity:Opening
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("currency-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, _) = python_bean_check(&temp_file);
    let Some((rs_success, _)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should fail on currency constraint
    assert!(
        !py_success,
        "Python should detect currency constraint violation"
    );
    assert!(
        !rs_success,
        "Rust should detect currency constraint violation"
    );

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_account_lifecycle_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with account used before open
    let content = r#"
option "title" "Lifecycle Test"

2020-01-01 open Equity:Opening

; Use account before it's opened
2020-01-15 * "Too early"
  Assets:Bank  100 USD
  Equity:Opening

2020-02-01 open Assets:Bank USD
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("lifecycle-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, _) = python_bean_check(&temp_file);
    let Some((rs_success, _)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should fail
    assert!(!py_success, "Python should detect account used before open");
    assert!(!rs_success, "Rust should detect account used before open");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_transaction_not_balanced_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with unbalanced transaction
    let content = r#"
option "title" "Unbalanced Test"

2020-01-01 open Assets:Bank USD
2020-01-01 open Expenses:Food USD

2020-01-15 * "Unbalanced"
  Assets:Bank     -100 USD
  Expenses:Food     50 USD  ; Should be 100 to balance
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("unbalanced-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, _) = python_bean_check(&temp_file);
    let Some((rs_success, _)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should fail on unbalanced transaction
    assert!(!py_success, "Python should detect unbalanced transaction");
    assert!(!rs_success, "Rust should detect unbalanced transaction");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_pad_directive_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with pad directive
    let content = r#"
option "title" "Pad Test"

2020-01-01 open Assets:Bank USD
2020-01-01 open Equity:Opening USD

2020-01-01 pad Assets:Bank Equity:Opening
2020-01-15 balance Assets:Bank 1000 USD
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("pad-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(
        py_success,
        "Python should handle pad directive: {py_output}"
    );
    assert!(rs_success, "Rust should handle pad directive: {rs_output}");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_price_directive_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with price directives
    let content = r#"
option "title" "Price Test"

2020-01-01 open Assets:Stock AAPL
2020-01-01 open Assets:Cash USD
2020-01-01 commodity AAPL
2020-01-01 commodity USD

2020-01-15 price AAPL 150 USD
2020-06-15 price AAPL 200 USD

2020-01-15 * "Buy stock"
  Assets:Stock   10 AAPL {150 USD}
  Assets:Cash   -1500 USD
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("price-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(
        py_success,
        "Python should handle price directive: {py_output}"
    );
    assert!(
        rs_success,
        "Rust should handle price directive: {rs_output}"
    );

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_pushtag_poptag_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with pushtag/poptag
    let content = r#"
option "title" "Tag Test"

2020-01-01 open Assets:Bank USD
2020-01-01 open Expenses:Food USD

pushtag #trip

2020-01-15 * "Lunch" #extra
  Expenses:Food    20 USD
  Assets:Bank

2020-01-16 * "Dinner"
  Expenses:Food    50 USD
  Assets:Bank

poptag #trip

2020-01-20 * "Home food"
  Expenses:Food    10 USD
  Assets:Bank
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("pushtag-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(
        py_success,
        "Python should handle pushtag/poptag: {py_output}"
    );
    assert!(rs_success, "Rust should handle pushtag/poptag: {rs_output}");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_arithmetic_expressions_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with arithmetic expressions in amounts
    let content = r#"
option "title" "Arithmetic Test"

2020-01-01 open Assets:Bank USD
2020-01-01 open Expenses:Food USD

2020-01-15 * "Split dinner"
  Expenses:Food    120 / 3 USD  ; 40 USD
  Assets:Bank      -40 USD

2020-01-16 * "Group lunch"
  Expenses:Food    15 + 10 USD  ; 25 USD
  Assets:Bank      -25 USD

2020-01-17 * "Multiplied"
  Expenses:Food    10 * 5 USD   ; 50 USD
  Assets:Bank      -50 USD
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("arithmetic-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(
        py_success,
        "Python should handle arithmetic expressions: {py_output}"
    );
    assert!(
        rs_success,
        "Rust should handle arithmetic expressions: {rs_output}"
    );

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_metadata_consistency() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with metadata
    let content = r#"
option "title" "Metadata Test"

2020-01-01 open Assets:Bank USD
  description: "Main checking account"
  bank: "First National"

2020-01-01 open Expenses:Food USD

2020-01-15 * "Restaurant" ^link-001
  document: "receipts/lunch.pdf"
  Expenses:Food    50 USD
    vendor: "Joe's Diner"
  Assets:Bank     -50 USD
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("metadata-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(py_success, "Python should handle metadata: {py_output}");
    assert!(rs_success, "Rust should handle metadata: {rs_output}");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_cost_and_price_annotations() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with various cost and price annotations
    let content = r#"
option "title" "Cost/Price Test"
option "operating_currency" "USD"

2020-01-01 open Assets:Stock AAPL
2020-01-01 open Assets:Cash USD
2020-01-01 open Income:Gains USD
2020-01-01 commodity AAPL
2020-01-01 commodity USD

; Buy with cost
2020-01-15 * "Buy stock"
  Assets:Stock   10 AAPL {150 USD}
  Assets:Cash   -1500 USD

; Sell with cost and price annotation
2020-06-15 * "Sell stock"
  Assets:Stock   -5 AAPL {150 USD} @ 200 USD
  Assets:Cash    1000 USD
  Income:Gains   -250 USD
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("cost-price-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(py_success, "Python should handle cost/price: {py_output}");
    assert!(rs_success, "Rust should handle cost/price: {rs_output}");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_event_and_query_directives() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with event and query directives
    let content = r#"
option "title" "Event/Query Test"

2020-01-01 open Assets:Bank USD
2020-01-01 open Expenses:Travel USD

2020-01-15 event "location" "New York"
2020-02-01 event "location" "Los Angeles"

2020-06-01 query "travel_expenses" "
  SELECT account, sum(position)
  WHERE account ~ 'Expenses:Travel'
  GROUP BY account
"

2020-01-20 * "Travel expense"
  Expenses:Travel   200 USD
  Assets:Bank
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("event-query-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(py_success, "Python should handle event/query: {py_output}");
    assert!(rs_success, "Rust should handle event/query: {rs_output}");

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_note_directive() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    // File with note directive
    let content = r#"
option "title" "Note Test"

2020-01-01 open Assets:Bank USD
2020-01-01 open Equity:Opening

2020-01-15 note Assets:Bank "Changed account number"
2020-06-01 note Assets:Bank "Switched to online banking"

2020-01-20 * "Deposit"
  Assets:Bank    1000 USD
  Equity:Opening
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("note-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let (py_success, py_output) = python_bean_check(&temp_file);
    let Some((rs_success, rs_output)) = rust_bean_check(&temp_file) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    // Both should succeed
    assert!(
        py_success,
        "Python should handle note directive: {py_output}"
    );
    assert!(rs_success, "Rust should handle note directive: {rs_output}");

    std::fs::remove_file(&temp_file).ok();
}

/// Path to beancount's canonical example.beancount file.
fn beancount_example_file() -> PathBuf {
    project_root().join("tests/fixtures/examples/example.beancount")
}

#[test]
fn test_beancount_canonical_example() {
    // This is beancount's official example.beancount file.
    // It should parse and validate without errors in rustledger.
    let path = beancount_example_file();

    if !path.exists() {
        eprintln!("Skipping: tests/fixtures/examples/example.beancount not found");
        return;
    }

    let Some((rs_success, rs_output)) = rust_bean_check(&path) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    assert!(
        rs_success,
        "Rust should validate beancount's canonical example.beancount without errors: {rs_output}"
    );
}

#[test]
fn test_beancount_canonical_example_matches_python() {
    if !python_beancount_available() {
        eprintln!("Skipping: Python beancount not available");
        return;
    }

    let path = beancount_example_file();

    if !path.exists() {
        eprintln!("Skipping: tests/fixtures/examples/example.beancount not found");
        return;
    }

    let (py_success, py_output) = python_bean_check(&path);
    let Some((rs_success, rs_output)) = rust_bean_check(&path) else {
        eprintln!("Skipping: rust bean-check binary not found");
        return;
    };

    assert!(
        py_success,
        "Python beancount should pass on its own example.beancount: {py_output}"
    );
    assert!(
        rs_success,
        "Rust should match Python on example.beancount: {rs_output}"
    );
}

#[test]
fn test_query_filename_lineno_columns_resolve() {
    // Regression: `SELECT filename, lineno` used to return NULL from the CLI
    // because the query command built the executor without a source map.
    let Some(binary) = rledger_binary() else {
        eprintln!("Skipping: rledger binary not found");
        return;
    };
    // Transaction is on line 3 (two opens precede it).
    let content = "2020-01-01 open Assets:Cash USD\n\
                   2020-01-01 open Equity:O USD\n\
                   2020-02-01 * \"p\"\n  \
                     Assets:Cash  10.00 USD\n  \
                     Equity:O\n";
    let temp_file = std::env::temp_dir().join("query-filename-lineno-test.beancount");
    std::fs::write(&temp_file, content).expect("write temp file");

    let output = Command::new(binary)
        .arg("query")
        .arg(&temp_file)
        .arg("SELECT filename, lineno WHERE flag = \"*\"")
        .output()
        .expect("run rledger query");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "query should succeed; stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    // filename resolves to the real path (was empty/NULL before the fix).
    assert!(
        stdout.contains("query-filename-lineno-test.beancount"),
        "expected the source filename in output, got:\n{stdout}"
    );
    // lineno resolves to 3 (the transaction's line).
    assert!(
        stdout
            .lines()
            .any(|l| l.contains(".beancount") && l.trim_end().ends_with('3')),
        "expected lineno 3 on the directive's row, got:\n{stdout}"
    );

    std::fs::remove_file(&temp_file).ok();
}
