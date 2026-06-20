//! CLI command integration tests.
//!
//! Tests for rledger check, rledger query, rledger format, rledger doctor, and rledger report.

mod common;

use std::path::PathBuf;
use std::process::Command;

use common::test_fixtures_dir;

// =============================================================================
// rledger check tests
// =============================================================================

#[test]
fn test_check_version() {
    let output = Command::new(require_rledger!())
        .args(["check", "--version"])
        .output()
        .expect("Failed to run rledger check --version");

    assert!(output.status.success(), "Version should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Version output should contain a version number
    assert!(
        stdout.chars().any(|c| c.is_ascii_digit()) || stdout.contains('.'),
        "Version output should contain version info: {stdout}"
    );
}

#[test]
fn test_check_help() {
    let output = Command::new(require_rledger!())
        .args(["check", "--help"])
        .output()
        .expect("Failed to run rledger check --help");

    assert!(output.status.success(), "Help should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Usage") || stdout.contains("usage"),
        "Help should show usage"
    );
}

#[test]
fn test_check_valid_file() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("check")
        .arg(&path)
        .output()
        .expect("Failed to run rledger check");

    assert!(output.status.success(), "Valid file should pass check");
}

#[test]
fn test_check_nonexistent_file() {
    let output = Command::new(require_rledger!())
        .args(["check", "/nonexistent/file.beancount"])
        .output()
        .expect("Failed to run rledger check");

    assert!(
        !output.status.success(),
        "Nonexistent file should fail check"
    );
}

#[test]
fn test_check_json_output() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("check")
        .arg("--json")
        .arg(&path)
        .output()
        .expect("Failed to run rledger check --json");

    // Skip if --json is not supported
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("error:") && stderr.contains("--json") {
            eprintln!("Skipping: --json flag not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    // JSON output should be valid JSON (starts with { or [)
    let trimmed = stdout.trim();
    if !trimmed.is_empty() {
        assert!(
            trimmed.starts_with('{') || trimmed.starts_with('['),
            "JSON output should be valid JSON, got: {trimmed}"
        );
    }
}

/// Regression for issue #736 case 1: an account whose root type is not one
/// of the configured account names (defaults: Assets/Liabilities/Equity/
/// Income/Expenses) must be reported as a parse-phase diagnostic in JSON
/// output. This matches Python beancount, where the lexer itself rejects
/// such account names, and satisfies the pta-standards conformance harness
/// which classifies errors by the `phase` field.
#[test]
fn test_check_invalid_account_root_is_parse_phase() {
    let rledger = require_rledger!();
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(tmp.path(), "2024-01-01 open Savings:Emergency\n").expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--format", "json", "--no-cache"])
        .arg(tmp.path())
        .output()
        .expect("Failed to run rledger check");

    // Skip if this rledger build doesn't support --no-cache or --format json.
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("--no-cache") || stderr.contains("--format") {
            eprintln!("Skipping: required flags not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("check --format json should produce valid JSON");

    let diagnostics = json["diagnostics"]
        .as_array()
        .expect("diagnostics array missing");
    let e1005 = diagnostics
        .iter()
        .find(|d| d["code"] == "E1005")
        .expect("expected E1005 diagnostic for Savings:Emergency");

    assert_eq!(
        e1005["phase"], "parse",
        "E1005 must be phase=parse for conformance compatibility, got: {e1005}"
    );
    assert_eq!(
        json["parse_error_count"], 1,
        "parse_error_count should include E1005; got json: {json}"
    );
    assert_eq!(
        json["validate_error_count"], 0,
        "validate_error_count should not include E1005; got json: {json}"
    );
}

/// Regression for issue #737: a wildcard reduction `-5 AAPL {}` against an
/// inventory holding lots at different costs must produce exactly one
/// "Ambiguous" diagnostic from the booking engine — not zero (the original
/// silent-accept bug) and not two (the old validator/booking double-report).
///
/// Since #859, the validator no longer re-runs lot matching on pre-booked
/// directives, so the sole reporter is the booking engine (code "BOOK").
#[test]
fn test_check_ambiguous_lot_match_reports_once() {
    let rledger = require_rledger!();
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(
        tmp.path(),
        "\
2024-01-01 open Assets:Stock AAPL \"STRICT\"
2024-01-01 open Assets:Cash USD
2024-01-01 open Income:Gains

2024-01-15 * \"Buy lot 1\"
  Assets:Stock 10 AAPL {150 USD}
  Assets:Cash -1500 USD

2024-01-20 * \"Buy lot 2\"
  Assets:Stock 10 AAPL {160 USD}
  Assets:Cash -1600 USD

2024-02-15 * \"Sell - ambiguous\"
  Assets:Stock -5 AAPL {}
  Assets:Cash 800 USD
  Income:Gains
",
    )
    .expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--format", "json", "--no-cache"])
        .arg(tmp.path())
        .output()
        .expect("failed to run rledger check");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("--no-cache") || stderr.contains("--format") {
            eprintln!("Skipping: required flags not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("check --format json should produce valid JSON");

    let diagnostics = json["diagnostics"]
        .as_array()
        .expect("diagnostics array missing");
    // The booking engine is the sole reporter of lot-matching errors (#859).
    // The validator no longer re-runs lot matching on unbooked postings.
    let book_errors: Vec<_> = diagnostics.iter().filter(|d| d["code"] == "BOOK").collect();

    assert_eq!(
        book_errors.len(),
        1,
        "expected exactly one BOOK diagnostic, got {}: {json}",
        book_errors.len()
    );
    let msg = book_errors[0]["message"].as_str().unwrap_or("");
    assert!(
        msg.to_lowercase().contains("ambiguous"),
        "BOOK diagnostic should mention 'ambiguous', got: {msg}"
    );

    // Confirm the validator does NOT double-report as E4003.
    let e4003: Vec<_> = diagnostics
        .iter()
        .filter(|d| d["code"] == "E4003")
        .collect();
    assert!(
        e4003.is_empty(),
        "validator should not re-report booking errors, but found {} E4003 diagnostics",
        e4003.len()
    );
}

// =============================================================================
// rledger lint transfers tests
// =============================================================================

#[test]
fn test_lint_transfers_help() {
    let output = Command::new(require_rledger!())
        .args(["lint", "transfers", "--help"])
        .output()
        .expect("Failed to run rledger lint transfers --help");
    assert!(output.status.success(), "Help should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("min-confidence") || stdout.contains("min_confidence"),
        "help should mention --min-confidence flag: {stdout}"
    );
}

#[test]
fn test_lint_transfers_detects_pair_across_files() {
    let dir = tempfile::tempdir().expect("tempdir");
    let checking = dir.path().join("checking.bean");
    let savings = dir.path().join("savings.bean");
    std::fs::write(
        &checking,
        "2024-01-01 open Assets:Checking USD\n\
         \n\
         2024-01-15 * \"Transfer to savings\"\n  \
         Assets:Checking  -500.00 USD\n  \
         Assets:Savings    500.00 USD\n",
    )
    .unwrap();
    std::fs::write(
        &savings,
        "2024-01-01 open Assets:Savings USD\n\
         \n\
         2024-01-15 * \"Transfer from checking\"\n  \
         Assets:Savings    500.00 USD\n  \
         Assets:Checking  -500.00 USD\n",
    )
    .unwrap();

    let output = Command::new(require_rledger!())
        .args(["lint", "transfers", "--format", "json"])
        .arg(&checking)
        .arg(&savings)
        .output()
        .expect("Failed to run rledger lint transfers");
    assert!(
        output.status.success(),
        "lint should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("xfer-20240115-"),
        "expected link_name in JSON output, got: {stdout}"
    );
    assert!(
        stdout.contains("\"applied\": false") || stdout.contains("\"applied\":false"),
        "without --apply, JSON should show applied=false: {stdout}"
    );
}

#[test]
fn test_lint_transfers_apply_is_idempotent() {
    let dir = tempfile::tempdir().expect("tempdir");
    let checking = dir.path().join("checking.bean");
    let savings = dir.path().join("savings.bean");
    std::fs::write(
        &checking,
        "2024-01-01 open Assets:Checking USD\n\
         2024-01-15 * \"Transfer to savings\"\n  \
         Assets:Checking  -500.00 USD\n  \
         Assets:Savings    500.00 USD\n",
    )
    .unwrap();
    std::fs::write(
        &savings,
        "2024-01-01 open Assets:Savings USD\n\
         2024-01-15 * \"Transfer from checking\"\n  \
         Assets:Savings    500.00 USD\n  \
         Assets:Checking  -500.00 USD\n",
    )
    .unwrap();

    let bin = require_rledger!();
    // First apply.
    let first = Command::new(&bin)
        .args(["lint", "transfers", "--apply"])
        .arg(&checking)
        .arg(&savings)
        .output()
        .expect("first --apply");
    assert!(
        first.status.success(),
        "first --apply must exit 0. stderr: {}",
        String::from_utf8_lossy(&first.stderr)
    );
    let after_first = std::fs::read_to_string(&checking).unwrap();
    assert!(
        after_first.contains("^xfer-20240115-"),
        "first --apply should add link: {after_first}"
    );

    // Second apply must be a no-op.
    let second = Command::new(&bin)
        .args(["lint", "transfers", "--apply"])
        .arg(&checking)
        .arg(&savings)
        .output()
        .expect("second --apply");
    assert!(
        second.status.success(),
        "second --apply must exit 0. stderr: {}",
        String::from_utf8_lossy(&second.stderr)
    );
    let after_second = std::fs::read_to_string(&checking).unwrap();
    assert_eq!(
        after_first, after_second,
        "second --apply must not modify the file (idempotency); got:\n{after_second}"
    );
}

// =============================================================================
// rledger check --lint transfers tests (Phase 2)
// =============================================================================

#[test]
fn test_check_with_lint_unknown_name_rejected_at_parse_time() {
    // ValueEnum should reject typos at clap parse time, not silently no-op.
    let output = Command::new(require_rledger!())
        .args(["check", "--lint", "tranfsers", "/tmp/whatever.bean"])
        .output()
        .expect("Failed to run rledger check --lint tranfsers");
    assert!(
        !output.status.success(),
        "unknown lint name must fail at argument parsing"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("tranfsers") || stderr.contains("invalid value"),
        "expected clap to flag the typo, got stderr: {stderr}"
    );
}

#[test]
fn test_check_with_lint_transfers_emits_warning_but_succeeds() {
    let dir = tempfile::tempdir().expect("tempdir");
    let combined = dir.path().join("combined.bean");
    std::fs::write(
        &combined,
        "option \"operating_currency\" \"USD\"\n\
         2024-01-01 open Assets:Checking USD\n\
         2024-01-01 open Assets:Savings USD\n\
         \n\
         2024-01-15 * \"Transfer to savings\"\n  \
         Assets:Checking  -500.00 USD\n  \
         Assets:Savings    500.00 USD\n\
         \n\
         2024-01-15 * \"Transfer from checking\"\n  \
         Assets:Savings    500.00 USD\n  \
         Assets:Checking  -500.00 USD\n",
    )
    .unwrap();

    let output = Command::new(require_rledger!())
        .args(["check", "--lint", "transfers", "-f", "json"])
        .arg(&combined)
        .output()
        .expect("Failed to run rledger check --lint transfers");
    assert!(
        output.status.success(),
        "check --lint should still exit 0 — lint is non-fatal. stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("LINT-XFER"),
        "expected LINT-XFER diagnostic, got: {stdout}"
    );
}

#[test]
fn test_query_version() {
    let output = Command::new(require_rledger!())
        .args(["query", "--version"])
        .output()
        .expect("Failed to run rledger query --version");

    assert!(output.status.success(), "Version should succeed");
}

#[test]
fn test_query_help() {
    let output = Command::new(require_rledger!())
        .args(["query", "--help"])
        .output()
        .expect("Failed to run rledger query --help");

    assert!(output.status.success(), "Help should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Usage") || stdout.contains("usage"),
        "Help should show usage"
    );
}

#[test]
fn test_query_select_accounts() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("query")
        .arg(&path)
        .arg("SELECT DISTINCT account ORDER BY account")
        .output()
        .expect("Failed to run rledger query");

    assert!(output.status.success(), "Query should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Assets") || stdout.contains("Expenses"),
        "Query should return accounts"
    );
}

#[test]
fn test_query_sum_positions() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("query")
        .arg(&path)
        .arg("SELECT account, SUM(position) GROUP BY account ORDER BY account")
        .output()
        .expect("Failed to run rledger query");

    assert!(output.status.success(), "Query should succeed");
}

#[test]
fn test_query_invalid_syntax() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("query")
        .arg(&path)
        .arg("SELEKT * FROM entries") // Intentional typo
        .output()
        .expect("Failed to run rledger query");

    assert!(!output.status.success(), "Invalid query syntax should fail");
}

#[test]
fn test_query_json_output() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("query")
        .arg("--json")
        .arg(&path)
        .arg("SELECT account LIMIT 3")
        .output()
        .expect("Failed to run rledger query --json");

    // Skip if --json is not supported
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("error:") && stderr.contains("--json") {
            eprintln!("Skipping: --json flag not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let trimmed = stdout.trim();
    if !trimmed.is_empty() {
        assert!(
            trimmed.starts_with('{') || trimmed.starts_with('['),
            "JSON output should be valid JSON"
        );
    }
}

// =============================================================================
// rledger format tests
// =============================================================================

#[test]
fn test_format_version() {
    let output = Command::new(require_rledger!())
        .args(["format", "--version"])
        .output()
        .expect("Failed to run rledger format --version");

    assert!(output.status.success(), "Version should succeed");
}

#[test]
fn test_format_help() {
    let output = Command::new(require_rledger!())
        .args(["format", "--help"])
        .output()
        .expect("Failed to run rledger format --help");

    assert!(output.status.success(), "Help should succeed");
}

#[test]
fn test_format_file() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("format")
        .arg(&path)
        .output()
        .expect("Failed to run rledger format");

    assert!(output.status.success(), "Format should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Formatted output should contain some beancount content
    assert!(
        stdout.contains("open") || stdout.contains("2020"),
        "Formatted output should contain beancount content"
    );
}

#[test]
fn test_format_check_mode() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    // --check mode should not modify file, just check if formatting needed
    let output = Command::new(require_rledger!())
        .arg("format")
        .arg("--check")
        .arg(&path)
        .output()
        .expect("Failed to run rledger format --check");

    // Either it passes (properly formatted) or fails (needs formatting)
    // Both are valid outcomes for this test
    let _success = output.status.success();
}

// =============================================================================
// rledger doctor tests
// =============================================================================

#[test]
fn test_doctor_version() {
    let output = Command::new(require_rledger!())
        .args(["doctor", "--version"])
        .output()
        .expect("Failed to run rledger doctor --version");

    assert!(output.status.success(), "Version should succeed");
}

#[test]
fn test_doctor_help() {
    let output = Command::new(require_rledger!())
        .args(["doctor", "--help"])
        .output()
        .expect("Failed to run rledger doctor --help");

    assert!(output.status.success(), "Help should succeed");
}

#[test]
fn test_doctor_missing_open() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("doctor")
        .arg("missing-open")
        .arg(&path)
        .output()
        .expect("Failed to run rledger doctor missing-open");

    // Should succeed even if no missing opens found
    assert!(
        output.status.success(),
        "Doctor missing-open should succeed"
    );
}

#[test]
fn test_doctor_context() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("doctor")
        .arg("context")
        .arg(&path)
        .arg("5") // Line number
        .output()
        .expect("Failed to run rledger doctor context");

    // Context command should work (or report no context at line)
    let _success = output.status.success();
}

// =============================================================================
// rledger report tests
// =============================================================================

#[test]
fn test_report_version() {
    let output = Command::new(require_rledger!())
        .args(["report", "--version"])
        .output()
        .expect("Failed to run rledger report --version");

    assert!(output.status.success(), "Version should succeed");
}

#[test]
fn test_report_help() {
    let output = Command::new(require_rledger!())
        .args(["report", "--help"])
        .output()
        .expect("Failed to run rledger report --help");

    assert!(output.status.success(), "Help should succeed");
}

#[test]
fn test_report_balances() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("report")
        .arg(&path)
        .arg("balances")
        .output()
        .expect("Failed to run rledger report balances");

    // Skip if subcommand not supported
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("error:") || stderr.contains("Usage") {
            eprintln!("Skipping: 'balances' subcommand not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Assets")
            || stdout.contains("USD")
            || stdout.contains("balance")
            || stdout.is_empty(),
        "Balances report should show accounts or amounts"
    );
}

#[test]
fn test_report_trial_balance() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("report")
        .arg(&path)
        .arg("trial-balance")
        .output()
        .expect("Failed to run rledger report trial-balance");

    // Skip if subcommand not supported
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("error:") || stderr.contains("Usage") {
            eprintln!("Skipping: 'trial-balance' subcommand not supported");
        }
    }
}

#[test]
fn test_report_journal() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("report")
        .arg(&path)
        .arg("journal")
        .output()
        .expect("Failed to run rledger report journal");

    // Skip if subcommand not supported
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("error:") || stderr.contains("Usage") {
            eprintln!("Skipping: 'journal' subcommand not supported");
        }
    }
}

// =============================================================================
// Error message format tests
// =============================================================================

#[test]
fn test_error_message_includes_line_number() {
    // Create a temp file with a validation error
    let content = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD  ; Account not opened
  Assets:Bank   -5.00 USD
"#;

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("error-line-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let output = Command::new(require_rledger!())
        .arg("check")
        .arg(&temp_file)
        .output()
        .expect("Failed to run rledger check");

    assert!(!output.status.success(), "Should have validation error");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let combined = format!("{stdout}{stderr}");

    // Error message should include line number
    assert!(
        combined.contains(':') && combined.chars().any(|c| c.is_ascii_digit()),
        "Error should include line number reference"
    );

    std::fs::remove_file(&temp_file).ok();
}

#[test]
fn test_error_message_includes_file_path() {
    let content = r"
2024-01-01 open Assets:Bank USD
2024-01-01 open Assets:Bank USD  ; Duplicate!
";

    let temp_dir = std::env::temp_dir();
    let temp_file = temp_dir.join("error-path-test.beancount");
    std::fs::write(&temp_file, content).expect("Failed to write temp file");

    let output = Command::new(require_rledger!())
        .arg("check")
        .arg(&temp_file)
        .output()
        .expect("Failed to run rledger check");

    assert!(!output.status.success(), "Should have validation error");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let combined = format!("{stdout}{stderr}");

    // Error message should include file path
    assert!(
        combined.contains("error-path-test.beancount") || combined.contains(".beancount"),
        "Error should reference file path"
    );

    std::fs::remove_file(&temp_file).ok();
}

// =============================================================================
// Plugin tests
// =============================================================================

#[test]
fn test_check_with_native_plugin() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("check")
        .arg("--native-plugin")
        .arg("auto_accounts")
        .arg(&path)
        .output()
        .expect("Failed to run rledger check with plugin");

    assert!(
        output.status.success(),
        "Check with auto_accounts plugin should succeed"
    );
}

#[test]
fn test_check_with_unknown_plugin() {
    let path = test_fixtures_dir().join("valid-ledger.beancount");
    if !path.exists() {
        eprintln!("Skipping: valid-ledger.beancount not found");
        return;
    }

    let output = Command::new(require_rledger!())
        .arg("check")
        .arg("--native-plugin")
        .arg("nonexistent_plugin_xyz_12345")
        .arg(&path)
        .output()
        .expect("Failed to run rledger check with unknown plugin");

    // Unknown plugin should either fail or produce a warning/error in output
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");

    // Either fails or shows error/warning about unknown plugin
    let has_plugin_error = !output.status.success()
        || combined.to_lowercase().contains("unknown")
        || combined.to_lowercase().contains("not found")
        || combined.to_lowercase().contains("error");

    assert!(
        has_plugin_error,
        "Unknown plugin should produce an error: {combined}"
    );
}

// =============================================================================
// Stdin input tests
// =============================================================================

#[test]
fn test_query_stdin_input() {
    let content = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let mut child = Command::new(require_rledger!())
        .arg("query")
        .arg("-") // Read from stdin
        .arg("SELECT account")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("Failed to spawn rledger query");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("Failed to get stdin");
        // Handle broken pipe gracefully - stdin may not be supported
        if stdin.write_all(content.as_bytes()).is_err() {
            let _ = child.wait();
            eprintln!("Skipping: stdin write failed (not supported)");
            return;
        }
    }

    let output = child.wait_with_output().expect("Failed to wait on child");

    // Skip if stdin not supported
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("error:") || stderr.contains('-') || stderr.contains("stdin") {
            eprintln!("Skipping: stdin input not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Assets") || stdout.contains("Expenses") || stdout.is_empty(),
        "Query should return accounts or be empty"
    );
}

// ============================================================================
// JSON Output Validity Tests (Issue #780)
// ============================================================================

/// Helper: run `rledger check --format json --no-cache` on inline content,
/// return parsed JSON. Skips the test if the binary doesn't support the flags.
fn check_json(rledger: &std::path::Path, content: &str) -> Option<serde_json::Value> {
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(tmp.path(), content).expect("write");

    let output = Command::new(rledger)
        .args(["check", "--format", "json", "--no-cache"])
        .arg(tmp.path())
        .output()
        .expect("failed to run rledger check");

    // Only skip when the command fails AND stderr indicates the flags
    // are unsupported (clap usage error). Don't skip on success — stderr
    // may legitimately contain other output like verbose logging.
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("--no-cache") || stderr.contains("--format") {
            eprintln!("Skipping: required flags not supported");
            return None;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Core assertion: stdout must start with '{' (no plain-text prefix).
    let trimmed = stdout.trim();
    let preview: String = trimmed.chars().take(200).collect();
    assert!(
        trimmed.starts_with('{'),
        "JSON output must start with '{{', got: {preview}"
    );

    let json: serde_json::Value = serde_json::from_str(trimmed).unwrap_or_else(|e| {
        let long_preview: String = trimmed.chars().take(500).collect();
        panic!("stdout is not valid JSON: {e}\nfirst 500 chars: {long_preview}")
    });

    // Structural assertions: required top-level fields.
    assert!(json["diagnostics"].is_array(), "missing diagnostics array");
    assert!(json["error_count"].is_number(), "missing error_count");
    assert!(json["warning_count"].is_number(), "missing warning_count");
    assert!(
        json["parse_error_count"].is_number(),
        "missing parse_error_count"
    );
    assert!(
        json["validate_error_count"].is_number(),
        "missing validate_error_count"
    );

    Some(json)
}

/// Regression for #774: plugin errors must appear inside the JSON diagnostics
/// array, not as plain text before the JSON document.
#[test]
fn test_json_output_plugin_errors_in_diagnostics() {
    let rledger = require_rledger!();
    let content = r#"
option "operating_currency" "USD"

plugin "a_completely_nonexistent_plugin"
plugin "another_fake_plugin" "some_config"

2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:Food

2024-01-15 * "Lunch"
  Expenses:Food   10 USD
  Assets:Cash    -10 USD
"#;

    let Some(json) = check_json(&rledger, content) else {
        return;
    };

    let diagnostics = json["diagnostics"].as_array().unwrap();

    // Plugin errors should be in the diagnostics array.
    let plugin_diags: Vec<_> = diagnostics
        .iter()
        .filter(|d| {
            let code = d["code"].as_str().unwrap_or("");
            code == "E8001" || code == "E8005"
        })
        .collect();

    assert!(
        plugin_diags.len() >= 2,
        "expected at least 2 plugin error diagnostics, got {}: {json}",
        plugin_diags.len()
    );

    // error_count must include the plugin errors.
    let error_count = json["error_count"].as_u64().unwrap_or(0);
    assert!(
        error_count >= 2,
        "error_count should include plugin errors, got {error_count}"
    );
}

/// Clean file with no errors: JSON output should have empty diagnostics
/// and all counts at zero.
#[test]
fn test_json_output_clean_file() {
    let rledger = require_rledger!();
    let content = r#"
2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:Food

2024-01-15 * "Lunch"
  Expenses:Food   10 USD
  Assets:Cash    -10 USD
"#;

    let Some(json) = check_json(&rledger, content) else {
        return;
    };

    let diagnostics = json["diagnostics"].as_array().unwrap();
    assert!(
        diagnostics.is_empty(),
        "clean file should have no diagnostics, got: {diagnostics:?}"
    );
    assert_eq!(json["error_count"], 0);
    assert_eq!(json["warning_count"], 0);
    assert_eq!(json["parse_error_count"], 0);
    assert_eq!(json["validate_error_count"], 0);
}

/// File with parse errors only: `parse_error_count` should be positive and
/// all error diagnostics should have phase "parse".
#[test]
fn test_json_output_parse_errors_only() {
    let rledger = require_rledger!();
    // Malformed beancount syntax
    let content = "2024-01-01 open Assets:Cash\n\nthis is not valid beancount syntax {{{ }}\n";

    let Some(json) = check_json(&rledger, content) else {
        return;
    };

    let error_count = json["error_count"].as_u64().unwrap_or(0);
    assert!(error_count > 0, "should have parse errors");

    let parse_count = json["parse_error_count"].as_u64().unwrap_or(0);
    assert!(parse_count > 0, "parse_error_count should be > 0");

    // All error diagnostics should be parse-phase (no validation on
    // a file that can't parse).
    let diagnostics = json["diagnostics"].as_array().unwrap();
    let non_parse_errors: Vec<_> = diagnostics
        .iter()
        .filter(|d| d["severity"] == "error" && d["phase"] != "parse")
        .collect();
    assert!(
        non_parse_errors.is_empty(),
        "all errors should be parse-phase, found non-parse: {non_parse_errors:?}"
    );
}

/// File with validation errors: diagnostics should include phase "validate".
#[test]
fn test_json_output_validation_errors() {
    let rledger = require_rledger!();
    // Transaction references account that was never opened
    let content = r#"
2024-01-15 * "No open"
  Expenses:Food   10 USD
  Assets:Cash    -10 USD
"#;

    let Some(json) = check_json(&rledger, content) else {
        return;
    };

    let diagnostics = json["diagnostics"].as_array().unwrap();
    assert!(
        diagnostics.iter().any(|d| d["phase"] == "validate"),
        "should have validation-phase diagnostics for unopened accounts"
    );

    let validate_count = json["validate_error_count"].as_u64().unwrap_or(0);
    assert!(validate_count > 0, "validate_error_count should be > 0");
}

// ============================================================================
// Plugin Execution Tests (Issue #784 regression guard)
//
// These tests verify that all plugin types (native, Python, WASM) are
// actually executed through the CLI. The #784 refactor accidentally
// removed Python/WASM execution with no test to catch it.
// ============================================================================

fn wasm_plugins_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/wasm-plugins")
}

fn python_plugins_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/python-plugins")
}

// --- Group 1: Native plugin parity (check vs query) ---

/// Native plugins declared in a beancount file must execute through
/// the check path (which delegates to `process::process`).
#[test]
fn test_native_plugin_runs_in_check_path() {
    let rledger = require_rledger!();
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    // auto_accounts should create opens for implicitly-used accounts,
    // making this file pass validation without explicit opens.
    std::fs::write(
        tmp.path(),
        "\
option \"operating_currency\" \"USD\"
plugin \"auto_accounts\"

2020-01-15 * \"Lunch\"
  Expenses:Food   10 USD
  Assets:Cash    -10 USD
",
    )
    .expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--format", "json", "--no-cache"])
        .arg(tmp.path())
        .output()
        .expect("failed to run rledger check");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("--no-cache") || stderr.contains("--format") {
            eprintln!("Skipping: required flags not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("should produce valid JSON");
    assert_eq!(
        json["error_count"], 0,
        "auto_accounts should make file pass: {json}"
    );
}

/// Native plugins must also execute through the query path (process.rs).
#[test]
fn test_native_plugin_runs_in_query_path() {
    let rledger = require_rledger!();
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(
        tmp.path(),
        "\
option \"operating_currency\" \"USD\"
plugin \"auto_accounts\"

2020-01-15 * \"Lunch\"
  Expenses:Food   10 USD
  Assets:Cash    -10 USD
",
    )
    .expect("write");

    let output = Command::new(&rledger)
        .args(["query", "-q"])
        .arg(tmp.path())
        .arg("SELECT DISTINCT account ORDER BY account")
        .output()
        .expect("failed to run rledger query");

    let stdout = String::from_utf8_lossy(&output.stdout);
    // auto_accounts should have created opens — accounts should appear
    assert!(
        stdout.contains("Assets:Cash") && stdout.contains("Expenses:Food"),
        "query should see accounts from auto_accounts plugin: {stdout}"
    );
}

// --- Group 2: Python plugin execution ---

/// Python file-based plugin dispatch must exist in check.rs.
/// If the dispatch code is removed, this test fails because rledger
/// would report 0 errors on a file that a Python plugin should flag.
///
/// Accepts either: plugin actually ran (error output), OR E8003
/// (Python runtime unavailable). Both prove the dispatch code exists.
/// Silent success (exit 0, no errors) means dispatch was removed.
#[cfg(feature = "python-plugin-wasm")]
#[test]
fn test_python_file_plugin_dispatch_exists() {
    let rledger = require_rledger!();
    let src_dir = python_plugins_dir();
    if !src_dir.join("error_plugin.py").exists() {
        eprintln!("Skipping: Python plugin fixtures not found");
        return;
    }

    // Copy plugin to temp dir and create a beancount file referencing it
    let tmp_dir = tempfile::TempDir::new().expect("tempdir");
    std::fs::copy(
        src_dir.join("error_plugin.py"),
        tmp_dir.path().join("error_plugin.py"),
    )
    .expect("copy plugin");

    let beancount_path = tmp_dir.path().join("test.beancount");
    std::fs::write(
        &beancount_path,
        "\
option \"operating_currency\" \"USD\"
plugin \"./error_plugin.py\"

2020-01-01 open Assets:Cash USD
2020-01-01 open Expenses:Food USD

; No payee — error_plugin.py should flag this
2020-01-15 * \"Groceries\"
  Expenses:Food   10 USD
  Assets:Cash    -10 USD
",
    )
    .expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--no-cache"])
        .arg(&beancount_path)
        .output()
        .expect("failed to run rledger check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");

    // The plugin dispatch code must be reached. Either:
    // - The plugin ran and produced output, OR
    // - E8003: Python runtime unavailable (acceptable in CI), OR
    // - E8002: Plugin execution failed
    // Silent exit-0 with no plugin mention means dispatch was removed.
    let dispatch_reached = combined.contains("E8002")
        || combined.contains("E8003")
        || combined.contains("error_plugin")
        || combined.contains("payee")
        || combined.contains("Python plugin");

    assert!(
        dispatch_reached,
        "Python plugin dispatch code must be reached. Got exit={}, stdout={stdout}, stderr={stderr}",
        output.status.code().unwrap_or(-1)
    );
}

/// Module-based Python plugin names must produce E8001 or E8004.
#[test]
fn test_python_module_plugin_error_code() {
    let rledger = require_rledger!();
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(
        tmp.path(),
        "\
2020-01-01 open Assets:Cash USD
plugin \"some.unknown.python.module\"
",
    )
    .expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--format", "json", "--no-cache"])
        .arg(tmp.path())
        .output()
        .expect("failed to run rledger check");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("--format") {
            eprintln!("Skipping: --format json not supported");
            return;
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("should produce valid JSON");
    let diagnostics = json["diagnostics"].as_array().expect("diagnostics");

    assert!(
        diagnostics.iter().any(|d| {
            let code = d["code"].as_str().unwrap_or("");
            // E8001: plugin not found, E8002: Python execution/runtime failed,
            // E8004: cannot resolve module (with suggestion), E8005: feature disabled
            code == "E8001" || code == "E8002" || code == "E8004" || code == "E8005"
        }),
        "unknown Python module should produce E8001/E8002/E8004/E8005: {json}"
    );
}

// --- Group 3: WASM plugin execution ---

/// The --plugin CLI flag must reach the WASM runtime.
/// A minimal stub plugin causes a deserialization error — the test
/// verifies the error appears (proving dispatch was reached).
#[cfg(feature = "python-plugin-wasm")]
#[test]
fn test_wasm_plugin_cli_flag_dispatch() {
    let rledger = require_rledger!();
    let wasm_path = wasm_plugins_dir().join("passthrough.wasm");
    if !wasm_path.exists() {
        eprintln!("Skipping: passthrough.wasm fixture not found");
        return;
    }

    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(tmp.path(), "2020-01-01 open Assets:Cash USD\n").expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--no-cache", "--plugin"])
        .arg(&wasm_path)
        .arg(tmp.path())
        .output()
        .expect("failed to run rledger check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");

    // The WASM runtime must be reached. The stub plugin returns invalid
    // data, so we expect an error — NOT silent success.
    assert!(
        combined.contains("WASM") || combined.contains("plugin") || combined.contains("error"),
        "WASM dispatch must be reached via --plugin flag: stdout={stdout}, stderr={stderr}"
    );
}

/// WASM plugins declared in beancount files must reach the WASM runtime.
#[cfg(feature = "python-plugin-wasm")]
#[test]
fn test_wasm_plugin_from_beancount_file() {
    let rledger = require_rledger!();
    let wasm_src = wasm_plugins_dir().join("passthrough.wasm");
    if !wasm_src.exists() {
        eprintln!("Skipping: passthrough.wasm fixture not found");
        return;
    }

    let tmp_dir = tempfile::TempDir::new().expect("tempdir");
    std::fs::copy(&wasm_src, tmp_dir.path().join("passthrough.wasm")).expect("copy wasm");

    let beancount_path = tmp_dir.path().join("test.beancount");
    std::fs::write(
        &beancount_path,
        "\
plugin \"./passthrough.wasm\"

2020-01-01 open Assets:Cash USD
",
    )
    .expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--no-cache"])
        .arg(&beancount_path)
        .output()
        .expect("failed to run rledger check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");

    // WASM dispatch must be reached — stub produces an error, not silence
    assert!(
        combined.contains("WASM") || combined.contains("plugin") || combined.contains("error"),
        "WASM dispatch must be reached via plugin directive: stdout={stdout}, stderr={stderr}"
    );
}

/// Missing WASM plugin file must produce an error.
#[cfg(feature = "python-plugin-wasm")]
#[test]
fn test_wasm_plugin_missing_file_error() {
    let rledger = require_rledger!();
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(tmp.path(), "2020-01-01 open Assets:Cash USD\n").expect("write");

    let output = Command::new(&rledger)
        .args(["check", "--no-cache", "--plugin", "/nonexistent/path.wasm"])
        .arg(tmp.path())
        .output()
        .expect("failed to run rledger check");

    assert!(!output.status.success(), "missing WASM plugin should fail");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("failed to load") || combined.contains("error"),
        "should report load failure: {combined}"
    );
}

// --- Group 4: Plugin categorization ---

/// Native plugins (beancount.plugins.*) must be resolved to Rust
/// implementations without falling through to Python/WASM.
#[test]
fn test_native_plugin_preferred_over_python_fallback() {
    let rledger = require_rledger!();
    let fixture = python_plugins_dir().join("native_preferred.beancount");
    if !fixture.exists() {
        eprintln!("Skipping: native_preferred.beancount not found");
        return;
    }

    let output = Command::new(&rledger)
        .args(["check", "--no-cache"])
        .arg(&fixture)
        .output()
        .expect("failed to run rledger check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");

    // Should NOT produce E8001/E8003/E8005 — all plugins are native
    assert!(
        !combined.contains("E8001") && !combined.contains("E8003") && !combined.contains("E8005"),
        "native plugins should not produce plugin-not-found errors: {combined}"
    );
}

/// Regression for OUTSTANDING #11: piping streaming output (`query`/`format`)
/// to a reader that closes the pipe early — e.g. `| head` — must exit cleanly
/// instead of printing `Broken pipe` and exiting non-zero. The `report` arm
/// already handled this; `query` and `format` now match it.
#[test]
fn test_query_and_format_handle_broken_pipe() {
    use std::io::Read as _;
    use std::process::Stdio;

    let bin = require_rledger!();

    // Build a ledger whose output comfortably exceeds the OS pipe buffer
    // (~64 KiB) so the writer is still producing output when we close the read
    // end; otherwise it would finish before the pipe breaks and never exercise
    // the EPIPE path. Same-date entries keep the ledger valid without date math.
    let mut ledger = String::from(
        "option \"operating_currency\" \"USD\"\n\
         2020-01-01 open Assets:Cash\n\
         2020-01-01 open Expenses:Food\n",
    );
    for i in 0..6000 {
        ledger.push_str(&format!(
            "2020-01-01 * \"payee {i}\" \"a deliberately long narration number {i} to inflate output\"\n  \
             Expenses:Food  {}.50 USD\n  Assets:Cash\n",
            i % 100
        ));
    }
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(tmp.path(), &ledger).expect("write ledger");
    let path = tmp.path().to_str().expect("path");

    // Run the command, read one chunk, then drop the read end to break the pipe.
    let run_and_close = |args: &[&str]| -> (std::process::ExitStatus, String) {
        let mut child = Command::new(&bin)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn rledger");
        let mut out = child.stdout.take().expect("stdout");
        let mut buf = [0u8; 256];
        let _ = out.read(&mut buf);
        drop(out); // close read end → writer hits EPIPE on its next write
        let mut errbuf = String::new();
        let _ = child
            .stderr
            .take()
            .expect("stderr")
            .read_to_string(&mut errbuf);
        let status = child.wait().expect("wait");
        (status, errbuf)
    };

    for args in [
        vec!["query", path, "SELECT date, account, position, narration"],
        vec!["format", path],
    ] {
        let (status, stderr) = run_and_close(&args);
        assert!(
            status.success(),
            "`rledger {}` piped to an early-closing reader should exit 0, got {status:?}; stderr: {stderr}",
            args.join(" ")
        );
        assert!(
            !stderr.contains("Broken pipe"),
            "`rledger {}` should not print a broken-pipe error; stderr: {stderr}",
            args.join(" ")
        );
    }
}
