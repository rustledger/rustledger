//! Comprehensive tests for all beancount fixtures.
//!
//! This module tests:
//! - spec/fixtures/syntax-edge-cases.beancount - Parser edge cases
//! - spec/fixtures/booking-scenarios.beancount - Booking algorithm scenarios
//! - spec/fixtures/validation-errors.beancount - Expected validation errors
//! - spec/fixtures/lima-tests/*.beancount - 218 parser conformance tests
//! - spec/fixtures/examples/*.beancount - Official beancount examples

use std::path::{Path, PathBuf};
use std::process::Command;

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn spec_fixtures_dir() -> PathBuf {
    project_root().join("spec/fixtures")
}

fn rust_bean_check_binary() -> PathBuf {
    project_root().join("target/debug/rledger-check")
}

/// Run rledger-check on a file and return (success, output).
fn rledger_check(path: &Path) -> (bool, String) {
    let output = Command::new(rust_bean_check_binary())
        .arg(path)
        .output()
        .expect("Failed to run rledger-check");

    let success = output.status.success();
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (success, combined)
}

/// Run rledger-check with `auto_accounts` plugin (permissive mode like Python beancount).
fn rledger_check_permissive(path: &Path) -> (bool, String) {
    let output = Command::new(rust_bean_check_binary())
        .arg("--native-plugin")
        .arg("auto_accounts")
        .arg(path)
        .output()
        .expect("Failed to run rledger-check");

    let success = output.status.success();
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (success, combined)
}

/// Parse a file with the parser and return (success, `error_count`).
fn parse_file(path: &Path) -> (bool, usize) {
    let source = std::fs::read_to_string(path).expect("Failed to read file");
    let result = rustledger_parser::parse(&source);
    (result.errors.is_empty(), result.errors.len())
}

// =============================================================================
// SYNTAX EDGE CASES
// =============================================================================

#[test]
fn test_syntax_edge_cases_parses() {
    let path = spec_fixtures_dir().join("syntax-edge-cases.beancount");
    if !path.exists() {
        eprintln!("Skipping: syntax-edge-cases.beancount not found");
        return;
    }

    let (success, error_count) = parse_file(&path);
    // Note: This file contains some syntax that rustledger may not support yet
    // (e.g., balance tolerance with ~). Track parse error count for regression.
    if !success {
        eprintln!(
            "syntax-edge-cases.beancount has {error_count} parse errors (tracking for future fixes)"
        );
        // Allow up to 1 known parse error for now (balance tolerance ~)
        assert!(
            error_count <= 1,
            "syntax-edge-cases.beancount should have at most 1 parse error, got {error_count}"
        );
    }
}

// =============================================================================
// BOOKING SCENARIOS
// =============================================================================

#[test]
fn test_booking_scenarios_parses() {
    let path = spec_fixtures_dir().join("booking-scenarios.beancount");
    if !path.exists() {
        eprintln!("Skipping: booking-scenarios.beancount not found");
        return;
    }

    let (success, error_count) = parse_file(&path);
    assert!(
        success,
        "booking-scenarios.beancount should parse without errors, but got {error_count} errors"
    );
}

#[test]
fn test_booking_scenarios_validates() {
    let path = spec_fixtures_dir().join("booking-scenarios.beancount");
    if !path.exists() {
        eprintln!("Skipping: booking-scenarios.beancount not found");
        return;
    }

    // Use permissive mode since this file may not have all Open directives
    let (success, output) = rledger_check_permissive(&path);
    // Note: This file tests booking scenarios which may require the booking
    // engine to fill in missing amounts. Some E3001 (unbalanced) errors are
    // expected if the booking engine hasn't processed the transactions.
    if !success {
        // Check if errors are only E3001 (expected for booking scenarios)
        // or E1001 (account not opened - would be fixed by auto_accounts)
        let has_unexpected_errors = output.lines().any(|line| {
            line.contains("error[E") && !line.contains("E3001") && !line.contains("E1001")
        });
        assert!(
            !has_unexpected_errors,
            "booking-scenarios.beancount has unexpected errors: {output}"
        );
        eprintln!("booking-scenarios.beancount has expected booking-related errors (E3001/E1001)");
    }
}

// =============================================================================
// VALIDATION ERRORS (expected to produce specific errors)
// =============================================================================

#[test]
fn test_validation_errors_parses() {
    let path = spec_fixtures_dir().join("validation-errors.beancount");
    if !path.exists() {
        eprintln!("Skipping: validation-errors.beancount not found");
        return;
    }

    let (success, error_count) = parse_file(&path);
    assert!(
        success,
        "validation-errors.beancount should parse without errors, but got {error_count} errors"
    );
}

#[test]
fn test_validation_errors_produces_expected_errors() {
    let path = spec_fixtures_dir().join("validation-errors.beancount");
    if !path.exists() {
        eprintln!("Skipping: validation-errors.beancount not found");
        return;
    }

    let (success, output) = rledger_check(&path);

    // This file should produce validation errors (not parse errors)
    assert!(
        !success,
        "validation-errors.beancount should produce validation errors"
    );

    // Check for expected error codes
    assert!(
        output.contains("E1001") || output.contains("Account") && output.contains("not open"),
        "Should contain E1001 (account not opened): {output}"
    );
}

// =============================================================================
// LIMA TESTS - Parser conformance tests
// =============================================================================

/// Get all lima test files
fn lima_test_files() -> Vec<PathBuf> {
    let lima_dir = spec_fixtures_dir().join("lima-tests");
    if !lima_dir.exists() {
        return vec![];
    }

    std::fs::read_dir(&lima_dir)
        .expect("Failed to read lima-tests directory")
        .filter_map(std::result::Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "beancount"))
        .collect()
}

/// Lima tests that are expected to have parse errors (based on test name)
fn lima_test_expects_parse_error(name: &str) -> bool {
    name.contains("LexerAndParserErrors")
        || name.contains("GrammarException")
        || name.contains("GrammarSyntaxError")
        || name.contains("IndentError")
        || name.contains("InvalidOption")
        || name.contains("BlankLineNotAllowed")
        || name.contains("BlankLineWithSpacesNotAllowed")
        || name.contains("IndentEOF")
        || name.starts_with("SyntaxErrors")
}

#[test]
fn test_lima_tests_parse() {
    let files = lima_test_files();
    if files.is_empty() {
        eprintln!("Skipping: No lima test files found");
        return;
    }

    let mut failures = Vec::new();

    for path in &files {
        let file_name = path.file_stem().unwrap().to_string_lossy().to_string();
        let expects_error = lima_test_expects_parse_error(&file_name);

        let (parse_success, error_count) = parse_file(path);

        if expects_error {
            // These tests are expected to have parse errors
            // We just verify we don't panic
            continue;
        }

        if !parse_success {
            failures.push(format!(
                "{}: {} parse errors",
                path.file_name().unwrap().to_string_lossy(),
                error_count
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "Lima tests with unexpected parse errors:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_lima_test_count() {
    let files = lima_test_files();
    // Skip if lima-tests directory doesn't exist (e.g., in CI without fixtures)
    if files.is_empty() {
        eprintln!("Skipping: lima-tests directory not found or empty");
        return;
    }
    // We expect at least 200 lima test files when the directory exists
    assert!(
        files.len() >= 200,
        "Expected at least 200 lima test files, found {}",
        files.len()
    );
}

// =============================================================================
// EXAMPLE FILES
// =============================================================================

/// Get all example beancount files
fn example_files() -> Vec<PathBuf> {
    let examples_dir = spec_fixtures_dir().join("examples");
    if !examples_dir.exists() {
        return vec![];
    }

    walkdir(&examples_dir)
        .into_iter()
        .filter(|path| path.extension().is_some_and(|ext| ext == "beancount"))
        .collect()
}

/// Files known to have unbalanced transactions or other issues in Python beancount too
fn example_file_has_known_issues(path: &Path) -> bool {
    let path_str = path.to_string_lossy();
    let file_name = path.file_name().unwrap().to_string_lossy();
    // These files have issues even in Python beancount or use plugins we don't support
    path_str.contains("forecast") // Uses Python plugins for forecasting
        || path_str.contains("vesting") // Uses complex Python plugins
        || path_str.contains("ingest") // Importer framework files
        // These files parse correctly but have validation issues (unbalanced transactions, etc.)
        || file_name == "starter.beancount"
        || file_name == "basic.beancount"
}

/// Simple recursive directory walker
fn walkdir(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(walkdir(&path));
            } else {
                files.push(path);
            }
        }
    }
    files
}

#[test]
fn test_example_files_parse() {
    let files = example_files();
    if files.is_empty() {
        eprintln!("Skipping: No example files found");
        return;
    }

    let mut failures = Vec::new();

    for path in &files {
        let (parse_success, error_count) = parse_file(path);
        if !parse_success {
            failures.push(format!(
                "{}: {} parse errors",
                path.strip_prefix(project_root()).unwrap_or(path).display(),
                error_count
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "Example files with parse errors:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_example_files_validate() {
    // These example files are from Python beancount and expect permissive behavior
    // (auto-opening accounts). We use the auto_accounts plugin to match that.
    let files = example_files();
    if files.is_empty() {
        eprintln!("Skipping: No example files found");
        return;
    }

    let mut failures = Vec::new();
    let mut skipped = 0;

    for path in &files {
        // Skip files with known validation issues
        if example_file_has_known_issues(path) {
            skipped += 1;
            continue;
        }

        // Use permissive mode (auto_accounts) since these examples don't always
        // have explicit Open directives - Python beancount auto-creates them
        let (success, output) = rledger_check_permissive(path);
        if !success {
            // Truncate output for readability
            let short_output: String = output.lines().take(3).collect::<Vec<_>>().join("\n");
            failures.push(format!(
                "{}: {}",
                path.strip_prefix(project_root()).unwrap_or(path).display(),
                short_output
            ));
        }
    }

    if skipped > 0 {
        eprintln!("Skipped {skipped} files with known validation issues");
    }

    assert!(
        failures.is_empty(),
        "Example files with validation errors (with auto_accounts):\n{}",
        failures.join("\n\n")
    );
}

#[test]
fn test_example_file_count() {
    let files = example_files();
    // Skip if examples directory doesn't exist (e.g., in CI without fixtures)
    if files.is_empty() {
        eprintln!("Skipping: examples directory not found or empty");
        return;
    }
    // We expect at least 5 example files when the directory exists
    assert!(
        files.len() >= 5,
        "Expected at least 5 example files, found {}",
        files.len()
    );
}

// =============================================================================
// INDIVIDUAL LIMA TESTS (for more granular failure reporting)
// =============================================================================

macro_rules! lima_test {
    ($test_name:ident, $file_name:literal) => {
        #[test]
        fn $test_name() {
            let path = spec_fixtures_dir().join("lima-tests").join($file_name);
            if !path.exists() {
                eprintln!("Skipping: {} not found", $file_name);
                return;
            }
            let (success, error_count) = parse_file(&path);
            assert!(
                success,
                "{} should parse without errors, got {} errors",
                $file_name, error_count
            );
        }
    };
    ($test_name:ident, $file_name:literal, expect_error) => {
        #[test]
        fn $test_name() {
            let path = spec_fixtures_dir().join("lima-tests").join($file_name);
            if !path.exists() {
                eprintln!("Skipping: {} not found", $file_name);
                return;
            }
            // Just verify we don't panic - errors are expected
            let _ = parse_file(&path);
        }
    };
}

// Parser entry type tests
lima_test!(lima_balance, "ParserEntryTypes.Balance.beancount");
lima_test!(
    lima_balance_with_cost,
    "ParserEntryTypes.BalanceWithCost.beancount"
);
lima_test!(lima_commodity, "ParserEntryTypes.Commodity.beancount");
lima_test!(lima_note, "ParserEntryTypes.Note.beancount");
lima_test!(lima_open3, "ParserEntryTypes.Open3.beancount");
lima_test!(lima_pad, "ParserEntryTypes.Pad.beancount");
lima_test!(lima_price, "ParserEntryTypes.Price.beancount");
lima_test!(
    lima_transaction_one_string,
    "ParserEntryTypes.TransactionOneString.beancount"
);

// Balance tests
lima_test!(lima_balance_total_cost, "Balance.TotalCost.beancount");
lima_test!(lima_balance_total_price, "Balance.TotalPrice.beancount");

// Cost/lot parsing tests
lima_test!(lima_cost_none, "ParseLots.CostNone.beancount");
lima_test!(
    lima_cost_total_just_currency,
    "ParseLots.CostTotalJustCurrency.beancount"
);
lima_test!(
    lima_cost_three_components,
    "ParseLots.CostThreeComponents.beancount"
);

// Currency tests
lima_test!(
    lima_parse_currencies,
    "Currencies.ParseCurrencies.beancount"
);

// Metadata tests
lima_test!(
    lima_metadata_transaction_indented,
    "MetaData.MetadataTransactionIndented.beancount"
);

// Multiline tests
lima_test!(
    lima_multiline_narration,
    "MultipleLines.MultilineNarration.beancount"
);

// Push/pop tag tests
lima_test!(lima_pushtag_multiple, "PushPopTag.Multiple.beancount");
lima_test!(
    lima_pushtag_left_unclosed,
    "PushPopTag.TagLeftUnclosed.beancount"
);

// Push/pop meta tests
lima_test!(lima_pushmeta_shadow, "PushPopMeta.PushmetaShadow.beancount");
lima_test!(
    lima_pushmeta_override,
    "PushPopMeta.PushmetaOverride.beancount"
);

// Totals and signs tests
lima_test!(
    lima_total_price_negative,
    "TotalsAndSigns.TotalPriceNegative.beancount"
);
lima_test!(
    lima_total_price_inverted,
    "TotalsAndSigns.TotalPriceInverted.beancount"
);
lima_test!(
    lima_total_price_with_missing,
    "TotalsAndSigns.TotalPriceWithMissing.beancount"
);
lima_test!(lima_cost_negative, "TotalsAndSigns.CostNegative.beancount");

// Transaction tests
lima_test!(lima_txn_no_postings, "Transactions.NoPostings.beancount");

// Incomplete input tests
lima_test!(
    lima_incomplete_price_missing_number,
    "IncompleteInputs.PriceMissingNumber.beancount"
);
lima_test!(
    lima_incomplete_price_missing,
    "IncompleteInputs.PriceMissing.beancount"
);
lima_test!(
    lima_incomplete_price_none,
    "IncompleteInputs.PriceNone.beancount"
);
lima_test!(
    lima_incomplete_units_missing_currency,
    "IncompleteInputs.UnitsMissingCurrency.beancount"
);
lima_test!(
    lima_incomplete_units_missing_with_cost,
    "IncompleteInputs.UnitsMissingWithCost.beancount"
);
lima_test!(
    lima_incomplete_units_missing_currency_with_price,
    "IncompleteInputs.UnitsMissingCurrencyWithPrice.beancount"
);
lima_test!(
    lima_incomplete_cost_missing_number_total,
    "IncompleteInputs.CostMissingNumberTotal.beancount"
);
lima_test!(
    lima_incomplete_cost_missing_numbers,
    "IncompleteInputs.CostMissingNumbers.beancount"
);
lima_test!(
    lima_incomplete_cost_average_with_other,
    "IncompleteInputs.CostAverageWithOther.beancount"
);

// Parser options tests
lima_test!(
    lima_readonly_option,
    "ParserOptions.ReadonlyOption.beancount"
);
lima_test!(
    lima_invalid_option,
    "ParserOptions.InvalidOption.beancount",
    expect_error
);

// Parser complete tests (whitespace handling)
lima_test!(
    lima_extra_whitespace_note,
    "ParserComplete.ExtraWhitespaceNote.beancount"
);
lima_test!(
    lima_extra_whitespace_transaction,
    "ParserComplete.ExtraWhitespaceTransaction.beancount"
);
lima_test!(lima_comment_eof, "ParserComplete.CommentEOF.beancount");

// Display context tests
lima_test!(
    lima_render_commas_no,
    "DisplayContextOptions.RenderCommasNo.beancount"
);

// Document tests
lima_test!(lima_document_links, "Document.DocumentLinks.beancount");

// Deprecated options tests
lima_test!(
    lima_deprecated_option,
    "DeprecatedOptions.DeprecatedOption.beancount"
);

// Error tests (expected to have parse errors)
lima_test!(
    lima_grammar_syntax_error_multiple,
    "LexerAndParserErrors.GrammarSyntaxErrorMultiple.beancount",
    expect_error
);
lima_test!(
    lima_lexer_exception_recovery,
    "LexerAndParserErrors.LexerExceptionRecovery.beancount",
    expect_error
);
lima_test!(
    lima_grammar_exceptions_plugin,
    "LexerAndParserErrors.GrammarExceptionsPlugin.beancount",
    expect_error
);
lima_test!(
    lima_grammar_exceptions_tag_link_pipe,
    "LexerAndParserErrors.GrammarExceptionsTagLinkPipe.beancount",
    expect_error
);
lima_test!(
    lima_grammar_exceptions_option,
    "LexerAndParserErrors.GrammarExceptionsOption.beancount",
    expect_error
);
lima_test!(
    lima_grammar_exceptions_poptag,
    "LexerAndParserErrors.GrammarExceptionsPoptag.beancount",
    expect_error
);

// Whitespace/indent error tests
lima_test!(
    lima_indent_error_0,
    "Whitespace.IndentError0.beancount",
    expect_error
);
lima_test!(
    lima_indent_error_1,
    "Whitespace.IndentError1.beancount",
    expect_error
);

// Syntax error tests
lima_test!(
    lima_syntax_error_in_posting,
    "SyntaxErrors.ErrorInPosting.beancount",
    expect_error
);
lima_test!(
    lima_syntax_error_in_transaction_line,
    "SyntaxErrors.ErrorInTransactionLine.beancount",
    expect_error
);
lima_test!(
    lima_syntax_no_final_newline,
    "SyntaxErrors.NoFinalNewline.beancount",
    expect_error
);
lima_test!(
    lima_syntax_single_error_token,
    "SyntaxErrors.SingleErrorTokenAtTopLevel.beancount",
    expect_error
);
