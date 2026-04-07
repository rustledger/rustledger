//! Diagnostics handler for publishing parse and validation errors.

use lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};
use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive};
use rustledger_loader::Options as LoaderOptions;
use rustledger_parser::{ParseError, ParseResult, Span, Spanned};
use rustledger_validate::{
    Severity, ValidationError, ValidationOptions, validate_spanned_with_options,
};

use super::utils::LineIndex;
use crate::ledger_state::LedgerState;

/// Build `ValidationOptions` with custom account type names from loader options.
///
/// Uses the already-merged account type names from the loader's `Options`,
/// which handles multi-file ledgers where `name_*` options may be in included files.
///
/// See issue #572: <https://github.com/rustledger/rustledger/issues/572>
fn build_validation_options_from_loader(loader_options: &LoaderOptions) -> ValidationOptions {
    ValidationOptions {
        account_types: loader_options
            .account_types()
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
        ..Default::default()
    }
}

/// Build `ValidationOptions` with custom account type names from parsed file options.
///
/// Extracts `name_assets`, `name_liabilities`, `name_equity`, `name_income`, and
/// `name_expenses` options to support custom (including Unicode) account type names.
/// Other `ValidationOptions` fields are left at their default values.
///
/// Used when no ledger is loaded (single-file validation).
///
/// See issue #572: <https://github.com/rustledger/rustledger/issues/572>
fn build_validation_options_from_file(
    file_options: &[(String, String, Span)],
) -> ValidationOptions {
    let mut opts = ValidationOptions::default();

    // Start with validator defaults, override with file options.
    // This avoids duplicating the canonical default account type names.
    let mut account_types = opts.account_types.clone();

    for (key, value, _span) in file_options {
        match key.as_str() {
            "name_assets" => {
                if !account_types.is_empty() {
                    account_types[0] = value.clone();
                }
            }
            "name_liabilities" => {
                if account_types.len() > 1 {
                    account_types[1] = value.clone();
                }
            }
            "name_equity" => {
                if account_types.len() > 2 {
                    account_types[2] = value.clone();
                }
            }
            "name_income" => {
                if account_types.len() > 3 {
                    account_types[3] = value.clone();
                }
            }
            "name_expenses" => {
                if account_types.len() > 4 {
                    account_types[4] = value.clone();
                }
            }
            _ => {}
        }
    }

    opts.account_types = account_types;
    opts
}

/// Convert parse errors to LSP diagnostics.
pub fn parse_errors_to_diagnostics(result: &ParseResult, source: &str) -> Vec<Diagnostic> {
    let line_index = LineIndex::new(source);
    result
        .errors
        .iter()
        .map(|e| parse_error_to_diagnostic(e, &line_index))
        .collect()
}

/// Convert a single parse error to an LSP diagnostic.
pub fn parse_error_to_diagnostic(error: &ParseError, line_index: &LineIndex) -> Diagnostic {
    let (start_line, start_col) = line_index.offset_to_position(error.span.start);
    let (end_line, end_col) = line_index.offset_to_position(error.span.end);

    Diagnostic {
        range: Range {
            start: Position::new(start_line, start_col),
            end: Position::new(end_line, end_col),
        },
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(lsp_types::NumberOrString::String(format!(
            "P{:04}",
            error.kind_code()
        ))),
        source: Some("rustledger".to_string()),
        message: error.message(),
        related_information: None,
        tags: None,
        code_description: None,
        data: None,
    }
}

/// Run validation on parsed directives and convert errors to LSP diagnostics.
///
/// This function runs booking/interpolation before validation to mirror the
/// ordering used by `rledger check`. Without booking, transactions with
/// auto-filled postings (e.g., a posting with no amount) would be incorrectly
/// flagged as unbalanced.
///
/// # Arguments
/// * `directives` - Directives from the current file (used for line number mapping)
/// * `source` - Source text of the current file
/// * `validation_options` - Validation options (including custom account type names)
/// * `full_directives` - Optional: All directives from all files (for multi-file validation)
/// * `current_file_id` - Optional: File ID of the current file (to filter errors)
///
/// When `full_directives` is provided, validation runs on the complete ledger
/// but only returns errors for the current file.
pub fn validation_errors_to_diagnostics(
    directives: &[Spanned<Directive>],
    source: &str,
    validation_options: ValidationOptions,
    full_directives: Option<&[Spanned<Directive>]>,
    current_file_id: Option<u16>,
) -> Vec<Diagnostic> {
    let line_index = LineIndex::new(source);

    // Only use full directives if we can identify this file in the ledger.
    // If current_file_id is None, we can't filter errors properly and would
    // produce diagnostics with incorrect line numbers (wrong file's LineIndex).
    let directives_to_validate = if current_file_id.is_some() {
        full_directives.unwrap_or(directives)
    } else {
        directives
    };

    // Clone and sort directives by date (required for correct lot matching during booking)
    let mut booked_directives: Vec<Spanned<Directive>> = directives_to_validate.to_vec();
    booked_directives.sort_by(|a, b| {
        a.value
            .date()
            .cmp(&b.value.date())
            .then_with(|| a.value.priority().cmp(&b.value.priority()))
    });

    // Run booking/interpolation on transactions before validation.
    // This fills in missing amounts (auto-balancing) so validation sees the complete picture.
    // Use Strict booking method to match rledger check's default behavior.
    let mut booking_engine = BookingEngine::with_method(BookingMethod::Strict);
    for spanned in &mut booked_directives {
        if let Directive::Transaction(txn) = &mut spanned.value
            && let Ok(result) = booking_engine.book_and_interpolate(txn)
        {
            booking_engine.apply(&result.transaction);
            *txn = result.transaction;
        }
        // If booking fails, we leave the transaction as-is and let validation catch it
    }

    let validation_errors = validate_spanned_with_options(&booked_directives, validation_options);

    // Filter errors to only those in the current file (if file_id filtering is enabled).
    // Also include errors with file_id == None, as these are global errors (e.g., duplicate
    // account opens across files) that should be shown to the user.
    let filtered_errors: Vec<_> = if let Some(file_id) = current_file_id {
        validation_errors
            .into_iter()
            .filter(|e| e.file_id == Some(file_id) || e.file_id.is_none())
            .collect()
    } else {
        validation_errors
    };

    filtered_errors
        .iter()
        .map(|e| validation_error_to_diagnostic(e, &line_index))
        .collect()
}

/// Convert a single validation error to an LSP diagnostic.
pub fn validation_error_to_diagnostic(
    error: &ValidationError,
    line_index: &LineIndex,
) -> Diagnostic {
    // Get position from span if available, otherwise use start of file
    let (start_line, start_col, end_line, end_col, has_location) = if let Some(span) = &error.span {
        let (sl, sc) = line_index.offset_to_position(span.start);
        let (el, ec) = line_index.offset_to_position(span.end);
        (sl, sc, el, ec, true)
    } else {
        // No span available - put at start of file and note in message
        (0, 0, 0, 0, false)
    };

    // Map severity to LSP severity
    let severity = match error.code.severity() {
        Severity::Error => DiagnosticSeverity::ERROR,
        Severity::Warning => DiagnosticSeverity::WARNING,
        Severity::Info => DiagnosticSeverity::INFORMATION,
    };

    // Build message with context if available
    let mut message = if let Some(ctx) = &error.context {
        format!("{} ({})\n  context: {}", error.message, error.date, ctx)
    } else {
        format!("{} ({})", error.message, error.date)
    };

    // Add note if location is unknown
    if !has_location {
        message.push_str("\n  (source location unknown)");
    }

    Diagnostic {
        range: Range {
            start: Position::new(start_line, start_col),
            end: Position::new(end_line, end_col),
        },
        severity: Some(severity),
        code: Some(lsp_types::NumberOrString::String(
            error.code.code().to_string(),
        )),
        source: Some("rustledger".to_string()),
        message,
        related_information: None,
        tags: None,
        code_description: None,
        data: None,
    }
}

/// Maximum file size (in bytes) for which validation will be run.
/// For larger files, only parse errors are reported to keep the LSP responsive.
/// 500KB is a generous limit - most beancount files are much smaller.
const MAX_VALIDATION_FILE_SIZE: usize = 500 * 1024;

/// Get all diagnostics (parse errors + validation errors) for a parse result.
///
/// Validation is skipped for files larger than `MAX_VALIDATION_FILE_SIZE` to
/// avoid blocking the LSP main loop on very large files.
///
/// # Arguments
/// * `result` - Parse result for the current file
/// * `source` - Source text of the current file
/// * `ledger_state` - Optional: Full ledger state for multi-file validation
/// * `current_file_id` - Optional: File ID of the current file (to filter errors)
///
/// When `ledger_state` is provided, validation considers all files in the ledger,
/// providing accurate diagnostics for balance assertions that depend on transactions
/// in other files.
pub fn all_diagnostics(
    result: &ParseResult,
    source: &str,
    ledger_state: Option<&LedgerState>,
    current_file_id: Option<u16>,
) -> Vec<Diagnostic> {
    let mut diagnostics = parse_errors_to_diagnostics(result, source);

    // Only run validation if:
    // 1. There are no parse errors (validation on partial parses is confusing)
    // 2. File is not too large (to keep LSP responsive)
    if result.errors.is_empty() {
        if source.len() <= MAX_VALIDATION_FILE_SIZE {
            // Get full directives from ledger state if available
            let full_directives = ledger_state.and_then(|ls| ls.directives());

            // Build validation options with custom account type names.
            // Use ledger-wide options when a ledger is loaded (handles multi-file
            // ledgers where name_* options may be in included files); fall back
            // to per-file options for single-file validation.
            let validation_options = if let Some(ls) = ledger_state
                && let Some(ledger) = ls.ledger()
            {
                build_validation_options_from_loader(&ledger.options)
            } else {
                build_validation_options_from_file(&result.options)
            };

            let validation_diagnostics = validation_errors_to_diagnostics(
                &result.directives,
                source,
                validation_options,
                full_directives,
                current_file_id,
            );
            diagnostics.extend(validation_diagnostics);
        } else {
            tracing::debug!(
                "Skipping validation for large file ({} bytes > {} limit)",
                source.len(),
                MAX_VALIDATION_FILE_SIZE
            );
        }
    }

    diagnostics
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_line_index_offset_to_position() {
        let source = "line1\nline2\nline3";
        let line_index = LineIndex::new(source);

        assert_eq!(line_index.offset_to_position(0), (0, 0));
        assert_eq!(line_index.offset_to_position(5), (0, 5));
        assert_eq!(line_index.offset_to_position(6), (1, 0));
        assert_eq!(line_index.offset_to_position(12), (2, 0));
    }

    #[test]
    fn test_validation_errors_shown_as_diagnostics() {
        // Minimal test case from issue #475
        let source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Typo

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -3000 USD

2024-01-16 balance Assets:Bank:Checking 2000 USD
"#;

        let result = parse(source);
        assert!(result.errors.is_empty(), "Should have no parse errors");

        // Single-file validation (no ledger state)
        let diagnostics = all_diagnostics(&result, source, None, None);

        // Should have at least these validation errors:
        // - E1001: Account Income:Typo was never opened
        // - E3001: Transaction(s) do not balance
        // - E2001: Balance assertion failed
        // Note: We check for presence rather than exact count to avoid brittleness
        // if the validator adds new checks in the future.
        assert!(
            !diagnostics.is_empty(),
            "Should have at least one validation error"
        );

        // Helper to get code string from a diagnostic
        fn get_code(d: &Diagnostic) -> String {
            match d.code.as_ref().unwrap() {
                lsp_types::NumberOrString::String(s) => s.clone(),
                lsp_types::NumberOrString::Number(n) => panic!("Unexpected number code: {}", n),
            }
        }

        // Check expected error codes are present
        let codes: Vec<_> = diagnostics.iter().map(get_code).collect();

        assert!(
            codes.iter().any(|c| c == "E1001"),
            "Should have E1001 (account not opened)"
        );
        assert!(
            codes.iter().any(|c| c == "E3001"),
            "Should have E3001 (unbalanced transaction)"
        );
        assert!(
            codes.iter().any(|c| c == "E2001"),
            "Should have E2001 (balance assertion failed)"
        );

        // Check that severity matches the expected severity for each error code
        // (rather than asserting all are ERROR, which would break if warnings are added)
        for diag in &diagnostics {
            let code = get_code(diag);
            let expected_severity = match code.as_str() {
                "E1001" | "E2001" | "E3001" => Some(DiagnosticSeverity::ERROR),
                // Add other known codes here as needed
                _ => continue, // Don't assert on unknown codes
            };
            assert_eq!(
                diag.severity, expected_severity,
                "Diagnostic {} should have correct severity",
                code
            );
        }
    }

    #[test]
    fn test_auto_filled_postings_do_not_trigger_false_positive() {
        // Regression test for issue #475 follow-up comment:
        // A valid file with auto-filled postings should NOT have E3001 errors.
        // The second posting has no amount, which should be auto-filled to -5000 USD.
        let source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary

2024-01-16 balance Assets:Bank:Checking 5000 USD
"#;

        let result = parse(source);
        assert!(result.errors.is_empty(), "Should have no parse errors");

        // Single-file validation (no ledger state)
        let diagnostics = all_diagnostics(&result, source, None, None);

        // Helper to get code string from a diagnostic
        fn get_code(d: &Diagnostic) -> String {
            match d.code.as_ref().unwrap() {
                lsp_types::NumberOrString::String(s) => s.clone(),
                lsp_types::NumberOrString::Number(n) => panic!("Unexpected number code: {}", n),
            }
        }

        // Filter to only ERROR severity diagnostics (allow warnings/info)
        let error_diagnostics: Vec<&Diagnostic> = diagnostics
            .iter()
            .filter(|d| matches!(d.severity, Some(DiagnosticSeverity::ERROR)))
            .collect();

        let error_codes: Vec<_> = error_diagnostics.iter().map(|d| get_code(d)).collect();

        // Specifically, there should be NO E3001 (unbalanced transaction) error
        // because the booking step should auto-fill the missing amount
        assert!(
            !error_codes.iter().any(|c| c == "E3001"),
            "Should NOT have E3001 - the transaction is balanced after booking fills in the missing amount. Got codes: {:?}",
            error_codes
        );

        // The file should have no ERROR-severity diagnostics (but may have warnings/info)
        assert!(
            error_diagnostics.is_empty(),
            "Valid file should have no ERROR diagnostics, but got: {:?}",
            error_codes
        );
    }

    #[test]
    fn test_multi_file_balance_assertion_issue_470() {
        // Regression test for issue #470:
        // Balance assertions should pass when transactions exist in other files.
        //
        // Scenario from the issue:
        // - bank.bean has a balance assertion expecting 4950 USD
        // - The 50 USD deduction comes from credit_card.bean
        // - When validated in isolation, bank.bean shows "expected 4950, actual 5000"
        // - When validated with full ledger, the balance should be correct

        // bank.bean content (the file we're "viewing" in the LSP)
        let bank_source = r#"2024-01-01 open Assets:Bank:Checking USD

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary

2024-01-16 balance Assets:Bank:Checking 5000 USD
; After paying off credit card:
2024-01-21 balance Assets:Bank:Checking 4950 USD
"#;

        // credit_card.bean content (included file with the 50 USD payment)
        let credit_card_source = r#"2024-01-01 open Liabilities:Credit-Card

2024-01-20 * "Pay off credit card"
  Assets:Bank:Checking -50 USD
  Liabilities:Credit-Card
"#;

        // main.bean content (root file with account opens)
        let main_source = r#"2024-01-01 open Income:Salary USD
2024-01-01 open Expenses:Food USD
"#;

        // Parse all files
        let bank_result = parse(bank_source);
        let credit_card_result = parse(credit_card_source);
        let main_result = parse(main_source);

        assert!(bank_result.errors.is_empty(), "bank.bean should parse");
        assert!(
            credit_card_result.errors.is_empty(),
            "credit_card.bean should parse"
        );
        assert!(main_result.errors.is_empty(), "main.bean should parse");

        // Combine all directives (simulating what the loader does)
        // Assign file_ids: main=0, bank=1, credit_card=2
        let mut all_directives: Vec<Spanned<Directive>> = Vec::new();

        for mut d in main_result.directives {
            d.file_id = 0;
            all_directives.push(d);
        }
        for mut d in bank_result.directives.clone() {
            d.file_id = 1;
            all_directives.push(d);
        }
        for mut d in credit_card_result.directives {
            d.file_id = 2;
            all_directives.push(d);
        }

        // Helper to get code string from a diagnostic
        fn get_code(d: &Diagnostic) -> String {
            match d.code.as_ref().unwrap() {
                lsp_types::NumberOrString::String(s) => s.clone(),
                lsp_types::NumberOrString::Number(n) => panic!("Unexpected number code: {}", n),
            }
        }

        // Test 1: Validate bank.bean in ISOLATION (old broken behavior)
        // This should show E2001 for the second balance assertion
        let isolated_diagnostics = validation_errors_to_diagnostics(
            &bank_result.directives,
            bank_source,
            ValidationOptions::default(),
            None,
            None,
        );

        let isolated_codes: Vec<_> = isolated_diagnostics.iter().map(get_code).collect();

        // In isolation, the second balance (4950 USD) should fail because
        // it doesn't see the -50 USD transaction from credit_card.bean
        assert!(
            isolated_codes.iter().any(|c| c == "E2001"),
            "Isolated validation should show E2001 (balance assertion failed). Got: {:?}",
            isolated_codes
        );

        // Test 2: Validate bank.bean with FULL LEDGER (fixed behavior)
        // This should NOT show E2001 because it sees the transaction from credit_card.bean
        let full_ledger_diagnostics = validation_errors_to_diagnostics(
            &bank_result.directives,
            bank_source,
            ValidationOptions::default(),
            Some(&all_directives),
            Some(1), // file_id=1 for bank.bean
        );

        let full_ledger_codes: Vec<_> = full_ledger_diagnostics.iter().map(get_code).collect();

        // With full ledger, there should be NO E2001 errors for bank.bean
        // because the -50 USD from credit_card.bean is now visible
        assert!(
            !full_ledger_codes.iter().any(|c| c == "E2001"),
            "Full ledger validation should NOT show E2001 - balance is correct when all files are considered. Got: {:?}",
            full_ledger_codes
        );

        // Verify no ERROR-level diagnostics at all for bank.bean with full ledger
        let error_diagnostics: Vec<_> = full_ledger_diagnostics
            .iter()
            .filter(|d| matches!(d.severity, Some(DiagnosticSeverity::ERROR)))
            .collect();

        assert!(
            error_diagnostics.is_empty(),
            "bank.bean should have no errors when validated with full ledger. Got: {:?}",
            full_ledger_codes
        );
    }

    /// Regression test for issue #572: Unicode account names with `name_*` options.
    /// <https://github.com/rustledger/rustledger/issues/572>
    ///
    /// Per the beancount v3 spec, account name segments must use only ASCII letters,
    /// digits, and hyphens. Unicode characters in account names produce parse errors,
    /// even when custom `name_*` options are set. This is a breaking change from the
    /// previous behavior where Unicode was accepted.
    #[test]
    fn test_unicode_account_names_issue_572() {
        // File with Russian account type names — these now produce parse errors
        // because beancount v3 restricts account names to ASCII characters only.
        let source = r#"option "name_assets" "Активы"
option "name_liabilities" "Обязательства"
option "name_income" "Доходы"
option "name_expenses" "Расходы"
option "name_equity" "Капитал"

1900-01-01 open Капитал:Retained-Earnings
1900-01-01 open Капитал:Opening-Balances
2024-01-01 open Активы:Банк:Checking USD
2024-01-01 open Доходы:Зарплата
"#;

        let result = parse(source);
        // Per beancount v3, Unicode account names are rejected at parse time.
        assert!(
            !result.errors.is_empty(),
            "Unicode account names should produce parse errors per the beancount v3 spec"
        );
    }
}
