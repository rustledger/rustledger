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
/// * `directives` - Owned directive list to validate. The caller is
///   responsible for constructing it (e.g., cloning from `LedgerState`
///   directives, or moving from an overlay produced by
///   [`build_live_directive_overlay`]). Taking ownership here lets
///   callers that already produced an owned Vec (the overlay path) avoid
///   a second clone on every diagnostics run.
/// * `source` - Source text of the current file
/// * `validation_options` - Validation options (including custom account type names)
/// * `current_file_id` - Optional: File ID of the current file (to filter errors)
///
/// When `current_file_id` is set, errors are filtered to those whose
/// `file_id` matches (or is `None`, for global errors like duplicate
/// account opens across files).
pub fn validation_errors_to_diagnostics(
    mut booked_directives: Vec<Spanned<Directive>>,
    source: &str,
    validation_options: ValidationOptions,
    current_file_id: Option<u16>,
) -> Vec<Diagnostic> {
    let line_index = LineIndex::new(source);

    // Sort directives by date (required for correct lot matching during booking).
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
    booking_engine.register_account_methods(booked_directives.iter().map(|s| &s.value));
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

/// Build the effective directive list for validation by overlaying one or
/// more fresh in-memory parses onto a potentially-stale ledger snapshot.
///
/// # Why this exists (issues #685 and #760)
///
/// The LSP's `LedgerState` is loaded from disk at startup and refreshed only
/// by file-watcher events, which fire on save. In-memory buffer edits do not
/// touch it. Without an overlay, `all_diagnostics` would validate the
/// current file against the stale on-disk directives and produce two bad
/// behaviors:
///
/// 1. A new error the user introduces in the buffer is not reported until
///    after the next save.
/// 2. After the user saves (at which point the file-watcher pushes the bad
///    content into `LedgerState`) and then fixes the error in the buffer,
///    the error is still reported against the now-stale `LedgerState` until
///    the user saves again.
///
/// #685 fixed the single-file case by overlaying just the file being
/// edited. #760 generalized the helper to accept overlays for multiple
/// files at once so that a multi-file ledger with several open buffers
/// gets a coherent view: the validator sees the in-memory buffer state
/// for every open file, plus the on-disk state for every file in the
/// ledger that is not currently open. That matters when a balance
/// assertion in file A depends on a transaction in file B and both have
/// unsaved changes.
///
/// For each `(file_id, fresh)` pair in `fresh_overlays`, stale directives
/// with that `file_id` are dropped from `full_directives` and replaced by
/// `fresh`, remapped to the same `file_id` so the per-file filter in
/// [`validation_errors_to_diagnostics`] still works.
///
/// Returns `None` when there is nothing to overlay (no ledger state, or
/// no fresh overlays). Callers should fall back to the original
/// `full_directives` in that case.
fn build_live_directive_overlay(
    fresh_overlays: &[(u16, &[Spanned<Directive>])],
    full_directives: Option<&[Spanned<Directive>]>,
) -> Option<Vec<Spanned<Directive>>> {
    let full = full_directives?;
    if fresh_overlays.is_empty() {
        return None;
    }

    // Collect the file_ids being replaced so the filter below is O(1) per
    // directive instead of O(n) over a slice scan. For typical small
    // overlay sets (1-5 open buffers) the HashSet overhead is negligible
    // but the code reads more clearly than a `contains` on a slice.
    let replaced: std::collections::HashSet<u16> =
        fresh_overlays.iter().map(|(fid, _)| *fid).collect();

    let mut merged: Vec<Spanned<Directive>> = full
        .iter()
        .filter(|d| !replaced.contains(&d.file_id))
        .cloned()
        .collect();

    for (fid, fresh) in fresh_overlays {
        for d in *fresh {
            // The per-file parse produces directives with file_id=0 by
            // default. Anything else would mean a caller pre-tagged them,
            // which would silently get overwritten here and likely indicate
            // a bug upstream. Assert in debug builds so we catch it early.
            debug_assert!(
                d.file_id == 0 || d.file_id == *fid,
                "fresh directive for file_id={fid} was pre-tagged with \
                 unexpected file_id={} (caller bug?)",
                d.file_id
            );
            let mut d = d.clone();
            d.file_id = *fid;
            merged.push(d);
        }
    }

    Some(merged)
}

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
/// * `other_buffer_overlays` - Fresh parses for every **other** open buffer
///   that is part of the ledger, keyed by file_id. Pass `&[]` in single-file
///   mode or for tests that don't care about cross-buffer consistency.
///   See `build_live_directive_overlay` for why this exists (#760).
///
/// When `ledger_state` is provided, validation considers all files in the ledger,
/// providing accurate diagnostics for balance assertions that depend on transactions
/// in other files. Fresh overlays for the current file (from `result`) and for
/// every entry in `other_buffer_overlays` replace the on-disk snapshot of
/// those files in the validation input, so in-memory edits are seen before
/// the buffer is saved.
pub fn all_diagnostics(
    result: &ParseResult,
    source: &str,
    ledger_state: Option<&LedgerState>,
    current_file_id: Option<u16>,
    other_buffer_overlays: &[(u16, &[Spanned<Directive>])],
) -> Vec<Diagnostic> {
    let mut diagnostics = parse_errors_to_diagnostics(result, source);

    // Only run validation if:
    // 1. There are no parse errors (validation on partial parses is confusing)
    // 2. File is not too large (to keep LSP responsive)
    if result.errors.is_empty() {
        if source.len() <= MAX_VALIDATION_FILE_SIZE {
            // Get full directives from ledger state if available, then
            // apply a live overlay of every fresh in-memory parse we have.
            //
            // See `build_live_directive_overlay` for why the overlay is
            // necessary (#685 / #760: without it, diagnostics lag behind
            // in-memory buffer edits because the ledger state is only
            // refreshed on file-watcher save events).
            //
            // We build the overlay list inline from the current file's
            // fresh parse plus any other open buffers the caller handed
            // in. The current file is always first so that a caller
            // passing duplicate entries in `other_buffer_overlays`
            // (shouldn't happen, but is harmless) doesn't shadow it.
            let full_directives_raw = ledger_state.and_then(|ls| ls.directives());

            // Build the list of overlays to apply to the ledger snapshot.
            // Always include the current file's fresh parse first, then
            // append any other open buffers the caller handed in (#760).
            let mut overlay_entries: Vec<(u16, &[Spanned<Directive>])> =
                Vec::with_capacity(1 + other_buffer_overlays.len());
            if let Some(fid) = current_file_id {
                overlay_entries.push((fid, result.directives.as_slice()));
            }
            overlay_entries.extend_from_slice(other_buffer_overlays);
            let overlay = build_live_directive_overlay(&overlay_entries, full_directives_raw);

            // Construct the owned directive list for validation. Moving
            // the overlay in by value saves a second clone on the
            // multi-file overlay path (the overlay is already an owned
            // Vec; handing it to `validation_errors_to_diagnostics` by
            // value avoids the `.to_vec()` that used to happen inside
            // that function). Other paths still pay one clone, same as
            // before. See #758 for the single-file version of this
            // optimization.
            let booked_directives: Vec<Spanned<Directive>> = if let Some(owned) = overlay {
                owned
            } else if let Some(full) = full_directives_raw
                && current_file_id.is_some()
            {
                full.to_vec()
            } else {
                result.directives.clone()
            };

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
                booked_directives,
                source,
                validation_options,
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
        let diagnostics = all_diagnostics(&result, source, None, None, &[]);

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
        let diagnostics = all_diagnostics(&result, source, None, None, &[]);

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
            bank_result.directives.clone(),
            bank_source,
            ValidationOptions::default(),
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
            all_directives.clone(),
            bank_source,
            ValidationOptions::default(),
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

        // Verify the diagnostics layer produces ERROR diagnostics (not just parse errors).
        let diagnostics = parse_errors_to_diagnostics(&result, source);
        assert!(
            !diagnostics.is_empty(),
            "Unicode account name errors should produce LSP diagnostics"
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.severity == Some(DiagnosticSeverity::ERROR)),
            "At least one diagnostic should be ERROR severity"
        );
    }

    /// Regression test for issue #685.
    ///
    /// When the LSP is started against a journal file, `ledger_state` is
    /// loaded from disk at startup and refreshed only by file-watcher events
    /// on save. In-memory buffer edits don't touch it, so without a live
    /// overlay the validation pass sees stale directives and diagnostics lag
    /// behind the buffer until the next save.
    ///
    /// This test exercises `build_live_directive_overlay` directly, plus the
    /// downstream `validation_errors_to_diagnostics` path, to confirm both of
    /// the bad behaviors that motivated the bug are fixed:
    ///
    /// 1. A new error introduced in the buffer is reported before any save.
    /// 2. After the buffer is fixed, the error is cleared, even if the
    ///    stale `full_directives` still hold the broken version.
    #[test]
    fn test_live_overlay_reflects_buffer_edits_issue_685() {
        // Helper for reading an LSP diagnostic's string code.
        fn get_code(d: &Diagnostic) -> String {
            match d.code.as_ref().unwrap() {
                lsp_types::NumberOrString::String(s) => s.clone(),
                lsp_types::NumberOrString::Number(n) => panic!("Unexpected number code: {n}"),
            }
        }

        // The on-disk version of the file is balanced.
        let on_disk_source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -5000 USD
"#;

        // The buffer version has been edited to be unbalanced (5000 vs 5001).
        let buffer_unbalanced_source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -5001 USD
"#;

        // And a later state where the user has fixed the imbalance back to
        // its original value while `ledger_state` still holds the broken
        // saved version (simulating: user saved while broken, then fixed in
        // the buffer).
        let buffer_fixed_source = on_disk_source;
        let on_disk_stale_broken_source = buffer_unbalanced_source;

        // ===== Scenario 1: buffer is edited, ledger_state still clean =====

        let fresh_unbalanced = parse(buffer_unbalanced_source);
        assert!(
            fresh_unbalanced.errors.is_empty(),
            "buffer should parse cleanly"
        );

        // Simulate what `LedgerState::load` would have given us: parsed
        // directives from the on-disk content, with a specific file_id.
        // file_id=1 matches how multi-file tests in this module assign IDs.
        let on_disk_clean = parse(on_disk_source);
        let stale_full_directives: Vec<Spanned<Directive>> = on_disk_clean
            .directives
            .iter()
            .map(|d| {
                let mut d = d.clone();
                d.file_id = 1;
                d
            })
            .collect();

        // Without the overlay: validation would use the stale clean
        // directives and report no error, which is the bug.
        let no_overlay = validation_errors_to_diagnostics(
            stale_full_directives.clone(),
            buffer_unbalanced_source,
            ValidationOptions::default(),
            Some(1),
        );
        let no_overlay_codes: Vec<_> = no_overlay.iter().map(get_code).collect();
        assert!(
            !no_overlay_codes.iter().any(|c| c == "E3001"),
            "Bug reproduction: without overlay, stale ledger_state hides \
             the buffer's new imbalance. Got: {no_overlay_codes:?}"
        );

        // With the overlay: fresh directives replace stale ones for this
        // file, and the new imbalance is reported.
        let overlay = build_live_directive_overlay(
            &[(1, fresh_unbalanced.directives.as_slice())],
            Some(&stale_full_directives),
        )
        .expect("overlay must be built when both full_directives and overlays are present");

        let with_overlay = validation_errors_to_diagnostics(
            overlay,
            buffer_unbalanced_source,
            ValidationOptions::default(),
            Some(1),
        );
        let with_overlay_codes: Vec<_> = with_overlay.iter().map(get_code).collect();
        assert!(
            with_overlay_codes.iter().any(|c| c == "E3001"),
            "Fix verification: with overlay, buffer's imbalance should be \
             reported as E3001. Got: {with_overlay_codes:?}"
        );

        // ===== Scenario 2: buffer is fixed, ledger_state still broken =====

        let fresh_fixed = parse(buffer_fixed_source);
        assert!(
            fresh_fixed.errors.is_empty(),
            "fixed buffer should parse cleanly"
        );

        // Simulate: user saved the broken version at some point, so
        // `ledger_state` now holds the broken directives.
        let stale_broken = parse(on_disk_stale_broken_source);
        let stale_broken_full: Vec<Spanned<Directive>> = stale_broken
            .directives
            .iter()
            .map(|d| {
                let mut d = d.clone();
                d.file_id = 1;
                d
            })
            .collect();

        // Without the overlay: validation uses the stale broken ledger and
        // the old error persists even though the buffer is fixed.
        let no_overlay_persist = validation_errors_to_diagnostics(
            stale_broken_full.clone(),
            buffer_fixed_source,
            ValidationOptions::default(),
            Some(1),
        );
        let no_overlay_persist_codes: Vec<_> = no_overlay_persist.iter().map(get_code).collect();
        assert!(
            no_overlay_persist_codes.iter().any(|c| c == "E3001"),
            "Bug reproduction: without overlay, stale broken ledger_state \
             makes a now-fixed buffer still appear broken. \
             Got: {no_overlay_persist_codes:?}"
        );

        // With the overlay: fresh fixed directives replace the stale broken
        // ones, and the error is cleared.
        let overlay_fixed = build_live_directive_overlay(
            &[(1, fresh_fixed.directives.as_slice())],
            Some(&stale_broken_full),
        )
        .expect("overlay must be built when both full_directives and overlays are present");

        let with_overlay_fixed = validation_errors_to_diagnostics(
            overlay_fixed,
            buffer_fixed_source,
            ValidationOptions::default(),
            Some(1),
        );
        let with_overlay_fixed_codes: Vec<_> = with_overlay_fixed.iter().map(get_code).collect();
        assert!(
            !with_overlay_fixed_codes.iter().any(|c| c == "E3001"),
            "Fix verification: with overlay, fixed buffer should clear the \
             stale error. Got: {with_overlay_fixed_codes:?}"
        );
    }

    #[test]
    fn test_live_overlay_returns_none_when_nothing_to_overlay() {
        let parsed = parse("2024-01-01 open Assets:Bank:Checking USD\n");

        // No ledger state at all: nothing to overlay onto.
        let result = build_live_directive_overlay(&[(1, parsed.directives.as_slice())], None);
        assert!(
            result.is_none(),
            "no full_directives: overlay should be None (caller falls back \
             to the single-file validation path)"
        );

        // Ledger state present but no fresh overlays: nothing to apply.
        let other_parsed = parse("2024-01-01 open Income:Salary\n");
        let other_dirs: Vec<Spanned<Directive>> = other_parsed
            .directives
            .iter()
            .map(|d| {
                let mut d = d.clone();
                d.file_id = 2;
                d
            })
            .collect();
        let result = build_live_directive_overlay(&[], Some(&other_dirs));
        assert!(
            result.is_none(),
            "full_directives present but no overlays: overlay should be None \
             (caller falls back to full_directives as-is)"
        );
    }

    /// Regression test for issue #760: multi-file live overlay.
    ///
    /// The #685 fix only overlays the file currently being validated. In a
    /// multi-file ledger with several open buffers, edits in files other
    /// than the one being validated were still ignored by the validator. A
    /// balance assertion in file A that depends on an edited transaction in
    /// file B would be validated against B's on-disk version, producing a
    /// diagnostic that disagrees with what the user sees on screen.
    ///
    /// This test directly exercises `build_live_directive_overlay` with
    /// two overlays at once and verifies that both files' stale entries
    /// are replaced atomically, so validation sees a coherent snapshot of
    /// every open buffer in the ledger.
    #[test]
    fn test_multi_buffer_overlay_replaces_multiple_files_issue_760() {
        fn get_code(d: &Diagnostic) -> String {
            match d.code.as_ref().unwrap() {
                lsp_types::NumberOrString::String(s) => s.clone(),
                lsp_types::NumberOrString::Number(n) => panic!("Unexpected number code: {n}"),
            }
        }

        // Bank file: has a balance assertion (4950) that depends on the
        // credit-card file's transaction amount (-50). If the credit-card
        // file's transaction is edited in the buffer to -75, the assertion
        // should start failing with an expected of 4925, not 4950.
        let bank_on_disk = r#"2024-01-01 open Assets:Bank:Checking USD

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary

2024-01-21 balance Assets:Bank:Checking 4950 USD
"#;

        // Credit card file: currently on disk has -50 USD, so the bank
        // balance assertion holds.
        let credit_card_on_disk = r#"2024-01-01 open Liabilities:Credit-Card

2024-01-20 * "Pay off credit card"
  Assets:Bank:Checking -50 USD
  Liabilities:Credit-Card
"#;

        // User edits the credit-card file in-buffer to -75 USD without
        // saving. Nothing else changes.
        let credit_card_buffer = r#"2024-01-01 open Liabilities:Credit-Card

2024-01-20 * "Pay off credit card"
  Assets:Bank:Checking -75 USD
  Liabilities:Credit-Card
"#;

        // Main file: root with account opens.
        let main_on_disk = r#"2024-01-01 open Income:Salary USD
2024-01-01 open Expenses:Food USD
"#;

        let main_parsed = parse(main_on_disk);
        let bank_parsed = parse(bank_on_disk);
        let credit_card_parsed_disk = parse(credit_card_on_disk);
        let credit_card_parsed_buffer = parse(credit_card_buffer);
        assert!(main_parsed.errors.is_empty());
        assert!(bank_parsed.errors.is_empty());
        assert!(credit_card_parsed_disk.errors.is_empty());
        assert!(credit_card_parsed_buffer.errors.is_empty());

        // Simulate the ledger snapshot the LSP would have at startup:
        // main=0, bank=1, credit_card=2, all loaded from disk.
        let mut stale_full: Vec<Spanned<Directive>> = Vec::new();
        for mut d in main_parsed.directives.clone() {
            d.file_id = 0;
            stale_full.push(d);
        }
        for mut d in bank_parsed.directives.clone() {
            d.file_id = 1;
            stale_full.push(d);
        }
        for mut d in credit_card_parsed_disk.directives {
            d.file_id = 2;
            stale_full.push(d);
        }

        // Baseline sanity check: with both files as they are on disk, the
        // bank balance assertion holds (4950 expected, 4950 actual). No
        // E2001 diagnostic for bank.
        let baseline = validation_errors_to_diagnostics(
            stale_full.clone(),
            bank_on_disk,
            ValidationOptions::default(),
            Some(1),
        );
        let baseline_codes: Vec<_> = baseline.iter().map(get_code).collect();
        assert!(
            !baseline_codes.iter().any(|c| c == "E2001"),
            "baseline: bank balance should hold with disk state. Got: {baseline_codes:?}"
        );

        // The bug we're fixing: user edits credit_card.bean in a second
        // buffer, but bank.bean is the one being validated. Without an
        // overlay for credit_card, the bank balance assertion is validated
        // against the stale credit_card directives and appears to hold,
        // even though the user's actual edited state makes it wrong
        // (4950 expected, 4925 actual after the -75 edit).
        //
        // Scenario 1: overlay only bank (simulating #685's fix). Bank's
        // balance assertion still appears to hold because credit_card is
        // stale.
        let single_buffer_overlay = build_live_directive_overlay(
            &[(1, bank_parsed.directives.as_slice())],
            Some(&stale_full),
        )
        .expect("overlay should be built");

        let single_overlay_diagnostics = validation_errors_to_diagnostics(
            single_buffer_overlay,
            bank_on_disk,
            ValidationOptions::default(),
            Some(1),
        );
        let single_codes: Vec<_> = single_overlay_diagnostics.iter().map(get_code).collect();
        assert!(
            !single_codes.iter().any(|c| c == "E2001"),
            "Bug reproduction: with only the current file overlaid, the \
             credit_card buffer edit is invisible and the bank balance \
             appears to still hold. Got: {single_codes:?}"
        );

        // Scenario 2: overlay both buffers (the #760 fix). Now validation
        // sees the edited credit_card content, the balance assertion in
        // bank is checked against the actual in-buffer state of the whole
        // ledger, and E2001 is reported as expected.
        let multi_buffer_overlay = build_live_directive_overlay(
            &[
                (1, bank_parsed.directives.as_slice()),
                (2, credit_card_parsed_buffer.directives.as_slice()),
            ],
            Some(&stale_full),
        )
        .expect("overlay should be built");

        let multi_overlay_diagnostics = validation_errors_to_diagnostics(
            multi_buffer_overlay,
            bank_on_disk,
            ValidationOptions::default(),
            Some(1),
        );
        let multi_codes: Vec<_> = multi_overlay_diagnostics.iter().map(get_code).collect();
        assert!(
            multi_codes.iter().any(|c| c == "E2001"),
            "Fix verification: with both files overlaid, bank balance \
             assertion (4950) should fail because credit_card was edited to \
             -75 in the buffer, making actual 4925. Got: {multi_codes:?}"
        );
    }

    /// End-to-end regression test for #685 through `all_diagnostics`.
    ///
    /// The other #685 regression test exercises
    /// `build_live_directive_overlay` and `validation_errors_to_diagnostics`
    /// directly, which pins the helper logic but does not pin the wiring
    /// inside `all_diagnostics`. A future refactor that moves or renames
    /// the overlay call (or adds a new caller that forgets it) could break
    /// the fix without tripping the direct tests. This test uses a real
    /// `LedgerState` backed by a tempdir file so the full
    /// `all_diagnostics` code path runs, catching integration-level
    /// regressions.
    #[test]
    fn test_all_diagnostics_applies_live_overlay_issue_685() {
        use std::fs;

        fn get_code(d: &Diagnostic) -> String {
            match d.code.as_ref().unwrap() {
                lsp_types::NumberOrString::String(s) => s.clone(),
                lsp_types::NumberOrString::Number(n) => panic!("Unexpected number code: {n}"),
            }
        }

        let on_disk = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -5000 USD
"#;
        let buffer_unbalanced = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -5001 USD
"#;

        // Write the balanced version to disk and build a real LedgerState
        // from it. This is the state the LSP would have at startup, before
        // any in-memory edits.
        let tempdir = tempfile::tempdir().expect("tempdir");
        let journal_path = tempdir.path().join("ledger.beancount");
        fs::write(&journal_path, on_disk).expect("write journal");

        let mut ledger_state = LedgerState::new();
        ledger_state
            .load(&journal_path)
            .expect("LedgerState::load should succeed on well-formed journal");

        // Find the file_id the loader assigned to this file. Mirrors the
        // logic in `main_loop::publish_diagnostics` at the call site.
        let canonical = journal_path.canonicalize().expect("canonicalize");
        let file_id = ledger_state
            .ledger()
            .expect("ledger loaded")
            .source_map
            .files()
            .iter()
            .find_map(|f| {
                f.path
                    .canonicalize()
                    .ok()
                    .filter(|p| *p == canonical)
                    .map(|_| f.id as u16)
            })
            .expect("file_id for loaded file");

        // Simulate a `didChange` with the unbalanced buffer content.
        // `all_diagnostics` parses the fresh text and should report E3001
        // because the overlay brings the buffer edits into the validation
        // directive list.
        let result = parse(buffer_unbalanced);
        assert!(
            result.errors.is_empty(),
            "buffer content should parse cleanly"
        );

        let diagnostics = all_diagnostics(
            &result,
            buffer_unbalanced,
            Some(&ledger_state),
            Some(file_id),
            &[],
        );
        let codes: Vec<_> = diagnostics.iter().map(get_code).collect();

        assert!(
            codes.iter().any(|c| c == "E3001"),
            "all_diagnostics should report the buffer's new imbalance (E3001) \
             even though LedgerState still holds the balanced on-disk \
             version. Got: {codes:?}"
        );

        // And the inverse: re-parsing the now-balanced buffer should clear
        // diagnostics, regardless of LedgerState's contents. (LedgerState
        // here still holds the balanced on-disk version, so this path is
        // symmetric with the unbalanced case — we're mainly asserting the
        // happy path still works after the overlay merge.)
        let result_clean = parse(on_disk);
        assert!(result_clean.errors.is_empty());
        let clean_diagnostics = all_diagnostics(
            &result_clean,
            on_disk,
            Some(&ledger_state),
            Some(file_id),
            &[],
        );
        let clean_error_count = clean_diagnostics
            .iter()
            .filter(|d| matches!(d.severity, Some(DiagnosticSeverity::ERROR)))
            .count();
        assert_eq!(
            clean_error_count,
            0,
            "balanced buffer should produce no ERROR diagnostics. Got: {:?}",
            clean_diagnostics.iter().map(get_code).collect::<Vec<_>>()
        );
    }

    /// End-to-end regression test for #760 through `all_diagnostics`.
    ///
    /// The direct helper test `test_multi_buffer_overlay_replaces_multiple_files_issue_760`
    /// exercises `build_live_directive_overlay` + `validation_errors_to_diagnostics`,
    /// but doesn't pin the integration point in `all_diagnostics` that
    /// consumes `other_buffer_overlays` and feeds them into the helper.
    /// This test uses a real `LedgerState` backed by a tempdir with two
    /// files (a main journal and an included credit-card file), verifies
    /// the baseline (no overlays → no error), then passes a fresh parse
    /// of an edited credit-card buffer as an `other_buffer_overlays` entry
    /// and confirms the edit is visible to validation of the main file.
    #[test]
    fn test_all_diagnostics_multi_buffer_overlay_issue_760() {
        use std::fs;

        fn get_code(d: &Diagnostic) -> String {
            match d.code.as_ref().unwrap() {
                lsp_types::NumberOrString::String(s) => s.clone(),
                lsp_types::NumberOrString::Number(n) => panic!("Unexpected number code: {n}"),
            }
        }

        // Main journal: opens, a paycheck, a balance assertion that depends
        // on the credit-card file, and an include directive.
        let main_content = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary USD
2024-01-01 open Liabilities:Credit-Card USD

2024-01-15 * "Paycheck"
  Assets:Bank:Checking                    5000 USD
  Income:Salary

2024-01-21 balance Assets:Bank:Checking 4950 USD

include "credit_card.beancount"
"#;

        // Credit-card file on disk: -50 USD, which makes the main balance
        // assertion (4950) hold.
        let credit_card_disk = r#"2024-01-20 * "Pay off credit card"
  Assets:Bank:Checking -50 USD
  Liabilities:Credit-Card
"#;

        // Credit-card file after the user edits the buffer to -75 USD
        // without saving. The main balance assertion should now fail
        // (expected 4950, actual 4925), but only if validation sees the
        // buffer edit.
        let credit_card_buffer = r#"2024-01-20 * "Pay off credit card"
  Assets:Bank:Checking -75 USD
  Liabilities:Credit-Card
"#;

        let tempdir = tempfile::tempdir().expect("tempdir");
        let main_path = tempdir.path().join("main.beancount");
        let credit_card_path = tempdir.path().join("credit_card.beancount");
        fs::write(&main_path, main_content).expect("write main");
        fs::write(&credit_card_path, credit_card_disk).expect("write credit_card");

        let mut ledger_state = LedgerState::new();
        ledger_state
            .load(&main_path)
            .expect("LedgerState::load should succeed");

        // Resolve file_ids for both files.
        let ledger = ledger_state.ledger().expect("ledger loaded");
        let main_canonical = main_path.canonicalize().expect("canonicalize main");
        let credit_card_canonical = credit_card_path
            .canonicalize()
            .expect("canonicalize credit_card");

        let main_file_id = ledger
            .source_map
            .files()
            .iter()
            .find_map(|f| {
                f.path
                    .canonicalize()
                    .ok()
                    .filter(|p| *p == main_canonical)
                    .map(|_| f.id as u16)
            })
            .expect("main file_id");
        let credit_card_file_id = ledger
            .source_map
            .files()
            .iter()
            .find_map(|f| {
                f.path
                    .canonicalize()
                    .ok()
                    .filter(|p| *p == credit_card_canonical)
                    .map(|_| f.id as u16)
            })
            .expect("credit_card file_id");

        // Simulate a didChange on the main file (unchanged). Without any
        // overlays for other buffers, validation uses the on-disk
        // credit-card content and the balance assertion holds.
        let main_result = parse(main_content);
        assert!(main_result.errors.is_empty(), "main should parse cleanly");

        let baseline = all_diagnostics(
            &main_result,
            main_content,
            Some(&ledger_state),
            Some(main_file_id),
            &[],
        );
        let baseline_codes: Vec<_> = baseline.iter().map(get_code).collect();
        assert!(
            !baseline_codes.iter().any(|c| c == "E2001"),
            "baseline: bank balance should hold with disk credit_card. Got: {baseline_codes:?}"
        );

        // Now simulate having the credit_card buffer open with the edited
        // content. Parse it and pass it as an other_buffer_overlays entry.
        // all_diagnostics should now report E2001 because the balance
        // assertion (4950) doesn't match the buffer-state actual (4925).
        let credit_card_buffer_parse = parse(credit_card_buffer);
        assert!(
            credit_card_buffer_parse.errors.is_empty(),
            "credit_card buffer should parse cleanly"
        );

        let with_overlay = all_diagnostics(
            &main_result,
            main_content,
            Some(&ledger_state),
            Some(main_file_id),
            &[(
                credit_card_file_id,
                credit_card_buffer_parse.directives.as_slice(),
            )],
        );
        let with_overlay_codes: Vec<_> = with_overlay.iter().map(get_code).collect();
        assert!(
            with_overlay_codes.iter().any(|c| c == "E2001"),
            "Fix verification: with credit_card buffer overlaid, main's \
             balance assertion should fail (4950 expected, 4925 actual \
             after the -75 edit). Got: {with_overlay_codes:?}"
        );
    }
}
