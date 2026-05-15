//! Integration tests for the loader crate.
//!
//! Tests are based on patterns from beancount's test suite.

use rustledger_loader::{LoadError, Loader, load_raw};
use std::path::Path;

fn fixtures_path(name: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

#[test]
fn test_load_simple_file() {
    let path = fixtures_path("simple.beancount");
    let result = load_raw(&path).expect("should load simple file");

    // Check options were parsed
    assert_eq!(result.options.title, Some("Test Ledger".to_string()));
    assert_eq!(result.options.operating_currency, vec!["USD".to_string()]);

    // Check directives were loaded
    assert!(!result.directives.is_empty());

    // Should have 3 open directives, 1 transaction, 1 balance
    let opens = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();
    assert_eq!(opens, 3, "expected 3 open directives");

    let txns = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Transaction(_)))
        .count();
    assert_eq!(txns, 1, "expected 1 transaction");

    // No errors
    assert!(result.errors.is_empty(), "expected no errors");
}

#[test]
fn test_load_with_include() {
    let path = fixtures_path("main_with_include.beancount");
    let result = load_raw(&path).expect("should load file with include");

    // Should have directives from both files
    // main_with_include.beancount: 1 transaction
    // accounts.beancount: 3 open directives
    let opens = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();
    assert_eq!(opens, 3, "expected 3 open directives from included file");

    let txns = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Transaction(_)))
        .count();
    assert_eq!(txns, 1, "expected 1 transaction from main file");

    // Check source map has both files
    assert_eq!(
        result.source_map.files().len(),
        2,
        "expected 2 files in source map"
    );

    // No errors
    assert!(result.errors.is_empty(), "expected no errors");
}

#[test]
fn test_load_include_cycle_detection() {
    let path = fixtures_path("cycle_a.beancount");
    let result = Loader::new().load(&path);

    match result {
        Err(LoadError::IncludeCycle { cycle }) => {
            // The cycle should include both files
            assert!(cycle.len() >= 2, "cycle should have at least 2 entries");
            let cycle_str = cycle.join(" -> ");
            assert!(
                cycle_str.contains("cycle_a.beancount"),
                "cycle should mention cycle_a.beancount"
            );
            assert!(
                cycle_str.contains("cycle_b.beancount"),
                "cycle should mention cycle_b.beancount"
            );
        }
        Ok(result) => {
            // If we get Ok, check if cycle was caught as an error in result.errors
            let has_cycle_error = result
                .errors
                .iter()
                .any(|e| matches!(e, LoadError::IncludeCycle { .. }));
            assert!(has_cycle_error, "expected include cycle to be detected");
        }
        Err(e) => panic!("expected IncludeCycle error, got: {e}"),
    }
}

/// Regression test for issue #765.
///
/// The pta-standards `include-cycle-detection` conformance test
/// asserts on `error_contains: ["Duplicate filename"]`, matching Python
/// beancount's wording for the same condition. rustledger previously
/// said `"include cycle detected: ..."` which was more informative but
/// didn't match the substring. We now lead with `"Duplicate filename
/// parsed: \"<file>\""` and preserve the cycle path in a trailing
/// parenthetical. This test pins the exact phrasing so a refactor
/// can't silently drop the conformance-required substring.
#[test]
fn test_include_cycle_display_contains_duplicate_filename_issue_765() {
    let path = fixtures_path("cycle_a.beancount");
    let result = Loader::new().load(&path);

    // Find the IncludeCycle error in either the Err path or the
    // load_result.errors collection (the loader supports partial
    // results).
    let err: LoadError = match result {
        Err(e @ LoadError::IncludeCycle { .. }) => e,
        Ok(result) => result
            .errors
            .into_iter()
            .find(|e| matches!(e, LoadError::IncludeCycle { .. }))
            .expect("expected IncludeCycle error in load_result.errors"),
        Err(other) => panic!("expected IncludeCycle error, got: {other}"),
    };

    let rendered = err.to_string();
    assert!(
        rendered.contains("Duplicate filename"),
        "IncludeCycle Display must contain 'Duplicate filename' for \
         beancount conformance (#765). Got: {rendered}"
    );
    assert!(
        rendered.contains("cycle_a.beancount"),
        "IncludeCycle Display must mention the cycle file. Got: {rendered}"
    );
    assert!(
        rendered.contains("include cycle:"),
        "IncludeCycle Display should still preserve the cycle path \
         for debuggability. Got: {rendered}"
    );
}

#[test]
fn test_load_missing_include() {
    let path = fixtures_path("missing_include.beancount");
    let result = load_raw(&path).expect("should load file even with missing include");

    // Should have IO error for missing file
    let has_io_error = result
        .errors
        .iter()
        .any(|e| matches!(e, LoadError::Io { .. }));
    assert!(has_io_error, "expected IO error for missing include");

    // Should still have the open directive from the main file
    let opens = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();
    assert_eq!(opens, 1, "expected 1 open directive from main file");
}

#[test]
fn test_load_with_plugins() {
    let path = fixtures_path("with_plugin.beancount");
    let result = load_raw(&path).expect("should load file with plugins");

    // Should have 2 plugin directives
    assert_eq!(result.plugins.len(), 2, "expected 2 plugins");

    // Check first plugin
    assert_eq!(result.plugins[0].name, "beancount.plugins.leafonly");
    assert!(result.plugins[0].config.is_none());

    // Check second plugin with config
    assert_eq!(result.plugins[1].name, "beancount.plugins.check_commodity");
    assert_eq!(result.plugins[1].config, Some("config_string".to_string()));
}

#[test]
fn test_load_with_parse_errors() {
    let path = fixtures_path("parse_error.beancount");
    let result = load_raw(&path).expect("should load file even with parse errors");

    // Should have parse errors
    let has_parse_error = result
        .errors
        .iter()
        .any(|e| matches!(e, LoadError::ParseErrors { .. }));
    assert!(has_parse_error, "expected parse error");

    // Should still have valid directives (error recovery)
    // At minimum: 1 open from before error, 1 open from after error
    let opens = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();
    assert!(
        opens >= 1,
        "expected at least 1 open directive despite errors"
    );
}

#[test]
fn test_load_nonexistent_file() {
    let path = fixtures_path("does_not_exist.beancount");
    let result = Loader::new().load(&path);

    match result {
        Err(LoadError::Io { path: err_path, .. }) => {
            assert!(
                err_path.to_string_lossy().contains("does_not_exist"),
                "error should mention the missing file"
            );
        }
        Ok(_) => panic!("expected IO error for nonexistent file"),
        Err(e) => panic!("expected IO error, got: {e}"),
    }
}

#[test]
fn test_loader_reuse() {
    // Test that a single Loader instance can be used to load multiple files
    let mut loader = Loader::new();

    let path1 = fixtures_path("simple.beancount");
    let result1 = loader.load(&path1).expect("should load first file");
    assert!(!result1.directives.is_empty());

    // Note: Loader tracks loaded files, so loading again might return cached/empty
    // This tests the expected behavior
    let path2 = fixtures_path("accounts.beancount");
    let mut loader2 = Loader::new();
    let result2 = loader2.load(&path2).expect("should load second file");
    assert!(!result2.directives.is_empty());
}

#[test]
fn test_source_map_line_lookup() {
    let path = fixtures_path("simple.beancount");
    let result = load_raw(&path).expect("should load simple file");

    // Source map should have the file
    assert!(!result.source_map.files().is_empty());

    let file = &result.source_map.files()[0];
    assert!(file.path.to_string_lossy().contains("simple.beancount"));

    // Should be able to look up line/column for positions
    // The first directive should have valid span info
    if let Some(first) = result.directives.first() {
        let (line, col) = file.line_col(first.span.start);
        assert!(line >= 1, "line should be >= 1");
        assert!(col >= 1, "col should be >= 1");
    }
}

#[test]
fn test_duplicate_include_ignored() {
    // Create a scenario where the same file is included multiple times
    // It should only be loaded once
    let path = fixtures_path("main_with_include.beancount");
    let result = load_raw(&path).expect("should load file");

    // Each unique file should only be in source map once
    let file_count = result.source_map.files().len();
    assert_eq!(
        file_count, 2,
        "should have exactly 2 files (main + accounts)"
    );
}

// ============================================================================
// Glob Include Pattern Tests
// ============================================================================

#[test]
fn test_glob_include_pattern() {
    let path = fixtures_path("glob_test/main.beancount");
    let result = load_raw(&path).expect("should load file with glob include");

    // Should have loaded files from the glob pattern
    // main.beancount: 1 open directive
    // transactions/2024.beancount: 1 open, 1 transaction
    // transactions/2025.beancount: 1 open, 1 transaction
    let opens = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();
    assert_eq!(
        opens, 3,
        "expected 3 open directives (1 from main, 2 from transactions)"
    );

    let txns = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Transaction(_)))
        .count();
    assert_eq!(txns, 2, "expected 2 transactions from glob-matched files");

    // Source map should have 3 files
    assert_eq!(
        result.source_map.files().len(),
        3,
        "expected 3 files in source map (main + 2 from glob)"
    );

    // No errors expected
    assert!(
        result.errors.is_empty(),
        "expected no errors, got: {:?}",
        result.errors
    );
}

#[test]
fn test_glob_include_no_match() {
    let path = fixtures_path("glob_nomatch.beancount");
    let result = load_raw(&path).expect("should load file even with no-match glob");

    // Should have GlobNoMatch error
    let has_glob_error = result
        .errors
        .iter()
        .any(|e| matches!(e, LoadError::GlobNoMatch { .. }));
    assert!(
        has_glob_error,
        "expected GlobNoMatch error for pattern with no matches"
    );

    // Should still have the open directive from the main file
    let opens = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();
    assert_eq!(opens, 1, "expected 1 open directive from main file");
}

#[test]
fn test_glob_include_deterministic_order() {
    // Load twice and ensure same order
    let path = fixtures_path("glob_test/main.beancount");

    let result1 = load_raw(&path).expect("should load file");
    let result2 = load_raw(&path).expect("should load file again");

    // File order in source map should be deterministic
    let files1: Vec<_> = result1
        .source_map
        .files()
        .iter()
        .map(|f| f.path.clone())
        .collect();
    let files2: Vec<_> = result2
        .source_map
        .files()
        .iter()
        .map(|f| f.path.clone())
        .collect();

    assert_eq!(
        files1, files2,
        "file order should be deterministic across loads"
    );
}

// ============================================================================
// Path Security Tests
// ============================================================================

#[test]
fn test_path_traversal_blocked_with_security_enabled() {
    let path = fixtures_path("path_traversal.beancount");
    let result = Loader::new()
        .with_path_security(true)
        .load(&path)
        .expect("should load file even with blocked include");

    // Should have path traversal error
    let has_traversal_error = result
        .errors
        .iter()
        .any(|e| matches!(e, LoadError::PathTraversal { .. }));
    assert!(
        has_traversal_error,
        "expected PathTraversal error when security is enabled"
    );

    // Should still have the open directive from the main file
    let opens = result
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();
    assert_eq!(opens, 1, "expected 1 open directive from main file");
}

#[test]
fn test_path_traversal_allowed_without_security() {
    let path = fixtures_path("path_traversal.beancount");
    let result = load_raw(&path).expect("should load file");

    // Without security enabled, should NOT have path traversal error
    // (though may have IO error if include target doesn't exist or parse error if not valid beancount)
    let has_traversal_error = result
        .errors
        .iter()
        .any(|e| matches!(e, LoadError::PathTraversal { .. }));
    assert!(
        !has_traversal_error,
        "should not have PathTraversal error when security is disabled"
    );
}

#[test]
fn test_with_custom_root_dir() {
    let path = fixtures_path("main_with_include.beancount");
    let fixtures_dir = fixtures_path("");

    // With root set to fixtures dir, include should work
    let result = Loader::new()
        .with_root_dir(fixtures_dir)
        .load(&path)
        .expect("should load file");

    // Should not have path traversal errors
    let has_traversal_error = result
        .errors
        .iter()
        .any(|e| matches!(e, LoadError::PathTraversal { .. }));
    assert!(
        !has_traversal_error,
        "should not have PathTraversal error for valid include"
    );

    // Should have loaded the include
    assert_eq!(result.source_map.files().len(), 2, "should have 2 files");
}

// ============================================================================
// Process Pipeline Tests (Coverage improvement for process.rs)
// ============================================================================

use rustledger_loader::{ErrorSeverity, LedgerError, LoadOptions, load, process};

#[test]
fn test_process_pipeline_with_validation() {
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions {
        validate: true,
        ..Default::default()
    };

    let ledger = load(&path, &options).expect("should load and process");

    // Should have processed directives
    assert!(!ledger.directives.is_empty());

    // Options should be preserved
    assert_eq!(ledger.options.title, Some("Test Ledger".to_string()));
}

#[test]
fn test_process_pipeline_without_validation() {
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions {
        validate: false,
        ..Default::default()
    };

    let ledger = load(&path, &options).expect("should load without validation");

    // Should still have directives
    assert!(!ledger.directives.is_empty());
}

#[test]
fn test_process_directives_sorted_by_date() {
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load and process");

    // Check that directives are sorted by date
    let mut last_date = None;
    for dir in &ledger.directives {
        let date = dir.value.date();
        if let Some(prev) = last_date {
            assert!(
                date >= prev,
                "directives should be sorted by date: {prev} should come before {date}"
            );
        }
        last_date = Some(date);
    }
}

#[test]
fn test_process_raw_mode() {
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions::raw();

    let ledger = load(&path, &options).expect("should load in raw mode");

    // Raw mode should still have directives but skip plugins/validation
    assert!(!ledger.directives.is_empty());
}

#[test]
fn test_process_with_extra_plugins() {
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions {
        run_plugins: false, // Don't run file plugins
        extra_plugins: vec!["check_commodity".to_string()],
        extra_plugin_configs: vec![None],
        ..Default::default()
    };

    let ledger = load(&path, &options).expect("should load with extra plugins");

    // The check_commodity plugin should have been run
    // It adds warnings for undeclared commodities
    // Just check that we processed without error
    assert!(!ledger.directives.is_empty());
}

#[test]
fn test_process_with_auto_accounts() {
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions {
        auto_accounts: true,
        ..Default::default()
    };

    let ledger = load(&path, &options).expect("should load with auto_accounts");

    // auto_accounts plugin adds Open directives for used accounts
    // Just verify it processed successfully
    assert!(!ledger.directives.is_empty());
}

#[test]
fn test_ledger_error_creation() {
    use rustledger_loader::ErrorLocation;

    // Test error creation
    let err = LedgerError::error("E001", "Test error message");
    assert_eq!(err.code, "E001");
    assert_eq!(err.message, "Test error message");
    assert!(matches!(err.severity, ErrorSeverity::Error));
    assert!(err.location.is_none());

    // Test warning creation
    let warn = LedgerError::warning("W001", "Test warning");
    assert!(matches!(warn.severity, ErrorSeverity::Warning));

    // Test with location
    let err_with_loc = LedgerError::error("E002", "Located error").with_location(ErrorLocation {
        file: std::path::PathBuf::from("test.beancount"),
        line: 10,
        column: 5,
    });
    assert!(err_with_loc.location.is_some());
    let loc = err_with_loc.location.unwrap();
    assert_eq!(loc.line, 10);
    assert_eq!(loc.column, 5);
}

#[test]
fn test_load_options_default() {
    let options = LoadOptions::default();

    assert!(options.validate);
    assert!(options.run_plugins);
    assert!(!options.auto_accounts);
    assert!(options.extra_plugins.is_empty());
    assert!(!options.path_security);
}

#[test]
fn test_load_options_raw() {
    let options = LoadOptions::raw();

    assert!(!options.validate);
    assert!(!options.run_plugins);
    assert!(!options.auto_accounts);
}

#[test]
fn test_process_from_load_result() {
    // Test calling process() directly on a LoadResult
    let path = fixtures_path("simple.beancount");
    let raw = load_raw(&path).expect("should load raw");

    let options = LoadOptions {
        validate: true,
        ..Default::default()
    };

    let ledger = process(raw, &options).expect("should process");
    assert!(!ledger.directives.is_empty());
}

#[test]
fn test_process_preserves_display_context() {
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load");

    // Display context should be available for formatting
    // Just check it exists (it's populated from directives)
    let _ctx = &ledger.display_context;
    // If we got here, display context was created successfully
}

// ============================================================================
// Booking Method Default Tests (Issue #775)
// ============================================================================

#[test]
fn test_file_level_booking_method_applied() {
    // The file has `option "booking_method" "FIFO"` and a sell posting
    // that matches 2 lots. Under STRICT this would be an ambiguous lot
    // match error. Under FIFO the oldest lot is selected.
    let path = fixtures_path("booking_method_fifo.beancount");
    let options = LoadOptions::default(); // default = Strict, but file says FIFO

    let ledger = load(&path, &options).expect("should load and process");

    // No booking errors — FIFO resolves the ambiguity.
    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors under file-level FIFO, got: {booking_errors:?}"
    );
}

#[test]
fn test_api_booking_method_used_when_file_does_not_set_option() {
    // simple.beancount does NOT set `option "booking_method"`. The
    // API-level LoadOptions.booking_method should be used as-is.
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions {
        booking_method: rustledger_core::BookingMethod::Fifo,
        ..Default::default()
    };

    let ledger = load(&path, &options).expect("should load and process");

    // No errors — simple.beancount has no cost-based transactions, so
    // the booking method doesn't matter. But the important thing is
    // that the API-level override is accepted (not overridden by the
    // file's default "STRICT").
    assert!(
        ledger.errors.is_empty(),
        "unexpected errors: {:?}",
        ledger.errors
    );
}

// ============================================================================
// Booking Method Tests for All Methods
// ============================================================================

#[test]
fn test_booking_method_lifo() {
    let path = fixtures_path("booking_lifo.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load and process");

    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors under LIFO, got: {booking_errors:?}"
    );
}

#[test]
fn test_booking_method_hifo() {
    let path = fixtures_path("booking_hifo.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load and process");

    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors under HIFO, got: {booking_errors:?}"
    );
}

#[test]
fn test_booking_method_average() {
    // Note: AVERAGE is a rustledger extension — Python beancount v3.2.0
    // does not implement it and reports "AVERAGE method is not supported".
    // This test verifies rustledger handles it correctly without errors.
    let path = fixtures_path("booking_average.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load and process");

    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors under AVERAGE, got: {booking_errors:?}"
    );
}

#[test]
fn test_booking_method_none() {
    let path = fixtures_path("booking_none.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load and process");

    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors under NONE, got: {booking_errors:?}"
    );
}

#[test]
fn test_booking_method_strict_with_size() {
    let path = fixtures_path("booking_strict_with_size.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load and process");

    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors under STRICT_WITH_SIZE, got: {booking_errors:?}"
    );
}

#[test]
fn test_booking_method_strict_ambiguous_errors() {
    let path = fixtures_path("booking_strict_ambiguous.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load and process");

    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        !booking_errors.is_empty(),
        "expected BOOK errors under STRICT with ambiguous lots, got: {booking_errors:?}"
    );
}

#[test]
fn test_per_account_booking_method() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("per_account_booking.beancount");
    std::fs::write(
        &path,
        r#"option "operating_currency" "USD"
option "booking_method" "STRICT"

2020-01-01 open Assets:Stock "FIFO"
2020-01-01 open Assets:Cash    USD

2020-02-01 * "Buy lot 1"
  Assets:Stock    10 CORP {1 USD}
  Assets:Cash    -10 USD

2020-03-01 * "Buy lot 2"
  Assets:Stock    10 CORP {2 USD}
  Assets:Cash    -20 USD

; Sell 5 - per-account FIFO should match lot 1 without ambiguity
2020-04-01 * "Sell"
  Assets:Stock    -5 CORP {}
  Assets:Cash      10 USD
"#,
    )
    .unwrap();

    let options = LoadOptions::default(); // default = Strict
    let ledger = load(&path, &options).expect("should load and process");

    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors with per-account FIFO override, got: {booking_errors:?}"
    );
}

#[test]
fn test_booking_method_api_override() {
    // File sets FIFO, but API overrides to LIFO
    let path = fixtures_path("booking_method_fifo.beancount");
    let options = LoadOptions {
        booking_method: rustledger_core::BookingMethod::Lifo,
        ..Default::default()
    };

    let ledger = load(&path, &options).expect("should load and process");

    // File-level option takes precedence when explicitly set
    let booking_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert!(
        booking_errors.is_empty(),
        "expected no BOOK errors (file FIFO overrides API LIFO), got: {booking_errors:?}"
    );
}

// ============================================================================
// Document Discovery Tests (Issue #466)
// ============================================================================

#[test]
fn test_document_discovery_from_option() {
    // Test that documents are auto-discovered from `option "documents"` directories.
    // See: https://github.com/rustledger/rustledger/issues/466
    let path = fixtures_path("doc_discovery.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load with document discovery");

    // Count document directives
    let documents: Vec<_> = ledger
        .directives
        .iter()
        .filter_map(|d| {
            if let rustledger_core::Directive::Document(doc) = &d.value {
                Some(doc)
            } else {
                None
            }
        })
        .collect();

    // Should have discovered 3 documents:
    // - Assets/Bank/Checking/2024-01-15.statement.pdf
    // - Assets/Bank/Checking/2024-02-15.statement.pdf
    // - Expenses/Food/2024-03-10.receipt.jpg
    assert_eq!(
        documents.len(),
        3,
        "expected 3 discovered documents, got: {documents:?}"
    );

    // Check accounts are correctly constructed from directory paths
    let accounts: Vec<&str> = documents.iter().map(|d| d.account.as_ref()).collect();
    assert!(
        accounts.contains(&"Assets:Bank:Checking"),
        "should have Assets:Bank:Checking document"
    );
    assert!(
        accounts.contains(&"Expenses:Food"),
        "should have Expenses:Food document"
    );

    // Check dates are correctly parsed from filenames
    let dates: Vec<_> = documents.iter().map(|d| d.date.to_string()).collect();
    assert!(
        dates.contains(&"2024-01-15".to_string()),
        "should have document dated 2024-01-15"
    );
    assert!(
        dates.contains(&"2024-02-15".to_string()),
        "should have document dated 2024-02-15"
    );
    assert!(
        dates.contains(&"2024-03-10".to_string()),
        "should have document dated 2024-03-10"
    );
}

#[test]
fn test_document_discovery_no_option() {
    // Test that document discovery doesn't happen when option "documents" is not set
    let path = fixtures_path("simple.beancount");
    let options = LoadOptions::default();

    // simple.beancount doesn't have option "documents", so no discovery should happen
    let ledger = load(&path, &options).expect("should load");

    // Count document directives (should be 0)
    let doc_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Document(_)))
        .count();

    assert_eq!(doc_count, 0, "should have no documents without option");
}

#[test]
fn test_document_discovery_no_duplicates() {
    // Test that document discovery doesn't create duplicates if a document directive
    // already exists for one of the discoverable files.
    //
    // The `doc_discovery_with_explicit.beancount` fixture:
    //   * Enables document discovery for `documents/` directory
    //   * Contains an explicit `document` directive for one file that would also be discovered
    //
    // If de-duplication is working correctly, the explicitly referenced file must not
    // be added again by discovery.
    let path = fixtures_path("doc_discovery_with_explicit.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load");

    let doc_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Document(_)))
        .count();

    // The fixture has 3 document files in the directory:
    //   - documents/Assets/Bank/Checking/2024-01-15.statement.pdf
    //   - documents/Assets/Bank/Checking/2024-02-15.statement.pdf
    //   - documents/Expenses/Food/2024-03-10.receipt.jpg
    // One of them (2024-01-15.statement.pdf) is explicitly declared in the file.
    // If duplicates were being created, we'd see 4 documents instead of 3.
    assert_eq!(
        doc_count, 3,
        "document discovery should not create duplicate Document directives"
    );
}

// ============================================================================
// Plugin execution through process::process() pipeline (Issue #788)
// ============================================================================

/// Test that plugins declared in a beancount file execute through the
/// process.rs pipeline and their output is visible in the Ledger.
///
/// `auto_accounts` should synthesize Open directives for all implicitly-used
/// accounts. Without the plugin, these accounts would have no opens.
#[test]
fn test_plugin_execution_auto_accounts() {
    use rustledger_loader::{LoadOptions, load};

    let path = fixtures_path("auto_accounts_plugin.beancount");
    let ledger = load(&path, &LoadOptions::default()).expect("should load file with plugin");

    // The file has NO explicit open directives — auto_accounts should
    // generate them for Assets:Bank:Checking, Income:Salary, Expenses:Food.
    let opens: Vec<_> = ledger
        .directives
        .iter()
        .filter_map(|d| {
            if let rustledger_core::Directive::Open(o) = &d.value {
                Some(o.account.to_string())
            } else {
                None
            }
        })
        .collect();

    assert!(
        opens.iter().any(|a| a == "Assets:Bank:Checking"),
        "auto_accounts should generate Open for Assets:Bank:Checking. Opens: {opens:?}"
    );
    assert!(
        opens.iter().any(|a| a == "Income:Salary"),
        "auto_accounts should generate Open for Income:Salary. Opens: {opens:?}"
    );
    assert!(
        opens.iter().any(|a| a == "Expenses:Food"),
        "auto_accounts should generate Open for Expenses:Food. Opens: {opens:?}"
    );

    // Validation should pass (no E1001 errors) since opens are auto-generated.
    let validation_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "E1001").collect();
    assert!(
        validation_errors.is_empty(),
        "auto_accounts should prevent E1001 (account not opened). Got: {validation_errors:?}"
    );
}

/// Test the interaction between booking and plugins: booking runs first,
/// then plugins see booked transactions.
///
/// With FIFO booking + `auto_accounts`: the sell transaction should match
/// lot 1 (FIFO) without ambiguity, and `auto_accounts` should generate
/// opens for the implicitly-used accounts.
#[test]
fn test_plugin_and_booking_interaction() {
    use rustledger_loader::{LoadOptions, load};

    let path = fixtures_path("fifo_with_plugin.beancount");
    let ledger = load(&path, &LoadOptions::default()).expect("should load FIFO + plugin file");

    // auto_accounts should have generated opens
    let opens: Vec<_> = ledger
        .directives
        .iter()
        .filter_map(|d| {
            if let rustledger_core::Directive::Open(o) = &d.value {
                Some(o.account.to_string())
            } else {
                None
            }
        })
        .collect();

    assert!(
        opens.iter().any(|a| a == "Assets:Stock"),
        "auto_accounts should generate Open for Assets:Stock. Opens: {opens:?}"
    );
    assert!(
        opens.iter().any(|a| a == "Assets:Cash"),
        "auto_accounts should generate Open for Assets:Cash. Opens: {opens:?}"
    );

    // FIFO booking should have resolved the sell without ambiguity error.
    // The sell is -5 CORP {} which should match lot 1 (cost 1 USD) under FIFO.
    let booking_errors: Vec<_> = ledger
        .errors
        .iter()
        .filter(|e| e.message.contains("ambiguous"))
        .collect();
    assert!(
        booking_errors.is_empty(),
        "FIFO booking should resolve sell without ambiguity. Errors: {booking_errors:?}"
    );

    // No validation errors expected (auto_accounts generates opens, FIFO resolves lots)
    assert!(
        ledger.errors.is_empty(),
        "No errors expected with FIFO + auto_accounts. Got: {:?}",
        ledger.errors
    );
}

/// Test that unknown plugin names are gracefully skipped without crashing.
///
/// The loader's `run_plugins()` only executes native plugins. Non-native
/// plugin names (Python modules, unknown names) are silently skipped.
/// This test verifies the pipeline doesn't panic or error on unknown plugins.
#[test]
fn test_unknown_plugin_skipped_gracefully() {
    use rustledger_loader::{LoadOptions, load};

    let path = fixtures_path("unknown_plugin.beancount");
    let ledger =
        load(&path, &LoadOptions::default()).expect("should load file with unknown plugin");

    // Unknown plugins should NOT crash the pipeline — they report an error
    // but loading continues with the remaining directives.
    assert!(
        !ledger.directives.is_empty(),
        "Ledger should still have directives even with unknown plugin"
    );

    // Should report the plugin as not found (not silently skip)
    assert!(
        ledger.errors.iter().any(|e| e.phase == "plugin"),
        "expected a plugin error for unknown plugin, got: {:?}",
        ledger.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

/// Test that plugin-synthesized directives are visible in the `Ledger`.
/// This verifies that the directive conversion round-trip (`Directive` →
/// `DirectiveWrapper` → `Directive`) preserves the synthesized data.
#[test]
fn test_plugin_output_directives_visible_in_ledger() {
    use rustledger_loader::{LoadOptions, load};

    let path = fixtures_path("auto_accounts_plugin.beancount");
    let ledger = load(&path, &LoadOptions::default()).expect("should load");

    // Count directives: the file has 2 transactions. auto_accounts should
    // add 3 open directives (Assets:Bank:Checking, Income:Salary, Expenses:Food).
    // Total should be at least 5.
    let total = ledger.directives.len();
    let txn_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Transaction(_)))
        .count();
    let open_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
        .count();

    assert_eq!(txn_count, 2, "Should have 2 transactions");
    assert!(
        open_count >= 3,
        "auto_accounts should synthesize at least 3 Open directives. Got {open_count}"
    );
    assert!(
        total >= 5,
        "Total directives should be at least 5 (2 txn + 3 opens). Got {total}"
    );
}

/// Test that parallel loading of multiple sibling includes produces
/// the same results as sequential loading. The fixture has a root file
/// with 3 includes (triggering the parallel path on `DiskFileSystem`).
#[test]
fn test_parallel_loading_multiple_includes() {
    use rustledger_loader::{LoadOptions, load};

    let path = fixtures_path("parallel_main.beancount");
    let ledger = load(&path, &LoadOptions::default()).expect("should load parallel fixture");

    // All 3 accounts should be opened (from parallel_a and parallel_b)
    let opens: Vec<_> = ledger
        .directives
        .iter()
        .filter_map(|d| {
            if let rustledger_core::Directive::Open(o) = &d.value {
                Some(o.account.to_string())
            } else {
                None
            }
        })
        .collect();

    assert!(
        opens.iter().any(|a| a == "Assets:Bank"),
        "Should have Assets:Bank from parallel_a. Opens: {opens:?}"
    );
    assert!(
        opens.iter().any(|a| a == "Expenses:Food"),
        "Should have Expenses:Food from parallel_a. Opens: {opens:?}"
    );
    assert!(
        opens.iter().any(|a| a == "Income:Salary"),
        "Should have Income:Salary from parallel_b. Opens: {opens:?}"
    );

    // 2 transactions (from parallel_a and parallel_b)
    let txn_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Transaction(_)))
        .count();
    assert_eq!(
        txn_count, 2,
        "Should have 2 transactions from included files"
    );

    // 1 balance assertion (from parallel_c)
    let balance_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, rustledger_core::Directive::Balance(_)))
        .count();
    assert_eq!(
        balance_count, 1,
        "Should have 1 balance assertion from parallel_c"
    );

    // Options from root file should be preserved
    assert_eq!(
        ledger.options.title,
        Some("Parallel Test Ledger".to_string())
    );

    // No errors expected
    assert!(
        ledger.errors.is_empty(),
        "Parallel loading should produce no errors. Got: {:?}",
        ledger.errors
    );

    // Source map should have 4 files (root + 3 includes)
    assert_eq!(
        ledger.source_map.files().len(),
        4,
        "Source map should have 4 files"
    );
}

/// Test that WASM plugins are attempted during load (not silently skipped).
///
/// This is a regression test for issue #842: WASM plugins were parsed
/// but never executed by the loader, only by `rledger check`.
///
/// Note: the passthrough WASM plugin may fail in some environments
/// (e.g., coverage instrumentation), so we verify the plugin was
/// *attempted* (not "not found"), not that execution succeeded.
#[cfg(feature = "wasm-plugins")]
#[test]
fn test_wasm_plugin_executed_during_load() {
    use rustledger_loader::{LoadOptions, load};

    let path = fixtures_path("with_wasm_plugin.beancount");
    let options = LoadOptions::default();

    let ledger = load(&path, &options).expect("should load file with WASM plugin");

    // The key assertion: the plugin was NOT reported as "not found".
    // Before the fix, unknown plugins (including .wasm) were silently skipped
    // with no error at all. Now they're either executed or report a WASM error.
    let not_found_errors: Vec<_> = ledger
        .errors
        .iter()
        .filter(|e| e.message.contains("not found") || e.message.contains("Not found"))
        .collect();
    assert!(
        not_found_errors.is_empty(),
        "WASM plugin should be recognized (not 'not found'), got: {not_found_errors:?}"
    );

    assert!(
        !ledger.directives.is_empty(),
        "directives should survive WASM plugin processing"
    );
}

/// Test that unknown plugins report an error (not silently skipped).
#[test]
fn test_unknown_plugin_reports_error() {
    use rustledger_loader::{LoadOptions, load};

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test.beancount");
    std::fs::write(
        &path,
        "plugin \"nonexistent_plugin\"\n2024-01-01 open Assets:Bank USD\n",
    )
    .unwrap();

    let options = LoadOptions::default();
    let ledger = load(&path, &options).expect("should not panic");

    // Should have an error about the unknown plugin
    assert!(
        ledger
            .errors
            .iter()
            .any(|e| e.message.contains("not found")),
        "expected 'not found' error for unknown plugin, got: {:?}",
        ledger.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

/// Test that Python module-style plugins report helpful errors when feature is disabled.
#[test]
fn test_python_module_plugin_reports_error() {
    use rustledger_loader::{LoadOptions, load};

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test.beancount");
    std::fs::write(
        &path,
        "plugin \"beancount.plugins.my_custom_plugin\"\n2024-01-01 open Assets:Bank USD\n",
    )
    .unwrap();

    let options = LoadOptions::default();
    let ledger = load(&path, &options).expect("should not panic");

    // Should have an error — not silently skip
    assert!(
        !ledger.errors.is_empty(),
        "python module plugin should produce an error, not be silently skipped"
    );
}

/// Test that missing WASM file produces a clear error.
#[cfg(feature = "wasm-plugins")]
#[test]
fn test_missing_wasm_plugin_reports_error() {
    use rustledger_loader::{LoadOptions, load};

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test.beancount");
    std::fs::write(
        &path,
        "plugin \"does_not_exist.wasm\"\n2024-01-01 open Assets:Bank USD\n",
    )
    .unwrap();

    let options = LoadOptions::default();
    let ledger = load(&path, &options).expect("should not panic");

    assert!(
        ledger
            .errors
            .iter()
            .any(|e| e.message.contains("WASM") && e.message.contains("failed")),
        "expected WASM error for missing file, got: {:?}",
        ledger.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

// ----- precision: N metadata on commodity directives (issue #991) ------------
//
// All tests use load_raw (not the full load() path) so the assertions stay
// scoped to display_context construction and aren't affected by validation /
// booking. Validator behavior for invalid values is exercised separately.

#[test]
fn precision_metadata_sets_fixed_precision() {
    // `precision: 2` alone should pin USD to 2dp regardless of the inferred
    // dp distribution (here 4dp would normally win under MostCommon).
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_meta.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 commodity USD
  precision: 2

2024-01-01 open Assets:Cash
2024-01-01 open Income:Salary

2024-01-15 * "test"
  Assets:Cash       100.0000 USD
  Income:Salary
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(
        result.display_context.get_precision("USD"),
        Some(2),
        "commodity precision metadata should pin USD to 2dp"
    );
    assert!(result.display_context.has_fixed_precision("USD"));
}

#[test]
fn precision_metadata_zero_is_valid() {
    // JPY-style integer-only currency: `precision: 0` must be honored.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_zero.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 commodity JPY
  precision: 0

2024-01-01 open Assets:Cash
2024-01-15 * "yen"
  Assets:Cash    1000 JPY
  Assets:Cash   -1000 JPY
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(result.display_context.get_precision("JPY"), Some(0));
}

#[test]
fn precision_metadata_wins_over_option_display_precision() {
    // option says 2dp (`USD:0.01` — the colon-encoded form rledger's
    // option parser accepts; precision = scale of the example value),
    // commodity meta says 4dp → meta wins (per #991).
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_vs_option.beancount");
    std::fs::write(
        &path,
        r#"option "display_precision" "USD:0.01"

2024-01-01 commodity USD
  precision: 4

2024-01-01 open Assets:Cash
2024-01-15 * "test"
  Assets:Cash    1.00 USD
  Assets:Cash   -1.00 USD
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(
        result.display_context.get_precision("USD"),
        Some(4),
        "commodity metadata must override option display_precision"
    );
}

#[test]
fn precision_metadata_multi_declaration_last_wins() {
    // Two commodity directives for USD; the second's precision wins.
    // Last-wins matches typical option-stacking semantics.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_multi.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 commodity USD
  precision: 2

2024-06-01 commodity USD
  precision: 6

2024-01-01 open Assets:Cash
2024-01-15 * "test"
  Assets:Cash    1 USD
  Assets:Cash   -1 USD
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(
        result.display_context.get_precision("USD"),
        Some(6),
        "last commodity declaration's precision must win"
    );
}

#[test]
fn precision_metadata_invalid_falls_back_to_inference() {
    // `precision: -1` is invalid → loader silently skips it. With no
    // `option "display_precision"` set, inference takes over (USD postings
    // are 4dp in this fixture). The option-present case is covered
    // separately by `precision_metadata_invalid_with_option_keeps_option`.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_invalid.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 commodity USD
  precision: -1

2024-01-01 open Assets:Cash
2024-01-15 * "test"
  Assets:Cash    1.2345 USD
  Assets:Cash   -1.2345 USD
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(
        result.display_context.get_precision("USD"),
        Some(4),
        "invalid precision must fall back to inferred dp"
    );
    assert!(
        !result.display_context.has_fixed_precision("USD"),
        "invalid precision must NOT install a fixed override"
    );
}

#[test]
fn precision_metadata_non_integer_falls_back() {
    // `precision: 2.5` is non-integer → invalid → inference wins (3dp here).
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_non_integer.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 commodity USD
  precision: 2.5

2024-01-01 open Assets:Cash
2024-01-15 * "test"
  Assets:Cash    1.234 USD
  Assets:Cash   -1.234 USD
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(result.display_context.get_precision("USD"), Some(3));
    assert!(!result.display_context.has_fixed_precision("USD"));
}

#[test]
fn precision_metadata_invalid_with_option_keeps_option() {
    // option says 2dp; commodity meta is invalid (-1). The invalid value is
    // ignored; the option override stays at 2dp. Pins the precedence stack
    // documented in docs/commands/query.md ("Overriding inference"):
    //   valid precision metadata > option "display_precision" > inference.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_invalid_with_option.beancount");
    std::fs::write(
        &path,
        r#"option "display_precision" "USD:0.01"

2024-01-01 commodity USD
  precision: -1

2024-01-01 open Assets:Cash
2024-01-15 * "test"
  Assets:Cash    1.2345 USD
  Assets:Cash   -1.2345 USD
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(
        result.display_context.get_precision("USD"),
        Some(2),
        "option fixed precision must persist when commodity meta is invalid"
    );
    assert!(
        result.display_context.has_fixed_precision("USD"),
        "option fixed override must remain in effect"
    );
}

#[test]
fn precision_metadata_valid_then_invalid_keeps_first() {
    // Same currency declared twice: first valid (2), second invalid (-1).
    // The invalid declaration is silently skipped by the loader, so the
    // earlier valid override stays in place. This pins the
    // "first-valid-wins-when-later-is-invalid" behavior — it's a
    // deliberate choice over strict last-wins because falling back to
    // inference because of a typo two pages later would be more
    // surprising. The validator still emits E5003 for the bad one
    // (covered separately).
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_valid_then_invalid.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 commodity USD
  precision: 2

2024-06-01 commodity USD
  precision: -1

2024-01-01 open Assets:Cash
2024-01-15 * "test"
  Assets:Cash    1.2345 USD
  Assets:Cash   -1.2345 USD
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(
        result.display_context.get_precision("USD"),
        Some(2),
        "earlier valid precision must persist when a later declaration is invalid"
    );
    assert!(result.display_context.has_fixed_precision("USD"));
}

#[test]
fn precision_metadata_string_value_falls_back() {
    // `precision: "abc"` is the wrong MetaValue variant → invalid →
    // inference wins (2dp here).
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("precision_string.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 commodity USD
  precision: "abc"

2024-01-01 open Assets:Cash
2024-01-15 * "test"
  Assets:Cash    1.23 USD
  Assets:Cash   -1.23 USD
"#,
    )
    .unwrap();
    let result = load_raw(&path).expect("load");
    assert_eq!(result.display_context.get_precision("USD"), Some(2));
    assert!(!result.display_context.has_fixed_precision("USD"));
}

#[test]
fn same_date_directives_keep_file_order_after_booking() {
    // Issue #1049: the loader's pre-booking sort uses
    // `(date, priority, has_cost_reduction)` so the booking engine
    // sees augmentations before reductions on the same date (issue
    // #841). After booking runs, we re-sort by `(date, priority,
    // file_id, span.start)` to match Python beancount's
    // `(date, type_priority, lineno)` order — otherwise BQL output
    // diverges from bean-query on same-date tie-breaks.
    //
    // This fixture has a Sell stamped *before* a Buy in the file but
    // on the same date. Booking reorders them so the Buy creates the
    // lot first; the post-booking re-sort then restores file order
    // for downstream consumers.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("same_date_order.beancount");
    std::fs::write(
        &path,
        r#"2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash
2024-01-01 open Equity:Opening

2024-01-10 * "Initial cash"
  Assets:Cash       2000.00 USD
  Equity:Opening   -2000.00 USD

2024-01-15 * "Sell — appears first in file"
  Assets:Stock     -5 STK {100.00 USD}
  Assets:Cash     500.00 USD

2024-01-15 * "Buy — appears second in file but creates the lot"
  Assets:Stock     10 STK {100.00 USD}
  Assets:Cash   -1000.00 USD
"#,
    )
    .unwrap();
    let options = LoadOptions::default();
    let ledger = load(&path, &options).expect("should load");

    // Booking succeeded — the Sell found a matching lot from the Buy
    // even though it's textually earlier (issue #841).
    assert!(
        ledger
            .errors
            .iter()
            .all(|e| !matches!(e.severity, ErrorSeverity::Error)),
        "booking should succeed across same-date sell-before-buy: {:?}",
        ledger
            .errors
            .iter()
            .filter(|e| matches!(e.severity, ErrorSeverity::Error))
            .collect::<Vec<_>>()
    );

    // Find the two same-date transactions and assert file order is
    // preserved: the textually-first "Sell" before the textually-second "Buy".
    let target_date = jiff::civil::date(2024, 1, 15);
    let txns_on_date: Vec<&str> = ledger
        .directives
        .iter()
        .filter_map(|d| {
            if let rustledger_core::Directive::Transaction(t) = &d.value
                && t.date == target_date
            {
                return Some(t.narration.as_str());
            }
            None
        })
        .collect();
    assert_eq!(
        txns_on_date.len(),
        2,
        "expected two same-date transactions, got {txns_on_date:?}"
    );
    assert!(
        txns_on_date[0].starts_with("Sell"),
        "textually-first Sell should come first after post-booking sort, got: {txns_on_date:?}"
    );
    assert!(
        txns_on_date[1].starts_with("Buy"),
        "textually-second Buy should come second, got: {txns_on_date:?}"
    );
}

// ─── Zero-value interpolated posting handling (#877 + Python compat) ────
//
// Two competing invariants:
//
// 1. (#877) When an elided posting interpolates to zero on an account that
//    was never `open`ed, validation must still emit E1001. Pruning the
//    posting before validation hides the error.
//
// 2. (Python compat) When the elided posting interpolates to zero on a
//    legitimately-opened account, user-facing output (BQL, JSON, format)
//    should NOT show it. Python beancount drops these from its rendered
//    output; rledger should too.
//
// The fix: the loader's `process()` runs `validate_early` BEFORE
// booking, so account-presence checks (E1001) fire on every elided
// posting — including ones that would later interpolate to zero.
// Then booking runs and prunes zero-value interpolated postings (to
// match Python's user-facing display). Then `validate_late` runs for
// balance/inventory checks. See `rustledger_validate::Phase` and the
// "Python Compatibility Policy" section in CLAUDE.md.

#[test]
fn test_zero_interpolated_posting_pruned_on_opened_account() {
    use rustledger_loader::{LoadOptions, process};

    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("zero_interp.beancount");
    std::fs::write(
        &path,
        "option \"operating_currency\" \"USD\"\n\
         2020-01-01 open Assets:Bank USD\n\
         2020-01-01 open Income:Trading\n\
         \n\
         2020-01-15 * \"Balanced trade with zero income\"\n  \
         Assets:Bank      100 USD\n  \
         Assets:Bank     -100 USD\n  \
         Income:Trading\n",
    )
    .unwrap();

    let raw = rustledger_loader::load_raw(&path).expect("load raw");
    let ledger = process(raw, &LoadOptions::default()).expect("process");

    let txn = ledger
        .directives
        .iter()
        .find_map(|d| match &d.value {
            rustledger_core::Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .expect("transaction present");

    // The Income:Trading posting was interpolated to 0 USD and should
    // have been pruned post-validation.
    let accounts: Vec<&str> = txn.postings.iter().map(|p| p.account.as_str()).collect();
    assert!(
        !accounts.contains(&"Income:Trading"),
        "zero-value interpolated Income:Trading should be pruned, got: {accounts:?}"
    );
    assert_eq!(txn.postings.len(), 2, "expected only the two cash postings");

    // No validation errors expected on opened accounts.
    let errors: Vec<&str> = ledger.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(
        errors.is_empty(),
        "expected no errors on legitimately-opened accounts, got: {errors:?}"
    );
}

#[test]
fn test_zero_interpolated_posting_keeps_e1001_on_unopened_account() {
    // Reproduces #877. The interpolated posting on Expenses:NeverOpened
    // resolves to 0 USD but must still surface as E1001 because the
    // account was never opened.
    use rustledger_loader::{LoadOptions, process};

    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("issue877.beancount");
    std::fs::write(
        &path,
        "option \"operating_currency\" \"USD\"\n\
         2020-01-01 open Assets:Bank USD\n\
         \n\
         2020-01-15 * \"Zero balance to unopened account\"\n  \
         Assets:Bank  0.00 USD\n  \
         Expenses:NeverOpened\n",
    )
    .unwrap();

    let raw = rustledger_loader::load_raw(&path).expect("load raw");
    let ledger = process(raw, &LoadOptions::default()).expect("process");

    let has_e1001 = ledger.errors.iter().any(|e| e.code == "E1001");
    assert!(
        has_e1001,
        "expected E1001 for never-opened account (per #877); got errors: {:?}",
        ledger.errors.iter().map(|e| &e.code).collect::<Vec<_>>()
    );
}

#[test]
fn test_non_zero_interpolated_posting_is_preserved() {
    // Sanity: only ZERO-value interpolated postings are pruned. A
    // legitimate interpolated residual (non-zero) must stay in output.
    use rustledger_loader::{LoadOptions, process};

    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("nonzero_interp.beancount");
    std::fs::write(
        &path,
        "option \"operating_currency\" \"USD\"\n\
         2020-01-01 open Assets:Bank USD\n\
         2020-01-01 open Income:Trading\n\
         \n\
         2020-01-15 * \"Trade with non-zero income\"\n  \
         Assets:Bank      150 USD\n  \
         Assets:Bank     -100 USD\n  \
         Income:Trading\n",
    )
    .unwrap();

    let raw = rustledger_loader::load_raw(&path).expect("load raw");
    let ledger = process(raw, &LoadOptions::default()).expect("process");

    let txn = ledger
        .directives
        .iter()
        .find_map(|d| match &d.value {
            rustledger_core::Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .expect("transaction present");

    let income = txn
        .postings
        .iter()
        .find(|p| p.account.as_str() == "Income:Trading")
        .expect("Income:Trading should still be present (interpolated -50 USD)");
    let amount = income
        .units
        .as_ref()
        .and_then(|u| u.as_amount())
        .expect("filled");
    assert_eq!(amount.number, rust_decimal::Decimal::from(-50));
}

// (Test for the INTERPOLATED_MARKER side channel was deleted with the
// rest of that workaround when the validate-phase-split landed; the
// marker no longer exists.)

/// Regression for the booking-failure partition: when a transaction
/// fails booking (e.g. `NoMatchingLot`), the loader removes it from
/// the directive flow that regular plugins and Late validation see,
/// then re-merges it for the final `Ledger.directives` output.
/// Without partition, the failed txn's unresolved-cost state cascades
/// into misleading downstream validation errors (and the prior
/// `failed_bookings`-keyed-by-span workaround broke under plugins
/// that round-trip directives through the wrapper protocol).
#[test]
fn test_booking_failure_partitioned_from_late_validation() {
    use rustledger_core::Directive;
    use rustledger_loader::{LoadOptions, load};

    let path = fixtures_path("booking_failure_partition.beancount");
    let ledger = load(&path, &LoadOptions::default()).expect("should load");

    // Exactly one BOOK error for the failed txn.
    let book_errors: Vec<_> = ledger.errors.iter().filter(|e| e.code == "BOOK").collect();
    assert_eq!(
        book_errors.len(),
        1,
        "expected exactly one BOOK error on the failing txn; got: {book_errors:?}"
    );

    // No cascading validation errors — partition keeps the failed txn
    // out of Late's iteration.
    let cascading: Vec<_> = ledger
        .errors
        .iter()
        .filter(|e| e.code.starts_with('E') || e.code.starts_with('W'))
        .collect();
    assert!(
        cascading.is_empty(),
        "no validation errors expected after partition; got: {cascading:?}"
    );

    // The failed txn is still present in the output for the user to
    // see — we partition during processing, but re-merge for display.
    let txn_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, Directive::Transaction(_)))
        .count();
    assert_eq!(
        txn_count, 3,
        "all three transactions should appear in final Ledger output (including the failed one); got {txn_count}"
    );
}
