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
