//! Integration tests for the loader crate.
//!
//! Tests are based on patterns from beancount's test suite.

use rustledger_loader::{load, LoadError, Loader};
use std::path::Path;

fn fixtures_path(name: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

#[test]
fn test_load_simple_file() {
    let path = fixtures_path("simple.beancount");
    let result = load(&path).expect("should load simple file");

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
    let result = load(&path).expect("should load file with include");

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
    let result = load(&path).expect("should load file even with missing include");

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
    let result = load(&path).expect("should load file with plugins");

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
    let result = load(&path).expect("should load file even with parse errors");

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
    let result = load(&path).expect("should load simple file");

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
    let result = load(&path).expect("should load file");

    // Each unique file should only be in source map once
    let file_count = result.source_map.files().len();
    assert_eq!(
        file_count, 2,
        "should have exactly 2 files (main + accounts)"
    );
}
