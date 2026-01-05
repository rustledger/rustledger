//! WASM-specific tests using wasm-bindgen-test.
//!
//! These tests run in an actual WASM environment (browser or Node.js).
//! Run with: `wasm-pack test --node` or `wasm-pack test --headless --firefox`

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

// Helper to extract a field from a JsValue object
fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

fn get_array_length(obj: &JsValue) -> u32 {
    js_sys::Array::from(obj).length()
}

#[wasm_bindgen_test]
fn test_parse_valid() {
    let source = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let result = rustledger_wasm::parse(source).expect("parse should not throw");

    // Check errors array is empty
    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");

    // Check ledger exists
    let ledger = get_field(&result, "ledger");
    assert!(!ledger.is_undefined(), "ledger should exist");

    // Check directives count
    let directives = get_field(&ledger, "directives");
    assert_eq!(get_array_length(&directives), 2, "should have 2 directives");
}

#[wasm_bindgen_test]
fn test_parse_invalid() {
    let source = "this is not valid beancount syntax";

    let result = rustledger_wasm::parse(source).expect("parse should not throw");

    // Check errors array has items
    let errors = get_field(&result, "errors");
    assert!(get_array_length(&errors) > 0, "should have parse errors");
}

#[wasm_bindgen_test]
fn test_validate_source_valid() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let result = rustledger_wasm::validate_source(source).expect("validate should not throw");

    let valid = get_field(&result, "valid");
    assert_eq!(valid, JsValue::TRUE, "ledger should be valid");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");
}

#[wasm_bindgen_test]
fn test_validate_source_invalid() {
    let source = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let result = rustledger_wasm::validate_source(source).expect("validate should not throw");

    let valid = get_field(&result, "valid");
    assert_eq!(valid, JsValue::FALSE, "ledger should be invalid");

    let errors = get_field(&result, "errors");
    assert!(
        get_array_length(&errors) > 0,
        "should have validation errors for unopened account"
    );
}

#[wasm_bindgen_test]
fn test_query() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let result =
        rustledger_wasm::query(source, "SELECT account, sum(position)").expect("query should work");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");

    let columns = get_field(&result, "columns");
    assert_eq!(get_array_length(&columns), 2, "should have 2 columns");

    let rows = get_field(&result, "rows");
    assert!(get_array_length(&rows) > 0, "should have results");
}

#[wasm_bindgen_test]
fn test_format() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let result = rustledger_wasm::format(source).expect("format should work");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");

    let formatted = get_field(&result, "formatted");
    assert!(!formatted.is_null(), "should have formatted output");
}

#[wasm_bindgen_test]
fn test_list_plugins() {
    let result = rustledger_wasm::list_plugins().expect("list_plugins should work");

    let arr = js_sys::Array::from(&result);
    assert!(arr.length() > 0, "should have plugins");

    // Check first plugin has name and description
    let first = arr.get(0);
    let name = get_field(&first, "name");
    let description = get_field(&first, "description");

    assert!(name.is_string(), "plugin should have name");
    assert!(description.is_string(), "plugin should have description");
}

#[wasm_bindgen_test]
fn test_bql_completions() {
    let result = rustledger_wasm::bql_completions("SEL", 3).expect("completions should work");

    let completions = get_field(&result, "completions");
    assert!(
        get_array_length(&completions) > 0,
        "should have completions for 'SEL'"
    );
}

#[wasm_bindgen_test]
fn test_version() {
    let version = rustledger_wasm::version();
    assert!(!version.is_empty(), "version should not be empty");
}

#[wasm_bindgen_test]
fn test_error_has_line_numbers() {
    let source = r#"
2024-01-01 open Assets:Bank USD
invalid syntax here
"#;

    let result = rustledger_wasm::parse(source).expect("parse should not throw");

    let errors = get_field(&result, "errors");
    assert!(get_array_length(&errors) > 0, "should have errors");

    let first_error = js_sys::Array::from(&errors).get(0);
    let line = get_field(&first_error, "line");

    // Line should be a number (not undefined)
    assert!(line.as_f64().is_some(), "error should have line number");
}

#[wasm_bindgen_test]
fn test_serialization_uses_null_not_undefined() {
    // Test that None values serialize as null, not undefined
    let source = r#"
2024-01-01 open Assets:Bank USD
"#;

    let result = rustledger_wasm::parse(source).expect("parse should work");
    let ledger = get_field(&result, "ledger");
    let options = get_field(&ledger, "options");
    let title = get_field(&options, "title");

    // With json_compatible(), None serializes as null
    assert!(title.is_null(), "title should be null, not undefined");
}

#[wasm_bindgen_test]
fn test_expand_pads() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Equity:Opening USD

2024-01-01 pad Assets:Bank Equity:Opening

2024-01-15 balance Assets:Bank 1000.00 USD
"#;

    let result = rustledger_wasm::expand_pads(source).expect("expand_pads should work");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");

    let directives = get_field(&result, "directives");
    assert!(get_array_length(&directives) > 0, "should have directives");

    let padding_txns = get_field(&result, "padding_transactions");
    // Pad should generate a transaction to bring balance to 1000
    assert!(
        get_array_length(&padding_txns) > 0,
        "should have padding transactions"
    );
}

#[wasm_bindgen_test]
fn test_run_plugin() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    // Run the check_closing plugin (should be a no-op for valid ledger)
    let result =
        rustledger_wasm::run_plugin(source, "check_closing").expect("run_plugin should work");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");

    let directives = get_field(&result, "directives");
    assert!(get_array_length(&directives) > 0, "should have directives");
}

#[wasm_bindgen_test]
fn test_run_plugin_unknown() {
    let source = "2024-01-01 open Assets:Bank USD";

    let result = rustledger_wasm::run_plugin(source, "nonexistent_plugin")
        .expect("run_plugin should not throw");

    let errors = get_field(&result, "errors");
    assert!(
        get_array_length(&errors) > 0,
        "should have error for unknown plugin"
    );
}

#[wasm_bindgen_test]
fn test_options_extracted() {
    let source = r#"
option "title" "My Ledger"
option "operating_currency" "USD"
option "operating_currency" "EUR"

2024-01-01 open Assets:Bank USD
"#;

    let result = rustledger_wasm::parse(source).expect("parse should work");
    let ledger = get_field(&result, "ledger");
    let options = get_field(&ledger, "options");

    let title = get_field(&options, "title");
    assert_eq!(
        title.as_string().unwrap(),
        "My Ledger",
        "title should be extracted"
    );

    let currencies = get_field(&options, "operating_currencies");
    assert_eq!(
        get_array_length(&currencies),
        2,
        "should have 2 operating currencies"
    );
}

// =============================================================================
// ParsedLedger class tests
// =============================================================================

#[wasm_bindgen_test]
fn test_parsed_ledger_valid() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let ledger = rustledger_wasm::ParsedLedger::new(source);

    assert!(ledger.is_valid(), "ledger should be valid");
    assert_eq!(ledger.directive_count(), 3, "should have 3 directives");

    let errors = ledger.get_errors().expect("get_errors should work");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");
}

#[wasm_bindgen_test]
fn test_parsed_ledger_invalid() {
    let source = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let ledger = rustledger_wasm::ParsedLedger::new(source);

    assert!(!ledger.is_valid(), "ledger should be invalid");

    let errors = ledger.get_validation_errors().expect("should work");
    assert!(
        get_array_length(&errors) > 0,
        "should have validation errors"
    );
}

#[wasm_bindgen_test]
fn test_parsed_ledger_query() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let ledger = rustledger_wasm::ParsedLedger::new(source);
    let result = ledger
        .query("SELECT account, sum(position)")
        .expect("query should work");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");

    let rows = get_field(&result, "rows");
    assert!(get_array_length(&rows) > 0, "should have results");
}

#[wasm_bindgen_test]
fn test_parsed_ledger_format() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let ledger = rustledger_wasm::ParsedLedger::new(source);
    let result = ledger.format().expect("format should work");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");

    let formatted = get_field(&result, "formatted");
    assert!(!formatted.is_null(), "should have formatted output");
}

#[wasm_bindgen_test]
fn test_parsed_ledger_expand_pads() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Equity:Opening USD

2024-01-01 pad Assets:Bank Equity:Opening
2024-01-15 balance Assets:Bank 1000.00 USD
"#;

    let ledger = rustledger_wasm::ParsedLedger::new(source);
    let result = ledger.expand_pads().expect("expand_pads should work");

    let padding_txns = get_field(&result, "padding_transactions");
    assert!(
        get_array_length(&padding_txns) > 0,
        "should have padding transactions"
    );
}

#[wasm_bindgen_test]
fn test_parsed_ledger_run_plugin() {
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

    let ledger = rustledger_wasm::ParsedLedger::new(source);
    let result = ledger
        .run_plugin("check_closing")
        .expect("run_plugin should work");

    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "should have no errors");
}
