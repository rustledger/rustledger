//! JS-runtime tests for #2911: a rejected option value is reported and not
//! applied, on the WASM `Ledger` and `ParsedLedger`.
//!
//! Node-targeting (no `run_in_browser`), like `wasm_booking_method.rs`, so
//! CI's `wasm-pack test --node` step runs them.
//!
//! The issue's ledger: bean-check 3.2.3 reports only `Error for option
//! 'name_equity': Invalid root account name: 'A😀'`, and `Equity:A` stays
//! valid. rledger applied the rename, so `open Equity:A` also failed with
//! E1005.

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

const ISSUE: &str = "option \"name_equity\" \"A\u{1F600}\"\n2024-01-01 open Equity:A\n";

const FIFO: &str = "option \"booking_method\" \"fifo\"
2024-01-01 open Assets:Cash
2024-01-01 open Income:Salary
2024-01-02 * \"pay\"
  Assets:Cash  100 USD
  Income:Salary
";

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// The `code` of every error in a `getErrors` array.
fn codes(errors: &JsValue) -> Vec<String> {
    js_sys::Array::from(errors)
        .iter()
        .map(|e| get_field(&e, "code").as_string().unwrap_or_default())
        .collect()
}

fn files(text: &str) -> JsValue {
    let files = js_sys::Object::new();
    js_sys::Reflect::set(
        &files,
        &JsValue::from_str("main.beancount"),
        &JsValue::from_str(text),
    )
    .expect("set");
    files.into()
}

#[wasm_bindgen_test]
fn test_ledger_invalid_name_option_reports_only_the_option_error() {
    let ledger =
        rustledger_wasm::Ledger::from_files(files(ISSUE), "main.beancount").expect("fromFiles");
    let errors = ledger.get_errors().expect("getErrors");
    assert_eq!(codes(&errors), ["E7008"]);
}

#[wasm_bindgen_test]
fn test_parsed_ledger_invalid_name_option_reports_only_the_option_error() {
    let ledger = rustledger_wasm::ParsedLedger::new(ISSUE);
    let errors = ledger.get_errors().expect("getErrors");
    assert_eq!(codes(&errors), ["E7008"]);
}

/// An invalid `booking_method` refuses the query (no columns), with the
/// option error among the reported errors, on `Ledger.query` and
/// `ParsedLedger.query`.
#[wasm_bindgen_test]
fn test_query_invalid_booking_method_refuses() {
    let query = "SELECT narration";
    let ledger =
        rustledger_wasm::Ledger::from_files(files(FIFO), "main.beancount").expect("fromFiles");
    let parsed = rustledger_wasm::ParsedLedger::new(FIFO);
    for (surface, result) in [
        ("Ledger.query", ledger.query(query).expect("query")),
        ("ParsedLedger.query", parsed.query(query).expect("query")),
    ] {
        let columns = js_sys::Array::from(&get_field(&result, "columns"));
        assert_eq!(columns.length(), 0, "{surface}: a refusal has no columns");
        let messages: Vec<String> = js_sys::Array::from(&get_field(&result, "errors"))
            .iter()
            .map(|e| get_field(&e, "message").as_string().unwrap_or_default())
            .collect();
        assert!(
            messages.iter().any(|m| m.contains("booking_method")),
            "{surface}: {messages:?}"
        );
    }
}
