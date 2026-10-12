//! JS-runtime tests for #2579: a table one query's `CREATE TABLE` makes is
//! there for the same ledger's next query.
//!
//! `ParsedLedger.query` and `Ledger.query` each built a fresh executor, so a
//! created table was gone by the next call. Node-targeting (no
//! `run_in_browser`), like `wasm_meta.rs`, so CI's `wasm-pack test --node`
//! step runs them.

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

const LEDGER: &str = r#"2024-01-01 open Assets:Cash
2024-01-01 open Expenses:Food
2024-01-02 * "lunch"
  Expenses:Food  10 USD
  Assets:Cash
"#;

const CREATE: &str = "CREATE TABLE spent AS SELECT account, number WHERE number > 0";

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

fn length(value: &JsValue) -> u32 {
    js_sys::Array::from(value).length()
}

/// The number of rows `result` holds, after asserting it has no errors.
fn rows(result: &JsValue, query: &str) -> u32 {
    let errors = get_field(result, "errors");
    assert_eq!(length(&errors), 0, "{query}: {errors:?}");
    length(&get_field(result, "rows"))
}

fn failed(result: &JsValue) -> bool {
    length(&get_field(result, "errors")) > 0
}

/// Every check, against one ledger's `query`.
fn check(query: impl Fn(&str) -> JsValue, surface: &str) {
    rows(&query(CREATE), surface);
    assert_eq!(rows(&query("SELECT * FROM spent"), surface), 1, "{surface}");
    rows(
        &query("INSERT INTO spent VALUES ('Expenses:Rent', 5)"),
        surface,
    );
    assert_eq!(rows(&query("SELECT * FROM spent"), surface), 2, "{surface}");
    // A failed query leaves the tables as they were.
    assert!(failed(&query(CREATE)), "{surface}: already exists");
    assert_eq!(rows(&query("SELECT * FROM spent"), surface), 2, "{surface}");
}

#[wasm_bindgen_test]
fn parsed_ledger_keeps_created_tables() {
    let ledger = rustledger_wasm::ParsedLedger::new(LEDGER);
    check(|q| ledger.query(q).expect("query"), "ParsedLedger");
    // Another ledger has its own.
    let other = rustledger_wasm::ParsedLedger::new(LEDGER);
    assert!(failed(&other.query("SELECT * FROM spent").expect("query")));
}

#[wasm_bindgen_test]
fn ledger_keeps_created_tables() {
    let files = js_sys::Object::new();
    js_sys::Reflect::set(
        &files,
        &JsValue::from_str("main.beancount"),
        &JsValue::from_str(LEDGER),
    )
    .expect("set file");
    let ledger =
        rustledger_wasm::Ledger::from_files(files.into(), "main.beancount").expect("fromFiles");
    check(|q| ledger.query(q).expect("query"), "Ledger");
}

#[wasm_bindgen_test]
fn the_free_query_function_keeps_none() {
    rows(
        &rustledger_wasm::query(LEDGER, CREATE).expect("query"),
        CREATE,
    );
    assert!(failed(
        &rustledger_wasm::query(LEDGER, "SELECT * FROM spent").expect("query")
    ));
}
