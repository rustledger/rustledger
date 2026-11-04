//! Every WASM query entry point resolves the source-location columns and
//! `#balances.discrepancy` (#2823, #2825).
//!
//! These read NULL on every WASM path: each built a bare executor with no
//! source map and no discrepancies, where the CLI set both up. All paths now
//! go through `Executor::for_ledger`. Expected values are bean-query's
//! (beanquery 0.2.0): `location` is `path:line:`, and an in-memory source is
//! named `<string>`, as beancount's `load_string` names it.

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

const LEDGER: &str = "2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
2024-01-05 balance Assets:Bank 999.00 USD
";

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// Row 0 of `result`, after checking the query raised no error.
fn first_row(result: &JsValue, query: &str) -> js_sys::Array {
    let rows = js_sys::Array::from(&get_field(result, "rows"));
    assert!(rows.length() > 0, "{query}: no rows");
    js_sys::Array::from(&rows.get(0))
}

fn string_cell(row: &js_sys::Array, i: u32) -> String {
    row.get(i)
        .as_string()
        .unwrap_or_else(|| panic!("cell {i} is not a string: {:?}", row.get(i)))
}

fn number_cell(row: &js_sys::Array, i: u32) -> f64 {
    row.get(i)
        .as_f64()
        .unwrap_or_else(|| panic!("cell {i} is not a number: {:?}", row.get(i)))
}

/// Check one surface: `query` runs a query on [`LEDGER`] loaded as `name`.
fn check(query: impl Fn(&str) -> JsValue, name: &str) {
    let q = "SELECT filename, lineno, location FROM postings LIMIT 1";
    let row = first_row(&query(q), q);
    assert_eq!(string_cell(&row, 0), name, "{name}: filename");
    assert_eq!(number_cell(&row, 1), 4.0, "{name}: lineno");
    assert_eq!(
        string_cell(&row, 2),
        format!("{name}:4:"),
        "{name}: location"
    );

    let q = "SELECT meta('lineno'), entry_meta('filename') LIMIT 1";
    let row = first_row(&query(q), q);
    assert_eq!(number_cell(&row, 0), 4.0, "{name}: meta('lineno')");
    assert_eq!(string_cell(&row, 1), name, "{name}: entry_meta('filename')");

    // bean-query: `Assets:Bank, -989.00 USD` (10 held, 999.00 asserted).
    let q = "SELECT account, discrepancy FROM #balances";
    let row = first_row(&query(q), q);
    let amount = row.get(1);
    assert_eq!(
        get_field(&amount, "number").as_string().as_deref(),
        Some("-989.00"),
        "{name}: discrepancy {amount:?}"
    );
    assert_eq!(
        get_field(&amount, "currency").as_string().as_deref(),
        Some("USD"),
        "{name}: discrepancy currency"
    );
}

#[wasm_bindgen_test]
fn query_resolves_sources_and_discrepancy() {
    check(
        |q| rustledger_wasm::query(LEDGER, q).expect("query"),
        "<string>",
    );
}

#[wasm_bindgen_test]
fn parsed_ledger_resolves_sources_and_discrepancy() {
    let ledger = rustledger_wasm::ParsedLedger::new(LEDGER);
    check(|q| ledger.query(q).expect("query"), "<string>");
}

#[wasm_bindgen_test]
fn parsed_ledger_from_cache_resolves_sources_and_discrepancy() {
    let bytes = rustledger_wasm::ParsedLedger::new(LEDGER)
        .serialize()
        .expect("serialize");
    let ledger = rustledger_wasm::ParsedLedger::from_cache(&bytes, LEDGER).expect("from cache");
    check(|q| ledger.query(q).expect("query"), "<string>");
}

fn files() -> JsValue {
    let files = js_sys::Object::new();
    js_sys::Reflect::set(
        &files,
        &JsValue::from_str("main.beancount"),
        &JsValue::from_str(LEDGER),
    )
    .expect("set");
    files.into()
}

#[wasm_bindgen_test]
fn query_multi_file_resolves_sources_and_discrepancy() {
    check(
        |q| rustledger_wasm::query_multi_file(files(), "main.beancount", q).expect("query"),
        "main.beancount",
    );
}

#[wasm_bindgen_test]
fn ledger_from_files_resolves_sources_and_discrepancy() {
    let ledger =
        rustledger_wasm::Ledger::from_files(files(), "main.beancount").expect("from files");
    check(|q| ledger.query(q).expect("query"), "main.beancount");
}
