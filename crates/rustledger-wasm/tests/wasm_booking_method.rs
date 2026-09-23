//! JS-runtime tests for #2386: every wasm query entry point realizes
//! `BALANCES` with the ledger's `option "booking_method"`.
//!
//! Node-targeting (no `run_in_browser`), like `wasm_meta.rs`, so CI's
//! `wasm-pack test --node` step runs them.
//!
//! The ledger books under a global NONE: the sale at `{90 USD}` names a cost
//! no lot has, so NONE opens a `-2 X {90 USD}` lot next to `5 X {100 USD}`,
//! which is what beancount 3.2.3 holds. `BALANCES` realizes the booked ledger
//! through a booking engine; with that engine's default hardcoded, the sale
//! replayed as a reduction and every entry point answered "No matching lot".

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

const GLOBAL_NONE: &str = r#"option "booking_method" "NONE"
2020-01-01 open Assets:Stock
2020-01-01 open Assets:Cash
2020-01-02 * "buy"
  Assets:Stock  5 X {100 USD}
  Assets:Cash  -500 USD
2020-01-03 * "sell at a cost no lot has"
  Assets:Stock  -2 X {90 USD}
  Assets:Cash   180 USD
"#;

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

fn stringify(value: &JsValue) -> String {
    js_sys::JSON::stringify(value)
        .ok()
        .and_then(|s| s.as_string())
        .unwrap_or_default()
}

/// Assert a `BALANCES` result has no errors and holds both lots of `X`.
///
/// The wire's inventory cell carries units only (`PositionValue` has no
/// cost), so the two lots show as `5 X` and `-2 X` side by side. That is still
/// the booked shape: a STRICT replay errored instead, and a replay that
/// reduced would have left one netted `3 X`.
fn assert_both_lots(result: &JsValue, surface: &str) {
    let errors = get_field(result, "errors");
    assert_eq!(
        js_sys::Array::from(&errors).length(),
        0,
        "{surface}: BALANCES must not error: {}",
        stringify(&errors)
    );
    let rows = stringify(&get_field(result, "rows"));
    let stock = r#"["Assets:Stock",{"positions":[{"units":{"number":"5","currency":"X"}},{"units":{"number":"-2","currency":"X"}}]}]"#;
    assert!(
        rows.contains(stock),
        "{surface}: BALANCES must hold the 5 X and -2 X lots apart: {rows}"
    );
}

fn files() -> JsValue {
    let files = js_sys::Object::new();
    js_sys::Reflect::set(
        &files,
        &JsValue::from_str("main.beancount"),
        &JsValue::from_str(GLOBAL_NONE),
    )
    .expect("set file");
    files.into()
}

#[wasm_bindgen_test]
fn query_realizes_with_the_global_booking_method_2386() {
    let result = rustledger_wasm::query(GLOBAL_NONE, "BALANCES").expect("query");
    assert_both_lots(&result, "query");
}

#[wasm_bindgen_test]
fn parsed_ledger_realizes_with_the_global_booking_method_2386() {
    let ledger = rustledger_wasm::ParsedLedger::new(GLOBAL_NONE);
    assert_both_lots(&ledger.query("BALANCES").expect("query"), "ParsedLedger");
}

#[wasm_bindgen_test]
fn query_multi_file_realizes_with_the_global_booking_method_2386() {
    let result = rustledger_wasm::query_multi_file(files(), "main.beancount", "BALANCES")
        .expect("queryMultiFile");
    assert_both_lots(&result, "queryMultiFile");
}

/// The multi-file class, and its cache round-trip: the method cannot be
/// recovered from the restored directives, so it has to be archived.
#[wasm_bindgen_test]
fn ledger_realizes_with_the_global_booking_method_2386() {
    let ledger = rustledger_wasm::Ledger::from_files(files(), "main.beancount").expect("fromFiles");
    assert_both_lots(&ledger.query("BALANCES").expect("query"), "Ledger");

    let restored = rustledger_wasm::Ledger::from_cache(&ledger.serialize().expect("serialize"))
        .expect("fromCache");
    assert_both_lots(
        &restored.query("BALANCES").expect("query"),
        "Ledger.fromCache",
    );
}
