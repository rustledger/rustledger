//! Every WASM query surface lists the ledger's option diagnostics as the
//! FFI's query surfaces and the canonical `Ledger::query_option_errors` list
//! them (#2911, #2929).
//!
//! The WASM side of the drift guard whose cases are
//! `rustledger-loader/tests/query_option_errors/cases.rs`. The drift it pins
//! (review of #2946): a rejected `booking_method` refuses the query, and its
//! E7002 is listed as the refusal that says why, once. The free `query`,
//! `ParsedLedger.query` and `Ledger.query` listed the plain E7002 instead,
//! and `queryMultiFile` listed the refusal and no other option diagnostic.
//!
//! Node-targeting (no `run_in_browser`), so CI's `wasm-pack test --node` step
//! runs it.

#![cfg(target_arch = "wasm32")]

include!("../../rustledger-loader/tests/query_option_errors/cases.rs");

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

/// Code, message, file, line.
type Row = (String, String, Option<String>, Option<u32>);

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// `result` (a WASM `QueryResult`) lists exactly `want`, in order, and
/// answers or refuses as `case` says.
fn check(case: &QueryOptionCase, surface: &str, result: &JsValue, want: &[Row]) {
    let got: Vec<Row> = js_sys::Array::from(&get_field(result, "errors"))
        .iter()
        .map(|e| {
            (
                get_field(&e, "code").as_string().unwrap_or_default(),
                get_field(&e, "message").as_string().unwrap_or_default(),
                get_field(&e, "file").as_string(),
                get_field(&e, "line").as_f64().map(|line| line as u32),
            )
        })
        .collect();
    assert_eq!(got, want, "{} via {surface}", case.name);
    let rows = js_sys::Array::from(&get_field(result, "rows")).length();
    assert_eq!(rows > 0, case.answers, "{} via {surface}", case.name);
}

fn files(case: &QueryOptionCase) -> JsValue {
    let files = js_sys::Object::new();
    for (path, text) in case.files {
        js_sys::Reflect::set(&files, &JsValue::from_str(path), &JsValue::from_str(text))
            .expect("set");
    }
    files.into()
}

#[wasm_bindgen_test]
fn wasm_query_surfaces_list_the_shared_option_errors() {
    for case in QUERY_OPTION_CASES {
        if case.is_single_file() {
            // The source-text surfaces name no file; the loader names the
            // text `<string>`, which the refusal's message quotes.
            let text = case.entry_text();
            let want = case.expected(None, "<string>");
            let result = rustledger_wasm::query(text, QUERY).expect("query");
            check(case, "query", &result, &want);
            let parsed = rustledger_wasm::ParsedLedger::new(text);
            check(
                case,
                "ParsedLedger.query",
                &parsed.query(QUERY).expect("query"),
                &want,
            );
            let restored = rustledger_wasm::ParsedLedger::from_cache(
                &parsed.serialize().expect("serialize"),
                text,
            )
            .expect("fromCache");
            check(
                case,
                "ParsedLedger.query from cache",
                &restored.query(QUERY).expect("query"),
                &want,
            );
        }

        let want = case.expected(Some(MAIN), MAIN);
        let result =
            rustledger_wasm::query_multi_file(files(case), MAIN, QUERY).expect("queryMultiFile");
        check(case, "queryMultiFile", &result, &want);
        let ledger = rustledger_wasm::Ledger::from_files(files(case), MAIN).expect("fromFiles");
        check(
            case,
            "Ledger.query",
            &ledger.query(QUERY).expect("query"),
            &want,
        );
        let restored = rustledger_wasm::Ledger::from_cache(&ledger.serialize().expect("serialize"))
            .expect("fromCache");
        check(
            case,
            "Ledger.query from cache",
            &restored.query(QUERY).expect("query"),
            &want,
        );
    }
}
