//! Every WASM diagnostic surface reports exactly the findings `rledger
//! check` reports, on the same ledgers (#2937).
//!
//! The WASM side of the drift guard whose cases are
//! `rustledger-loader/tests/surface_agreement/cases.rs`. Two drifts it pins:
//! the single-source surfaces reported E1004 (closing an account with a
//! balance), which `check` and bean-check do not, and skipped validation
//! after a booking error, which `check` and bean-check do not.

#![cfg(target_arch = "wasm32")]

include!("../../rustledger-loader/tests/surface_agreement/cases.rs");

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// `errors` (a JS array of WASM `Error`s) is exactly `case`'s findings: code,
/// line and message start, in any order.
fn check(case: &SurfaceCase, surface: &str, errors: &JsValue) {
    let mut got: Vec<(String, u32, String)> = js_sys::Array::from(errors)
        .iter()
        .map(|e| {
            (
                get_field(&e, "code").as_string().unwrap_or_default(),
                get_field(&e, "line").as_f64().unwrap_or_default() as u32,
                get_field(&e, "message").as_string().unwrap_or_default(),
            )
        })
        .collect();
    got.sort();
    let mut want: Vec<&Finding> = case.findings.iter().collect();
    want.sort_by_key(|f| (f.code, f.line));
    let context = format!("{} via {surface}: {got:?}", case.name);
    assert_eq!(got.len(), want.len(), "{context}");
    for ((code, line, message), finding) in got.iter().zip(&want) {
        assert_eq!(code, finding.code, "{context}");
        assert_eq!(*line, finding.line, "{context}");
        assert!(message.starts_with(finding.message), "{context}");
    }
}

fn files(case: &SurfaceCase) -> JsValue {
    let files = js_sys::Object::new();
    js_sys::Reflect::set(
        &files,
        &JsValue::from_str("ledger.beancount"),
        &JsValue::from_str(case.source),
    )
    .expect("set");
    files.into()
}

#[wasm_bindgen_test]
fn wasm_surfaces_report_the_shared_findings() {
    for case in SURFACE_CASES {
        let result = rustledger_wasm::validate_source(case.source).expect("validateSource");
        check(case, "validateSource", &get_field(&result, "errors"));
        assert_eq!(
            get_field(&result, "valid").as_bool(),
            Some(case.findings.is_empty()),
            "{} via validateSource",
            case.name
        );

        let result = rustledger_wasm::validate_multi_file(files(case), "ledger.beancount")
            .expect("validateMultiFile");
        check(case, "validateMultiFile", &get_field(&result, "errors"));

        let parsed = rustledger_wasm::ParsedLedger::new(case.source);
        check(
            case,
            "ParsedLedger",
            &parsed.get_errors().expect("getErrors"),
        );
        let restored = rustledger_wasm::ParsedLedger::from_cache(
            &parsed.serialize().expect("serialize"),
            case.source,
        )
        .expect("fromCache");
        check(
            case,
            "ParsedLedger from cache",
            &restored.get_errors().expect("getErrors"),
        );

        let ledger = rustledger_wasm::Ledger::from_files(files(case), "ledger.beancount")
            .expect("fromFiles");
        check(case, "Ledger", &ledger.get_errors().expect("getErrors"));
        let restored = rustledger_wasm::Ledger::from_cache(&ledger.serialize().expect("ser"))
            .expect("fromCache");
        check(
            case,
            "Ledger from cache",
            &restored.get_errors().expect("getErrors"),
        );
    }
}
