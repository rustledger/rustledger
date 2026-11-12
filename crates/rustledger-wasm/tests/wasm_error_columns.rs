//! Every WASM diagnostic surface reports a column in characters, as `rledger
//! check` and the FFI component report it (#2946).
//!
//! `validateSource`, `ParsedLedger.getErrors`, `parse` and `format` counted
//! the column in bytes, so a BOM (three bytes, one character) or a multi-byte
//! character before an error read it high, where `validateMultiFile` (and
//! `rledger check`) did not. Each surface now locates through the loader's
//! canonical (`SourceMap::locate`, `LineIndex`).
//!
//! Runs under `wasm-pack test --node`.

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// `(code, line, column)` of each error in `errors`, sorted.
fn locations(errors: &JsValue) -> Vec<(String, u32, u32)> {
    let mut got: Vec<(String, u32, u32)> = js_sys::Array::from(errors)
        .iter()
        .map(|e| {
            (
                get_field(&e, "code").as_string().unwrap_or_default(),
                get_field(&e, "line").as_f64().unwrap_or_default() as u32,
                get_field(&e, "column").as_f64().unwrap_or_default() as u32,
            )
        })
        .collect();
    got.sort();
    got
}

fn files(source: &str) -> JsValue {
    let files = js_sys::Object::new();
    js_sys::Reflect::set(
        &files,
        &JsValue::from_str("ledger.beancount"),
        &JsValue::from_str(source),
    )
    .expect("set");
    files.into()
}

/// The surfaces that report a source's whole load: `validateSource`,
/// `validateMultiFile`, and `ParsedLedger.getErrors`, fresh and from cache.
fn assert_load_surfaces(source: &str, want: &[(&str, u32, u32)]) {
    let want: Vec<(String, u32, u32)> = want
        .iter()
        .map(|(code, line, column)| ((*code).to_string(), *line, *column))
        .collect();

    let result = rustledger_wasm::validate_source(source).expect("validateSource");
    assert_eq!(
        locations(&get_field(&result, "errors")),
        want,
        "validateSource"
    );

    let result = rustledger_wasm::validate_multi_file(files(source), "ledger.beancount")
        .expect("validateMultiFile");
    assert_eq!(
        locations(&get_field(&result, "errors")),
        want,
        "validateMultiFile"
    );

    let parsed = rustledger_wasm::ParsedLedger::new(source);
    assert_eq!(
        locations(&parsed.get_errors().expect("getErrors")),
        want,
        "ParsedLedger"
    );
    let restored =
        rustledger_wasm::ParsedLedger::from_cache(&parsed.serialize().expect("serialize"), source)
            .expect("fromCache");
    assert_eq!(
        locations(&restored.get_errors().expect("getErrors")),
        want,
        "ParsedLedger from cache"
    );
}

/// A validation finding on line 1 after a BOM is at column 2, as `rledger
/// check --format json` reports it, not 4.
#[wasm_bindgen_test]
fn test_validation_error_column_after_bom_counts_characters() {
    let source = "\u{FEFF}2024-01-02 balance Assets:X 1 USD\n2024-01-01 open Assets:Y\n";
    assert_load_surfaces(source, &[("E1001", 1, 2), ("E2001", 1, 2)]);
}

/// A parse error after a multi-byte character (`Ü`, two bytes) is at its
/// character column, on every surface that reports parse errors, and after a
/// BOM too.
#[wasm_bindgen_test]
fn test_parse_error_column_after_multibyte_counts_characters() {
    for (source, column) in [
        ("2024-01-03 open Assets:Ü 10\n", 26),
        ("\u{FEFF}2024-01-03 open Assets:Ü 10\n", 27),
    ] {
        let want = [("P0012", 1, column)];
        assert_load_surfaces(source, &want);
        let want: Vec<(String, u32, u32)> = vec![("P0012".to_string(), 1, column)];

        let result = rustledger_wasm::parse(source).expect("parse");
        assert_eq!(
            locations(&get_field(&result, "errors")),
            want,
            "parse {source:?}"
        );

        let result = rustledger_wasm::format(source).expect("format");
        assert_eq!(
            locations(&get_field(&result, "errors")),
            want,
            "format {source:?}"
        );
    }
}
