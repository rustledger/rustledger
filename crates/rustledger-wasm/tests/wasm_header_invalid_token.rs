//! An invalid token in a transaction header moves no string to a different
//! field on the WASM wire (#2932).
//!
//! `parse` keeps a transaction whose header holds an invalid token, and
//! reports the token. Its payee and narration must be the ones written: in
//! `* "Cafe" <bad>` the payee is `Cafe` and the narration is empty (elided on
//! the wire), where `Cafe` was the narration with no payee.
//!
//! Runs under `wasm-pack test --node`.

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// The transaction of `header`, and the number of errors `parse` reports.
fn parse_header(header: &str) -> (JsValue, u32) {
    let source = format!(
        "2024-01-01 open Assets:Bank\n2024-01-01 open Expenses:Food\n\
         2024-01-15 {header}\n  Expenses:Food  5.00 USD\n  Assets:Bank\n"
    );
    let result = rustledger_wasm::parse(&source).expect("parse should not throw");
    let errors = js_sys::Array::from(&get_field(&result, "errors")).length();
    let directives = js_sys::Array::from(&get_field(&get_field(&result, "ledger"), "directives"));
    let txn = (0..directives.length())
        .map(|i| directives.get(i))
        .find(|d| get_field(d, "type").as_string().as_deref() == Some("transaction"))
        .expect("the transaction is kept");
    (txn, errors)
}

#[wasm_bindgen_test]
fn test_parse_invalid_token_after_payee_keeps_the_payee() {
    for header in ["* \"Cafe\" \u{11}\"x\"", "txn \"Cafe\" \u{11} #t"] {
        let (txn, errors) = parse_header(header);
        assert_eq!(errors, 1, "{header:?}: the invalid token is reported");
        assert_eq!(
            get_field(&txn, "payee").as_string().as_deref(),
            Some("Cafe"),
            "{header:?}"
        );
        assert!(
            get_field(&txn, "narration").is_undefined(),
            "{header:?}: an empty narration is elided"
        );
    }
}

#[wasm_bindgen_test]
fn test_parse_invalid_token_before_the_strings_moves_neither() {
    let (txn, errors) = parse_header("* \u{11} \"Cafe\" \"Lunch\" #t ^l");
    assert_eq!(errors, 1);
    assert_eq!(
        get_field(&txn, "payee").as_string().as_deref(),
        Some("Cafe")
    );
    assert_eq!(
        get_field(&txn, "narration").as_string().as_deref(),
        Some("Lunch")
    );
    let tags = js_sys::Array::from(&get_field(&txn, "tags"));
    let links = js_sys::Array::from(&get_field(&txn, "links"));
    assert_eq!(tags.get(0).as_string().as_deref(), Some("t"));
    assert_eq!(links.get(0).as_string().as_deref(), Some("l"));
}

/// A token after the string does not move it: with an unexpected token
/// before it too, the string stays the narration.
#[wasm_bindgen_test]
fn test_parse_unexpected_token_before_and_after_keeps_the_narration() {
    let (txn, errors) = parse_header("* \u{11} \"Lunch\" \u{11}");
    assert_eq!(errors, 2, "each invalid token is reported");
    assert!(get_field(&txn, "payee").is_undefined());
    assert_eq!(
        get_field(&txn, "narration").as_string().as_deref(),
        Some("Lunch")
    );
}

/// A token that cannot have swallowed a string leaves the count rule
/// standing: a forgotten newline (`* "Cafe" 5.00 USD`) keeps the narration,
/// and so does a number before the string, even with an invalid token after.
#[wasm_bindgen_test]
fn test_parse_other_token_keeps_the_narration() {
    for (header, errors) in [
        ("* \"Cafe\" 5.00 USD", 1),
        ("* \"Cafe\" USD", 1),
        ("* \"Cafe\" ~", 1),
        ("* 123 \"Cafe\" \u{11}", 2),
        ("* 2024-01-03 \"Cafe\" \u{11}", 2),
    ] {
        let (txn, got) = parse_header(header);
        assert_eq!(got, errors, "{header:?}");
        assert!(get_field(&txn, "payee").is_undefined(), "{header:?}");
        assert_eq!(
            get_field(&txn, "narration").as_string().as_deref(),
            Some("Cafe"),
            "{header:?}"
        );
    }
}
