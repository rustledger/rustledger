//! JS-runtime tests for issue #1168 metadata exposure.
//!
//! These run under `wasm-pack test --node`. The sibling `wasm.rs`
//! file is configured `run_in_browser` only, which means its tests
//! skip on CI (the browser test job is disabled per Issue #261).
//! This file is node-targeting so the metadata wire shape — the
//! whole feature value of #1168 — actually gets exercised in CI.
//!
//! Test goals:
//!  - Verify `serde-wasm-bindgen` lowers `MetaValueJson` to native
//!    JS types (string/boolean/object/null/undefined), not wrapped
//!    `Map<>` or string-encoded JSON.
//!  - Pin the per-variant wire shape (String / Bool / Amount / Null).
//!  - Pin the `skip_serializing_if` behavior — directives without
//!    explicit metadata MUST NOT carry a `meta` field.
//!  - Pin `Custom.values` exposure (dropped entirely pre-#1168).

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

// NB: no `wasm_bindgen_test_configure!(run_in_browser)` — these
// tests are node-compatible by design. Without that macro,
// wasm-bindgen-test runs them in node by default, which is what
// CI's `wasm-pack test --node` step exercises.

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

fn get_array_length(obj: &JsValue) -> u32 {
    js_sys::Array::from(obj).length()
}

#[wasm_bindgen_test]
fn directive_meta_exposed_to_js_1168() {
    // Fixture covers every wire shape `MetaValueJson` emits:
    //   - String (description, source)
    //   - Number → String on the wire (precision, preserves digits)
    //   - Bool (TRUE)
    //   - posting-level meta nested inside `postings[0].meta`
    let source = r#"
2024-01-01 open Assets:Bank USD
  description: "Main account"
2024-01-01 commodity USD
  precision: 2

2024-01-15 * "Coffee Shop" "Morning coffee"
  trip: "vacation-2024"
  reconciled: TRUE
  Expenses:Food  5.00 USD
    note: "espresso"
  Assets:Bank   -5.00 USD
"#;

    let result = rustledger_wasm::parse(source).expect("parse should not throw");
    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "fixture must parse cleanly",);

    let ledger = get_field(&result, "ledger");
    let directives = get_field(&ledger, "directives");
    let directives_arr = js_sys::Array::from(&directives);

    // Open directive: `description: "Main account"` lands on
    // `meta.description` as a JS string (not as wrapped JSON or
    // a Map<> entry).
    let open = directives_arr.get(0);
    assert_eq!(get_field(&open, "type"), JsValue::from_str("open"));
    let open_meta = get_field(&open, "meta");
    assert!(!open_meta.is_undefined(), "open.meta must be present");
    let description = get_field(&open_meta, "description");
    assert_eq!(
        description.as_string().as_deref(),
        Some("Main account"),
        "description must be a JS string",
    );

    // Commodity directive: `precision: 2` is a Number host-side;
    // the FFI-WASI-compatible wire format stringifies numbers to
    // preserve precision. Expect a string `"2"` on the JS side.
    let commodity = directives_arr.get(1);
    let commodity_meta = get_field(&commodity, "meta");
    let precision = get_field(&commodity_meta, "precision");
    assert_eq!(
        precision.as_string().as_deref(),
        Some("2"),
        "Number metadata must serialize as a string",
    );

    // Transaction-level meta: string + boolean.
    let txn = directives_arr.get(2);
    let txn_meta = get_field(&txn, "meta");
    assert_eq!(
        get_field(&txn_meta, "trip").as_string().as_deref(),
        Some("vacation-2024"),
    );
    let reconciled = get_field(&txn_meta, "reconciled");
    assert_eq!(
        reconciled,
        JsValue::TRUE,
        "Bool metadata must be a JS boolean, not the string \"TRUE\"",
    );

    // Posting-level metadata reaches `postings[0].meta.note`.
    let postings = get_field(&txn, "postings");
    let postings_arr = js_sys::Array::from(&postings);
    let coffee = postings_arr.get(0);
    let coffee_meta = get_field(&coffee, "meta");
    assert!(
        !coffee_meta.is_undefined(),
        "posting.meta must be present when posting has metadata",
    );
    assert_eq!(
        get_field(&coffee_meta, "note").as_string().as_deref(),
        Some("espresso"),
    );
}

#[wasm_bindgen_test]
fn directive_meta_absent_when_empty_1168() {
    // Pin the wire-side `skip_serializing_if` — directives without
    // explicit metadata MUST NOT carry a `meta` field. JS consumers
    // that check `'meta' in directive` see false; consumers that
    // read `directive.meta` see `undefined`. This preserves the
    // pre-#1168 shape for directives without explicit metadata.
    let source = "2024-01-01 open Assets:Bank USD\n";
    let result = rustledger_wasm::parse(source).expect("parse should not throw");
    let ledger = get_field(&result, "ledger");
    let directives = get_field(&ledger, "directives");
    let open = js_sys::Array::from(&directives).get(0);

    let meta = get_field(&open, "meta");
    assert!(
        meta.is_undefined(),
        "open.meta must be absent (skip_serializing_if = empty)",
    );
}

#[wasm_bindgen_test]
fn custom_directive_values_exposed_1168() {
    // Pre-#1168 the `Custom` directive's positional values were
    // dropped entirely from JSON output. Pin the new wire shape:
    // a JS array, preserving order and per-arg type.
    let source = r#"2024-01-01 custom "budget" "monthly" TRUE
"#;
    let result = rustledger_wasm::parse(source).expect("parse should not throw");
    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0);

    let ledger = get_field(&result, "ledger");
    let directives = get_field(&ledger, "directives");
    let custom = js_sys::Array::from(&directives).get(0);
    assert_eq!(get_field(&custom, "type"), JsValue::from_str("custom"));

    let values = get_field(&custom, "values");
    let values_arr = js_sys::Array::from(&values);
    assert_eq!(
        values_arr.length(),
        2,
        "Custom values array must carry both positional args",
    );
    assert_eq!(values_arr.get(0).as_string().as_deref(), Some("monthly"));
    assert_eq!(
        values_arr.get(1),
        JsValue::TRUE,
        "TRUE arg must be a JS boolean",
    );
}
