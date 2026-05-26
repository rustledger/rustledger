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

/// Find the first directive whose `type` field equals `target`.
///
/// Index-based access (`directives[0]`) is fragile to parser
/// ordering changes; type-filtering is robust. Tests that need a
/// specific directive type from a multi-directive fixture should
/// use this helper.
fn find_directive_by_type(directives: &JsValue, target: &str) -> JsValue {
    let arr = js_sys::Array::from(directives);
    for i in 0..arr.length() {
        let d = arr.get(i);
        if get_field(&d, "type").as_string().as_deref() == Some(target) {
            return d;
        }
    }
    panic!("no directive of type `{target}` found in fixture");
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

    // Open directive: `description: "Main account"` lands on
    // `meta.description` as a JS string (not as wrapped JSON or
    // a Map<> entry). Type-filter rather than index-filter so a
    // future parser reordering doesn't break the test.
    let open = find_directive_by_type(&directives, "open");
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
    let commodity = find_directive_by_type(&directives, "commodity");
    let commodity_meta = get_field(&commodity, "meta");
    let precision = get_field(&commodity_meta, "precision");
    assert_eq!(
        precision.as_string().as_deref(),
        Some("2"),
        "Number metadata must serialize as a string",
    );

    // Transaction-level meta: string + boolean.
    let txn = find_directive_by_type(&directives, "transaction");
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
fn amount_metadata_exposes_as_object_in_js_1168() {
    // The `MetaValueJson::Amount` variant must reach JS as a plain
    // object `{number, currency}` — not as a string, not as a
    // wrapped wasm-bindgen reference. This pins serde-wasm-bindgen's
    // lowering of the struct-style untagged variant.
    let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Stock buy"
  cost-basis: 1500.00 USD
  Assets:Bank   100.00 USD
  Assets:Bank  -100.00 USD
"#;

    let result = rustledger_wasm::parse(source).expect("parse should not throw");
    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0, "fixture must parse cleanly",);

    let ledger = get_field(&result, "ledger");
    let directives = get_field(&ledger, "directives");
    let txn = find_directive_by_type(&directives, "transaction");

    let txn_meta = get_field(&txn, "meta");
    let cost_basis = get_field(&txn_meta, "cost-basis");
    // Must be an object — not a string, not undefined.
    assert!(
        cost_basis.is_object(),
        "Amount metadata must be a JS object {{number, currency}}, got {cost_basis:?}",
    );
    assert!(
        cost_basis.as_string().is_none(),
        "Amount metadata must NOT be a string (would defeat the whole point of the variant)",
    );
    let number = get_field(&cost_basis, "number");
    let currency = get_field(&cost_basis, "currency");
    assert_eq!(number.as_string().as_deref(), Some("1500.00"));
    assert_eq!(currency.as_string().as_deref(), Some("USD"));
}

#[wasm_bindgen_test]
fn null_metadata_exposes_as_js_null_1168() {
    // `MetaValue::None` reaches the host when a metadata key is
    // parsed but no value follows (`key:\n`). Per parser.rs:1043,
    // that's the production rule. The wire side must lower this to
    // JS `null` — not `undefined`, not the string `"null"`. JS
    // consumers distinguish:
    //   - `meta['key'] === null` → key was explicitly value-less
    //   - `meta['key'] === undefined` → key was never set
    let source = "\
2024-01-01 open Assets:Bank USD
  unused-flag:
";

    let result = rustledger_wasm::parse(source).expect("parse should not throw");
    let errors = get_field(&result, "errors");
    assert_eq!(
        get_array_length(&errors),
        0,
        "fixture must parse cleanly (key-without-value produces MetaValue::None)",
    );

    let ledger = get_field(&result, "ledger");
    let directives = get_field(&ledger, "directives");
    let open = js_sys::Array::from(&directives).get(0);
    let meta = get_field(&open, "meta");

    let value = get_field(&meta, "unused-flag");
    assert!(
        value.is_null(),
        "MetaValue::None must reach JS as null, got {value:?}",
    );
    // Explicit guards against the most likely degenerate mappings.
    assert!(
        !value.is_undefined(),
        "null metadata must be present (null), not absent (undefined)",
    );
    assert_ne!(value.as_string().as_deref(), Some("null"));
    assert_ne!(value.as_string().as_deref(), Some(""));
}

#[wasm_bindgen_test]
fn account_metadata_flattens_to_string_in_js_1168() {
    // Documented behavior: `MetaValue::Account` flattens to a JS
    // string on the wire (lossy by design, mirrors FFI-WASI). Pin
    // it so a future tightening that adds an Account variant to
    // MetaValueJson doesn't silently change JS consumer behavior.
    let source = r#"
2024-01-01 open Assets:Bank USD
  source-account: Assets:Other
"#;

    let result = rustledger_wasm::parse(source).expect("parse should not throw");
    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0);

    let ledger = get_field(&result, "ledger");
    let directives = get_field(&ledger, "directives");
    let open = js_sys::Array::from(&directives).get(0);
    let meta = get_field(&open, "meta");

    let source_account = get_field(&meta, "source-account");
    assert_eq!(
        source_account.as_string().as_deref(),
        Some("Assets:Other"),
        "Account metadata must reach JS as a plain string",
    );
}

#[wasm_bindgen_test]
fn open_booking_is_clean_string_in_js() {
    // Pre-fix the booking field was Debug-formatted, producing
    // `"\"STRICT\""` on the JS side. Pin the clean form.
    let source = "2024-01-01 open Assets:Bank USD \"STRICT\"\n";

    let result = rustledger_wasm::parse(source).expect("parse should not throw");
    let errors = get_field(&result, "errors");
    assert_eq!(get_array_length(&errors), 0);

    let ledger = get_field(&result, "ledger");
    let directives = get_field(&ledger, "directives");
    let open = js_sys::Array::from(&directives).get(0);

    let booking = get_field(&open, "booking");
    assert_eq!(
        booking.as_string().as_deref(),
        Some("STRICT"),
        "booking must be the literal source token, not Debug-formatted (no leading `\\\"`)",
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
