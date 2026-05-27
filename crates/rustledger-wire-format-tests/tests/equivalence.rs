//! Cross-binding equivalence tests for the `Directive → JSON` wire format.
//!
//! Calls both bindings' actual `directive_to_json` functions
//! ([`rustledger_ffi_wasi::convert::directive_to_json`] and
//! [`rustledger_wasm::convert::directive_to_json`]) on a shared
//! `Directive` fixture and asserts they produce structurally
//! equivalent JSON.
//!
//! ## Why this exists
//!
//! Each binding has its own tests pinning its own wire shape in
//! isolation — nothing asserts the two SHAPES AGREE. Issue #1168 was
//! exactly that failure: WASM dropped directive metadata for the
//! crate's entire lifetime, and the per-binding tests didn't catch
//! it because each test only knew about its own DTO. See issue #1200
//! for the broader audit/scaffold plan.
//!
//! ## Known divergences (normalized away in this test)
//!
//! Each divergence below should be converged in a follow-up PR (it's
//! a JSON-RPC / JS API change; out of scope for landing this harness).
//! The normalization step exists so the test can land in a useful
//! state today and start catching *new* drift while the existing
//! drift gets fixed in dedicated PRs.
//!
//! 1. **`meta` field internal shape**: FFI-WASI's `Meta` is a
//!    flattened struct bundling `filename` / `lineno` / `hash` with
//!    user metadata. WASM's `meta` is `HashMap<String, MetaValueJson>`
//!    — user metadata only. Normalization strips
//!    `filename`/`lineno`/`hash` from the FFI-WASI side. Converge by
//!    moving source-position info to a sibling field on the FFI-WASI
//!    directive.
//!
//! 2. **Empty-collection serialization**: WASM uses
//!    `skip_serializing_if = "HashMap::is_empty"` on its `meta`
//!    field; FFI-WASI emits `"meta": {}`. Normalization drops
//!    `meta: {}` on both sides. Converge by adding
//!    `skip_serializing_if` to the FFI-WASI side (or by always
//!    emitting an explicit empty object on both — pick one rule).
//!
//! 3. **None vs absent**: WASM emits `"payee": null`, FFI-WASI uses
//!    `skip_serializing_if = "Option::is_none"`. Normalization drops
//!    explicit nulls. Converge by adding `skip_serializing_if` on
//!    the WASM side.

use rust_decimal_macros::dec;
use rustledger_core::{
    Account, Amount, Currency, Directive, Link, MetaValue, Metadata, Open, Posting, Spanned, Tag,
    Transaction, naive_date,
};

// =============================================================================
// Normalization
// =============================================================================

/// Strip the FFI-WASI-specific source-position keys from `meta`.
/// See divergence #1 in the module doc.
fn strip_source_position_keys(json: &mut serde_json::Value) {
    const SOURCE_POSITION_KEYS: &[&str] = &["filename", "lineno", "hash"];
    if let Some(obj) = json.as_object_mut()
        && let Some(meta) = obj.get_mut("meta").and_then(|m| m.as_object_mut())
    {
        for key in SOURCE_POSITION_KEYS {
            meta.remove(*key);
        }
    }
}

/// Recursively strip empty objects keyed `"meta"` and explicit nulls.
/// See divergences #2 and #3 in the module doc.
fn strip_empty_meta_and_nulls(json: &mut serde_json::Value) {
    match json {
        serde_json::Value::Object(map) => {
            map.retain(|key, value| {
                if value.is_null() {
                    return false;
                }
                if key == "meta" && value.as_object().is_some_and(serde_json::Map::is_empty) {
                    return false;
                }
                true
            });
            for value in map.values_mut() {
                strip_empty_meta_and_nulls(value);
            }
        }
        serde_json::Value::Array(arr) => {
            for v in arr {
                strip_empty_meta_and_nulls(v);
            }
        }
        _ => {}
    }
}

/// Run a `Directive` through both bindings' `directive_to_json` and
/// assert the JSON outputs agree after normalization.
///
/// `label` is used in the assertion message so a failure points at
/// the offending fixture.
#[track_caller]
fn assert_wire_equivalent(label: &str, directive: &Directive) {
    let ffi_wasi_json = rustledger_ffi_wasi::convert::directive_to_json(directive, 1, "test.bean");
    let mut ffi_wasi_value = serde_json::to_value(&ffi_wasi_json)
        .expect("FFI-WASI DirectiveJson is always JSON-serializable");
    strip_source_position_keys(&mut ffi_wasi_value);
    strip_empty_meta_and_nulls(&mut ffi_wasi_value);

    let wasm_json = rustledger_wasm::convert::directive_to_json(directive);
    let mut wasm_value =
        serde_json::to_value(&wasm_json).expect("WASM DirectiveJson is always JSON-serializable");
    strip_empty_meta_and_nulls(&mut wasm_value);

    assert_eq!(
        ffi_wasi_value, wasm_value,
        "wire-format divergence between FFI-WASI and WASM for fixture {label:?}",
    );
}

// =============================================================================
// Fixture builders
// =============================================================================

fn fixture_posting(account: &str, amount_str: &str, currency: &str) -> Spanned<Posting> {
    Spanned::synthesized(Posting::new(
        Account::new(account),
        Amount::new(amount_str.parse().unwrap(), Currency::new(currency)),
    ))
}

/// Build a `Metadata` with one entry per `MetaValue` variant. This
/// fixture is what exercises the metadata wire-shape — every
/// flavor (`String`, `Account`, `Currency`, `Tag`, `Link`, `Date`,
/// `Number`, `Bool`, `Amount`, `None`) is present so the test
/// catches a binding dropping a single variant.
fn fixture_metadata_all_variants() -> Metadata {
    let mut m = Metadata::default();
    m.insert(
        "string-key".to_string(),
        MetaValue::String("hello".to_string()),
    );
    m.insert(
        "account-key".to_string(),
        MetaValue::Account(Account::new("Assets:Cash")),
    );
    m.insert(
        "currency-key".to_string(),
        MetaValue::Currency(Currency::new("USD")),
    );
    m.insert("tag-key".to_string(), MetaValue::Tag(Tag::new("trip")));
    m.insert("link-key".to_string(), MetaValue::Link(Link::new("inv-42")));
    m.insert(
        "date-key".to_string(),
        MetaValue::Date(naive_date(2024, 6, 15).unwrap()),
    );
    m.insert("number-key".to_string(), MetaValue::Number(dec!(123.456)));
    m.insert("bool-key".to_string(), MetaValue::Bool(true));
    m.insert(
        "amount-key".to_string(),
        MetaValue::Amount(Amount::new(dec!(99.99), Currency::new("EUR"))),
    );
    m.insert("none-key".to_string(), MetaValue::None);
    m
}

// =============================================================================
// Tests
// =============================================================================

/// Metadata equivalence — every `MetaValue` flavor produces the
/// same JSON shape in both bindings. This is the original #1168
/// motivation: WASM dropped the whole `meta` field for the crate's
/// lifetime before #1199. The exhaustive-variants fixture means
/// any future drop of a single variant is caught.
#[test]
fn metadata_equivalence_across_all_meta_value_variants() {
    let txn = Transaction::new(naive_date(2024, 1, 15).unwrap(), "test")
        .with_posting(fixture_posting("Assets:Cash", "100.00", "USD"))
        .with_posting(fixture_posting("Expenses:Food", "-100.00", "USD"))
        .with_tag(Tag::new("trip"));
    let mut txn = txn;
    txn.meta = fixture_metadata_all_variants();

    let directive = Directive::Transaction(txn);
    assert_wire_equivalent("transaction_with_all_meta_variants", &directive);
}

/// Smoke test that a minimal Open directive (no metadata, no
/// optional fields) agrees between bindings. Establishes that the
/// harness doesn't false-positive on a trivial case.
#[test]
fn open_directive_minimal_equivalence() {
    let open = Open::new(naive_date(2024, 1, 1).unwrap(), Account::new("Assets:Cash"))
        .with_currencies(vec![Currency::new("USD")]);
    assert_wire_equivalent("open_minimal", &Directive::Open(open));
}
