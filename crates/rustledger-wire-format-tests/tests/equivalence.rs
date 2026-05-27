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
//! ## What this catches — and what it doesn't
//!
//! Equivalence alone catches **drift between bindings**: if one
//! binding starts emitting a different shape than the other, the
//! corresponding fixture fails. It does **not** catch
//! **wrong-in-lockstep** bugs — if both bindings emit the same buggy
//! shape, the equivalence check passes silently.
//!
//! For audit fixtures that need to verify specific fields are
//! actually present (and non-trivially-empty) in the wire shape,
//! use [`assert_wire_format`] with the field paths listed. It
//! combines presence + non-empty + equivalence in one call, computes
//! both bindings' JSON exactly once, and catches both failure modes
//! (field missing, field always-empty).
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
    Account, Amount, Balance, Close, Commodity, CostNumber, CostSpec, Currency, Custom, Directive,
    Document, Event, IncompleteAmount, Link, MetaValue, Metadata, Note, Open, Pad, Posting, Price,
    PriceAnnotation, PriceKind, Query, Spanned, Tag, Transaction, naive_date,
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

/// Strip empty `meta` objects and explicit nulls from the directive
/// and its `postings` children. **Does not** recurse into the `meta`
/// object itself: inside `meta`, `null` is a legitimate value —
/// `MetaValue::None` serializes as `null` in both bindings, and the
/// metadata-variant fixture deliberately includes a `none-key: null`
/// entry to pin that variant's wire shape. Stripping nulls there
/// would silently hide a future drop of the `None` variant.
///
/// See divergences #2 and #3 in the module doc.
fn strip_empty_meta_and_directive_nulls(json: &mut serde_json::Value) {
    let Some(map) = json.as_object_mut() else {
        return;
    };
    map.retain(|key, value| {
        if value.is_null() {
            return false;
        }
        if key == "meta" && value.as_object().is_some_and(serde_json::Map::is_empty) {
            return false;
        }
        true
    });
    // Descend into `postings` (each posting can also carry null
    // optional fields like `flag` per audit finding #1205) but NOT
    // into `meta`.
    if let Some(postings) = map.get_mut("postings").and_then(|p| p.as_array_mut()) {
        for posting in postings {
            strip_empty_meta_and_directive_nulls(posting);
        }
    }
}

/// Convert a `Directive` through both bindings' `directive_to_json`
/// in one pass and return both raw JSON values (pre-normalization).
/// Centralizes the conversion-site arguments so a future change to
/// either binding's signature only edits one place.
fn convert_through_both_bindings(directive: &Directive) -> (serde_json::Value, serde_json::Value) {
    let ffi_wasi = serde_json::to_value(rustledger_ffi_wasi::convert::directive_to_json(
        directive,
        1,
        "test.bean",
    ))
    .expect("FFI-WASI DirectiveJson is always JSON-serializable");
    let wasm = serde_json::to_value(rustledger_wasm::convert::directive_to_json(directive))
        .expect("WASM DirectiveJson is always JSON-serializable");
    (ffi_wasi, wasm)
}

/// Walk a JSON value via dot-separated `path` (e.g. `"tags"`,
/// `"postings.0.account"`) and return the value at that location, or
/// `None` if any segment is missing.
///
/// **Path syntax constraint**: segments split on `.` and `usize`-
/// parseable segments index arrays. No escape mechanism for literal
/// dots in keys — if a future fixture uses a metadata key like
/// `"app.feature"`, this helper will misroute. Avoid such keys in
/// fixtures (this is a test-only utility, not a public API).
fn json_get_path<'v>(value: &'v serde_json::Value, path: &str) -> Option<&'v serde_json::Value> {
    let mut cursor = value;
    for segment in path.split('.') {
        cursor = if let Ok(idx) = segment.parse::<usize>() {
            cursor.get(idx)?
        } else {
            cursor.get(segment)?
        };
    }
    Some(cursor)
}

/// Whether a JSON value is "trivially-default" — null, empty array,
/// or empty object. Used by [`assert_wire_format`]'s field-presence
/// checks to catch a binding that emits the field but always-empty
/// (which would slip past a pure key-existence check).
fn is_trivially_default(value: &serde_json::Value) -> bool {
    match value {
        serde_json::Value::Null => true,
        serde_json::Value::Array(a) => a.is_empty(),
        serde_json::Value::Object(o) => o.is_empty(),
        _ => false,
    }
}

/// One-call audit helper: compute both bindings' JSON once, assert
/// every `required_field` is present **and non-trivially-default**
/// in both outputs, then assert the normalized shapes are equivalent.
///
/// Pass an empty `required_fields` slice for plain equivalence-only
/// fixtures (smoke tests, variants where there's nothing field-
/// specific to pin). Audit fixtures that care about specific fields
/// being on the wire — and about a future regression that emits the
/// field always-empty — list those fields' dot-paths.
///
/// "Non-trivially-default" means: not `null`, not `[]`, not `{}`.
/// Catches both the field-missing failure mode (e.g. #1205 dropping
/// `Posting.flag`) and the field-always-empty failure mode (e.g. a
/// future regression that emits `"tags": []` regardless of input).
#[track_caller]
fn assert_wire_format(label: &str, directive: &Directive, required_fields: &[&str]) {
    let (mut ffi_wasi, mut wasm) = convert_through_both_bindings(directive);

    // Presence + non-empty checks BEFORE normalization, so the
    // assertion error message shows the actual binding output.
    for path in required_fields {
        for (binding, value) in [("ffi-wasi", &ffi_wasi), ("wasm", &wasm)] {
            let found = json_get_path(value, path).unwrap_or_else(|| {
                panic!(
                    "fixture {label:?}: {binding} output missing field {path:?}\nfull output: {value:#}",
                )
            });
            assert!(
                !is_trivially_default(found),
                "fixture {label:?}: {binding} output has field {path:?} but value is trivially default ({found:#}) — likely an always-empty regression\nfull output: {value:#}",
            );
        }
    }

    // Equivalence check after normalization.
    strip_source_position_keys(&mut ffi_wasi);
    strip_empty_meta_and_directive_nulls(&mut ffi_wasi);
    strip_empty_meta_and_directive_nulls(&mut wasm);
    assert_eq!(
        ffi_wasi, wasm,
        "wire-format divergence between FFI-WASI and WASM for fixture {label:?}",
    );
}

// =============================================================================
// Fixture builders
// =============================================================================

fn fixture_posting(account: &str, amount_str: &str, currency: &str) -> Spanned<Posting> {
    Spanned::synthesized(Posting::new(
        Account::new(account),
        Amount::new(
            amount_str
                .parse()
                .expect("fixture amount must parse as Decimal"),
            Currency::new(currency),
        ),
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

/// Metadata equivalence on a Transaction — every `MetaValue`
/// flavor produces the same JSON shape in both bindings. This is
/// the original #1168 motivation: WASM dropped the whole `meta`
/// field for the crate's lifetime before #1199. The exhaustive-
/// variants fixture means any future drop of a single variant is
/// caught.
#[test]
fn metadata_equivalence_on_transaction_directive() {
    let mut txn = Transaction::new(naive_date(2024, 1, 15).unwrap(), "test")
        .with_posting(fixture_posting("Assets:Cash", "100.00", "USD"))
        .with_posting(fixture_posting("Expenses:Food", "-100.00", "USD"))
        .with_tag(Tag::new("trip"));
    txn.meta = fixture_metadata_all_variants();

    let directive = Directive::Transaction(txn);
    assert_wire_format("transaction_with_all_meta_variants", &directive, &["meta"]);
}

/// Metadata equivalence on an Open — same exhaustive `MetaValue`
/// fixture, different directive variant. Catches a binding that
/// handles metadata correctly on Transaction but drops it on
/// other directive variants.
#[test]
fn metadata_equivalence_on_open_directive() {
    let open = Open::new(naive_date(2024, 1, 1).unwrap(), Account::new("Assets:Cash"))
        .with_currencies(vec![Currency::new("USD")])
        .with_meta(fixture_metadata_all_variants());
    let directive = Directive::Open(open);
    assert_wire_format("open_with_all_meta_variants", &directive, &["meta"]);
}

/// Metadata equivalence on a Document — also covers the audit
/// candidate fields (`tags`/`links`) when carrying metadata.
#[test]
fn metadata_equivalence_on_document_directive() {
    let document = Document {
        date: naive_date(2024, 1, 15).unwrap(),
        account: Account::new("Assets:Bank"),
        path: "statements/2024-01.pdf".to_string(),
        tags: vec![Tag::new("statement")],
        links: vec![],
        meta: fixture_metadata_all_variants(),
    };
    let directive = Directive::Document(document);
    assert_wire_format("document_with_all_meta_variants", &directive, &["meta"]);
}

/// Smoke test that a minimal Open directive (no metadata, no
/// optional fields) agrees between bindings. Establishes that the
/// harness doesn't false-positive on a trivial case.
#[test]
fn open_directive_minimal_equivalence() {
    let open = Open::new(naive_date(2024, 1, 1).unwrap(), Account::new("Assets:Cash"))
        .with_currencies(vec![Currency::new("USD")]);
    assert_wire_format("open_minimal", &Directive::Open(open), &[]);
}

#[test]
fn open_with_booking_method_equivalence() {
    let open = Open::new(naive_date(2024, 1, 1).unwrap(), Account::new("Assets:Cash"))
        .with_currencies(vec![Currency::new("USD")])
        .with_booking("STRICT");
    // Pin `booking` is present in both wire shapes — pre-#1199 WASM
    // emitted it as a Debug-formatted quoted string; the audit
    // confirmed the format is now standardized.
    assert_wire_format("open_with_booking", &Directive::Open(open), &["booking"]);
}

#[test]
fn close_directive_equivalence() {
    let close = Close::new(
        naive_date(2024, 12, 31).unwrap(),
        Account::new("Assets:Cash"),
    );
    assert_wire_format("close_minimal", &Directive::Close(close), &[]);
}

/// Audit finding from issue #1200 item 3: WASM drops `Balance.tolerance`
/// entirely from its wire shape; FFI-WASI emits it. Tracked in #1206
/// with a concrete fix plan. Remove the `#[ignore]` once WASM emits
/// the field — the test then pins the convergence going forward.
#[test]
#[ignore = "WASM drops Balance.tolerance — tracked in #1206"]
fn balance_directive_with_tolerance_equivalence() {
    let mut balance = Balance::new(
        naive_date(2024, 6, 1).unwrap(),
        Account::new("Assets:Cash"),
        Amount::new(dec!(1000.00), Currency::new("USD")),
    );
    balance.tolerance = Some(dec!(0.01));
    assert_wire_format(
        "balance_with_tolerance",
        &Directive::Balance(balance),
        &["tolerance"],
    );
}

#[test]
fn pad_directive_equivalence() {
    let pad = Pad::new(
        naive_date(2024, 1, 1).unwrap(),
        Account::new("Assets:Cash"),
        Account::new("Equity:Opening-Balances"),
    );
    assert_wire_format("pad_basic", &Directive::Pad(pad), &[]);
}

#[test]
fn commodity_directive_equivalence() {
    let commodity = Commodity::new(naive_date(2024, 1, 1).unwrap(), Currency::new("USD"));
    assert_wire_format("commodity_basic", &Directive::Commodity(commodity), &[]);
}

#[test]
fn price_directive_equivalence() {
    let price = Price::new(
        naive_date(2024, 1, 1).unwrap(),
        Currency::new("AAPL"),
        Amount::new(dec!(195.50), Currency::new("USD")),
    );
    assert_wire_format("price_basic", &Directive::Price(price), &[]);
}

#[test]
fn event_directive_equivalence() {
    let event = Event::new(naive_date(2024, 6, 1).unwrap(), "location", "Tokyo");
    assert_wire_format("event_basic", &Directive::Event(event), &[]);
}

#[test]
fn note_directive_equivalence() {
    let note = Note::new(
        naive_date(2024, 1, 1).unwrap(),
        Account::new("Assets:Cash"),
        "year-end reconciliation",
    );
    assert_wire_format("note_basic", &Directive::Note(note), &[]);
}

/// Audit finding from issue #1200 item 3 — caught by the
/// `assert_wire_format` helper's field-presence check, not by
/// equivalence: **both bindings** drop `Document.tags` and
/// `Document.links` from their wire shape (lockstep-wrong, so
/// equivalence alone would have passed silently). Tracked in #1208
/// with a concrete fix plan for both bindings.
#[test]
#[ignore = "Both bindings drop Document.tags and Document.links — tracked in #1208"]
fn document_directive_with_tags_and_links_equivalence() {
    let document = Document {
        date: naive_date(2024, 1, 15).unwrap(),
        account: Account::new("Assets:Bank"),
        path: "statements/2024-01.pdf".to_string(),
        tags: vec![Tag::new("statement"), Tag::new("bank")],
        links: vec![Link::new("inv-2024-01")],
        meta: Metadata::default(),
    };
    assert_wire_format(
        "document_with_tags_and_links",
        &Directive::Document(document),
        &["tags", "links"],
    );
}

#[test]
fn query_directive_equivalence() {
    let query = Query::new(
        naive_date(2024, 1, 1).unwrap(),
        "expenses",
        "SELECT account, sum(position)",
    );
    assert_wire_format("query_basic", &Directive::Query(query), &[]);
}

/// Audit finding from issue #1200 item 3: `Custom.values` is present
/// in both bindings (since #1199), but the **shape** diverges. FFI-WASI
/// emits each value as a tagged union `{type: "...", value: ...}`,
/// which is type-safe — a JS consumer can distinguish a `Date` value
/// from a `String` value. WASM emits values raw (the bare string,
/// number, or object), which is lossy. Tracked in #1207 with a fix
/// plan to adopt the tagged shape on the WASM side.
#[test]
#[ignore = "WASM emits Custom.values raw (lossy); tagged union expected — tracked in #1207"]
fn custom_directive_with_all_value_variants_equivalence() {
    let custom = Custom {
        date: naive_date(2024, 1, 1).unwrap(),
        custom_type: "budget".to_string(),
        values: vec![
            MetaValue::String("Q1".to_string()),
            MetaValue::Account(Account::new("Expenses:Food")),
            MetaValue::Amount(Amount::new(dec!(500.00), Currency::new("USD"))),
            MetaValue::Date(naive_date(2024, 3, 31).unwrap()),
            MetaValue::Number(dec!(0.85)),
            MetaValue::Bool(true),
        ],
        meta: Metadata::default(),
    };
    assert_wire_format(
        "custom_with_all_value_variants",
        &Directive::Custom(custom),
        &["values"],
    );
}

// =============================================================================
// Posting-level audits (issue #1200 item 3)
// =============================================================================

/// Posting with cost spec (`{...}` syntax). FFI-WASI and WASM both
/// have to serialize the `CostSpec` shape, including the `kind`-
/// tagged `CostNumber` enum that #1178 standardized.
#[test]
fn posting_with_cost_spec_equivalence() {
    let posting = Posting::new(
        Account::new("Assets:Stock:AAPL"),
        Amount::new(dec!(10), Currency::new("AAPL")),
    )
    .with_cost(CostSpec {
        number: Some(CostNumber::PerUnit {
            value: dec!(150.00),
        }),
        currency: Some(Currency::new("USD")),
        date: Some(naive_date(2024, 1, 15).unwrap()),
        label: None,
        merge: false,
    });
    let txn = Transaction::new(naive_date(2024, 1, 15).unwrap(), "buy")
        .with_posting(Spanned::synthesized(posting))
        .with_posting(fixture_posting("Assets:Cash", "-1500.00", "USD"));
    assert_wire_format(
        "posting_with_cost_spec",
        &Directive::Transaction(txn),
        &["postings.0.cost"],
    );
}

/// Posting with price annotation (`@` for per-unit, `@@` for total).
#[test]
fn posting_with_price_annotation_equivalence() {
    let posting = Posting::new(
        Account::new("Assets:FX"),
        Amount::new(dec!(100), Currency::new("EUR")),
    )
    .with_price(PriceAnnotation {
        kind: PriceKind::Unit,
        amount: Some(IncompleteAmount::Complete(Amount::new(
            dec!(1.10),
            Currency::new("USD"),
        ))),
    });
    let txn = Transaction::new(naive_date(2024, 6, 1).unwrap(), "fx")
        .with_posting(Spanned::synthesized(posting))
        .with_posting(fixture_posting("Assets:Cash", "-110.00", "USD"));
    assert_wire_format(
        "posting_with_price_annotation",
        &Directive::Transaction(txn),
        &["postings.0.price"],
    );
}

/// Pins the fix from #1205: WASM previously dropped `Posting.flag`
/// (the `!` flag on individual postings) from its wire shape while
/// FFI-WASI emitted it. After #1205 both bindings emit the field as
/// an optional stringified char (`"!"`, `"*"`).
#[test]
fn posting_with_flag_equivalence() {
    let posting = Posting::new(
        Account::new("Assets:Cash"),
        Amount::new(dec!(100), Currency::new("USD")),
    )
    .with_flag('!');
    let txn = Transaction::new(naive_date(2024, 1, 1).unwrap(), "pending")
        .with_posting(Spanned::synthesized(posting))
        .with_posting(fixture_posting("Expenses:Misc", "-100.00", "USD"));
    assert_wire_format(
        "posting_with_flag",
        &Directive::Transaction(txn),
        &["postings.0.flag"],
    );
}
