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

/// Strip empty `meta` objects and explicit nulls from the **top level
/// of the directive only** — never recurse into the `meta` object
/// itself. Inside `meta`, `null` is a legitimate value: `MetaValue::None`
/// serializes as `null` in both bindings, and the metadata-variant
/// fixture deliberately includes a `none-key: null` entry to pin
/// that variant's wire shape. Stripping nulls there would silently
/// hide a future drop of the `None` variant.
///
/// See divergences #2 and #3 in the module doc.
fn strip_top_level_empty_meta_and_nulls(json: &mut serde_json::Value) {
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
    // Recurse into postings (which can also carry null optional
    // fields like `flag` per audit finding #1205) but NOT into `meta`.
    if let Some(postings) = map.get_mut("postings").and_then(|p| p.as_array_mut()) {
        for posting in postings {
            strip_top_level_empty_meta_and_nulls(posting);
        }
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
    strip_top_level_empty_meta_and_nulls(&mut ffi_wasi_value);

    let wasm_json = rustledger_wasm::convert::directive_to_json(directive);
    let mut wasm_value =
        serde_json::to_value(&wasm_json).expect("WASM DirectiveJson is always JSON-serializable");
    strip_top_level_empty_meta_and_nulls(&mut wasm_value);

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

#[test]
fn open_with_booking_method_equivalence() {
    let open = Open::new(naive_date(2024, 1, 1).unwrap(), Account::new("Assets:Cash"))
        .with_currencies(vec![Currency::new("USD")])
        .with_booking("STRICT");
    assert_wire_equivalent("open_with_booking", &Directive::Open(open));
}

#[test]
fn close_directive_equivalence() {
    let close = Close::new(
        naive_date(2024, 12, 31).unwrap(),
        Account::new("Assets:Cash"),
    );
    assert_wire_equivalent("close_minimal", &Directive::Close(close));
}

/// Audit finding from issue #1200 item 3: WASM drops `Balance.tolerance`
/// entirely from its wire shape; FFI-WASI emits it. Until WASM's
/// `DirectiveJson::Balance` variant gains a `tolerance` field, this
/// test stays `#[ignore]`d but documents the expected convergence
/// target. Remove the `#[ignore]` once WASM is fixed.
#[test]
#[ignore = "WASM drops Balance.tolerance — fix in a follow-up PR; tracked in #1200"]
fn balance_directive_with_tolerance_equivalence() {
    let mut balance = Balance::new(
        naive_date(2024, 6, 1).unwrap(),
        Account::new("Assets:Cash"),
        Amount::new(dec!(1000.00), Currency::new("USD")),
    );
    balance.tolerance = Some(dec!(0.01));
    assert_wire_equivalent("balance_with_tolerance", &Directive::Balance(balance));
}

#[test]
fn pad_directive_equivalence() {
    let pad = Pad::new(
        naive_date(2024, 1, 1).unwrap(),
        Account::new("Assets:Cash"),
        Account::new("Equity:Opening-Balances"),
    );
    assert_wire_equivalent("pad_basic", &Directive::Pad(pad));
}

#[test]
fn commodity_directive_equivalence() {
    let commodity = Commodity::new(naive_date(2024, 1, 1).unwrap(), Currency::new("USD"));
    assert_wire_equivalent("commodity_basic", &Directive::Commodity(commodity));
}

#[test]
fn price_directive_equivalence() {
    let price = Price::new(
        naive_date(2024, 1, 1).unwrap(),
        Currency::new("AAPL"),
        Amount::new(dec!(195.50), Currency::new("USD")),
    );
    assert_wire_equivalent("price_basic", &Directive::Price(price));
}

#[test]
fn event_directive_equivalence() {
    let event = Event::new(naive_date(2024, 6, 1).unwrap(), "location", "Tokyo");
    assert_wire_equivalent("event_basic", &Directive::Event(event));
}

#[test]
fn note_directive_equivalence() {
    let note = Note::new(
        naive_date(2024, 1, 1).unwrap(),
        Account::new("Assets:Cash"),
        "year-end reconciliation",
    );
    assert_wire_equivalent("note_basic", &Directive::Note(note));
}

/// Audit candidate from issue #1200 item 3: `Document.tags` /
/// `Document.links` exist on the core type but were never plumbed
/// through `plugin-types::DocumentData`. The plugin-types DTO is a
/// separate wire shape — this test exercises the FFI-WASI/WASM
/// JSON-RPC + JS API shapes specifically (both have `Document`
/// variants in their `DirectiveJson` enums). If either binding
/// drops `tags`/`links`, this fixture surfaces it.
#[test]
fn document_directive_with_tags_and_links_equivalence() {
    let document = Document {
        date: naive_date(2024, 1, 15).unwrap(),
        account: Account::new("Assets:Bank"),
        path: "statements/2024-01.pdf".to_string(),
        tags: vec![Tag::new("statement"), Tag::new("bank")],
        links: vec![Link::new("inv-2024-01")],
        meta: Metadata::default(),
    };
    assert_wire_equivalent(
        "document_with_tags_and_links",
        &Directive::Document(document),
    );
}

#[test]
fn query_directive_equivalence() {
    let query = Query::new(
        naive_date(2024, 1, 1).unwrap(),
        "expenses",
        "SELECT account, sum(position)",
    );
    assert_wire_equivalent("query_basic", &Directive::Query(query));
}

/// Audit finding from issue #1200 item 3: `Custom.values` is present
/// in both bindings (since #1199), but the **shape** diverges. FFI-WASI
/// emits each value as a tagged union `{type: "...", value: ...}`,
/// which is type-safe — a JS consumer can distinguish a `Date` value
/// from a `String` value. WASM emits values raw (the bare string,
/// number, or object), which is lossy. Marked `#[ignore]` until the
/// WASM side adopts the tagged shape; tracked in #1200.
#[test]
#[ignore = "WASM emits Custom.values raw (lossy); FFI-WASI uses tagged union — fix in a follow-up"]
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
    assert_wire_equivalent("custom_with_all_value_variants", &Directive::Custom(custom));
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
    assert_wire_equivalent("posting_with_cost_spec", &Directive::Transaction(txn));
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
    assert_wire_equivalent(
        "posting_with_price_annotation",
        &Directive::Transaction(txn),
    );
}

/// Audit finding from issue #1200 item 3: WASM drops `Posting.flag`
/// (the `!` flag on individual postings) entirely from its wire
/// shape; FFI-WASI emits it. Same failure mode as the pre-#1199 meta
/// drop — silently absent from one binding. Marked `#[ignore]`
/// until WASM is fixed; tracked in #1200.
#[test]
#[ignore = "WASM drops Posting.flag — fix in a follow-up PR; tracked in #1200"]
fn posting_with_flag_equivalence() {
    let mut posting = Posting::new(
        Account::new("Assets:Cash"),
        Amount::new(dec!(100), Currency::new("USD")),
    );
    posting.flag = Some('!');
    let txn = Transaction::new(naive_date(2024, 1, 1).unwrap(), "pending")
        .with_posting(Spanned::synthesized(posting))
        .with_posting(fixture_posting("Expenses:Misc", "-100.00", "USD"));
    assert_wire_equivalent("posting_with_flag", &Directive::Transaction(txn));
}
