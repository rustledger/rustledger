//! Pipeline-boundary property test for the plugin wire format (#1235).
//!
//! Wire-format roundtrip: a directive must survive conversion to the DTO
//! (`DirectiveWrapper`, the JSON shape plugins see), a JSON
//! serialize/deserialize, and conversion back — unchanged. This catches
//! serialization/DTO drift one layer below the cross-binding harness.
//!
//! The generators cover all constructor-reachable directive variants and
//! the drift-prone fields that have regressed before — e.g. Document tags
//! and links (#1214), and posting cost specs / price annotations. Metadata,
//! posting flags/comments, and `Custom` value lists are deliberately left
//! out: several have known-lossy or sentinel-based conversions, so they
//! belong in their own focused tests rather than silently weakening this
//! equality check.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Balance, Close, Commodity, CostNumber, CostSpec, Directive, Document, Event, NaiveDate,
    Note, Open, Pad, Posting, Price, PriceAnnotation, Query, Transaction,
};
use rustledger_plugin::{directive_to_wrapper, wrapper_to_directive};
use rustledger_plugin_types::DirectiveWrapper;

fn arb_date() -> impl Strategy<Value = NaiveDate> {
    // 1..=28 so every month is valid (February included) while still
    // covering day 28.
    (2000i32..2100, 1u32..13, 1u32..=28)
        .prop_map(|(y, m, d)| rustledger_core::naive_date(y, m, d).unwrap())
}

fn arb_currency() -> impl Strategy<Value = &'static str> {
    prop_oneof![Just("USD"), Just("EUR"), Just("GBP"), Just("AAPL")]
}

fn arb_account() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        Just("Assets:Bank"),
        Just("Expenses:Food"),
        Just("Income:Salary"),
        Just("Equity:Opening"),
    ]
}

fn arb_amount() -> impl Strategy<Value = Amount> {
    (-1_000_000i64..1_000_000, 0u32..4, arb_currency())
        .prop_map(|(n, scale, c)| Amount::new(Decimal::new(n, scale), c))
}

fn arb_tags() -> impl Strategy<Value = Vec<&'static str>> {
    let tag = prop_oneof![Just("trip"), Just("tax"), Just("reimb"), Just("2024")];
    prop::collection::vec(tag, 0..3)
}

fn arb_links() -> impl Strategy<Value = Vec<&'static str>> {
    let link = prop_oneof![Just("inv-1"), Just("doc-2"), Just("ref-3")];
    prop::collection::vec(link, 0..3)
}

/// Postings in three flavors: plain, cost-bearing (`{N CCY}`), and priced
/// (`@ N CCY`) — the cost-spec and price-annotation conversions are among
/// the most drift-prone in the DTO layer.
fn arb_posting() -> impl Strategy<Value = Posting> {
    prop_oneof![
        (arb_account(), arb_amount()).prop_map(|(a, amt)| Posting::new(a, amt)),
        (
            arb_account(),
            arb_amount(),
            1i64..100_000,
            0u32..3,
            arb_currency()
        )
            .prop_map(|(a, amt, n, scale, c)| {
                let cost = CostSpec::empty()
                    .with_number(CostNumber::PerUnit {
                        value: Decimal::new(n, scale),
                    })
                    .with_currency(c);
                Posting::new(a, amt).with_cost(cost)
            }),
        (arb_account(), arb_amount(), arb_amount())
            .prop_map(
                |(a, amt, price)| Posting::new(a, amt).with_price(PriceAnnotation::unit(price))
            ),
    ]
}

fn arb_transaction() -> impl Strategy<Value = Transaction> {
    (
        arb_date(),
        prop::collection::vec(arb_posting(), 1..4),
        "[A-Za-z ]{0,12}",
        prop::option::of("[A-Za-z ]{1,10}"),
        arb_tags(),
        arb_links(),
    )
        .prop_map(|(d, postings, narration, payee, tags, links)| {
            let mut t = Transaction::new(d, narration);
            if let Some(p) = payee {
                t = t.with_payee(p);
            }
            for tag in tags {
                t = t.with_tag(tag);
            }
            for link in links {
                t = t.with_link(link);
            }
            for p in postings {
                t = t.with_synthesized_posting(p);
            }
            t
        })
}

/// Document directives with tags and links — the field family that
/// regressed in #1214 (both halves of the conversion dropped them).
fn arb_document() -> impl Strategy<Value = Document> {
    (
        arb_date(),
        arb_account(),
        "[a-z/.]{1,16}",
        arb_tags(),
        arb_links(),
    )
        .prop_map(|(d, a, path, tags, links)| {
            let mut doc = Document::new(d, a, path);
            doc.tags = tags.into_iter().map(Into::into).collect();
            doc.links = links.into_iter().map(Into::into).collect();
            doc
        })
}

/// All constructor-reachable directive variants. Equality via `Directive`'s
/// derived `PartialEq` covers every field (`Spanned` compares values only),
/// so any inequality is genuine wire-format drift.
fn arb_directive() -> impl Strategy<Value = Directive> {
    prop_oneof![
        arb_transaction().prop_map(Directive::Transaction),
        (arb_date(), arb_account()).prop_map(|(d, a)| Directive::Open(Open::new(d, a))),
        (arb_date(), arb_account()).prop_map(|(d, a)| Directive::Close(Close::new(d, a))),
        (arb_date(), arb_account(), arb_amount())
            .prop_map(|(d, a, amt)| Directive::Balance(Balance::new(d, a, amt))),
        (arb_date(), arb_currency(), arb_amount())
            .prop_map(|(d, c, amt)| Directive::Price(Price::new(d, c, amt))),
        (arb_date(), arb_currency()).prop_map(|(d, c)| Directive::Commodity(Commodity::new(d, c))),
        (arb_date(), arb_account(), arb_account())
            .prop_map(|(d, a, src)| Directive::Pad(Pad::new(d, a, src))),
        (arb_date(), "[A-Za-z]{1,8}", "[A-Za-z ]{0,12}")
            .prop_map(|(d, ty, val)| Directive::Event(Event::new(d, ty, val))),
        (arb_date(), "[A-Za-z]{1,8}", "[A-Za-z ]{0,16}")
            .prop_map(|(d, name, q)| Directive::Query(Query::new(d, name, q))),
        (arb_date(), arb_account(), "[A-Za-z ]{0,16}")
            .prop_map(|(d, a, c)| Directive::Note(Note::new(d, a, c))),
        arb_document().prop_map(Directive::Document),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn directive_survives_json_wire_roundtrip(d in arb_directive()) {
        // Convert fallible steps into TestCaseError (rather than panicking
        // via `expect`) so proptest keeps shrinking and the failure carries
        // the underlying error.
        let wrapper = directive_to_wrapper(&d);
        let json = serde_json::to_string(&wrapper)
            .map_err(|e| TestCaseError::fail(format!("serialize DTO: {e}")))?;
        let wrapper2: DirectiveWrapper = serde_json::from_str(&json)
            .map_err(|e| TestCaseError::fail(format!("deserialize DTO: {e}")))?;
        let d2 = wrapper_to_directive(&wrapper2)
            .map_err(|e| TestCaseError::fail(format!("convert DTO back to core: {e}")))?;
        prop_assert_eq!(d2, d, "directive changed across the JSON wire roundtrip");
    }
}
