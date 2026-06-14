//! Pipeline-boundary property test for the plugin wire format (#1235).
//!
//! Wire-format roundtrip: a directive must survive conversion to the DTO
//! (`DirectiveWrapper`, the JSON shape plugins see), a JSON
//! serialize/deserialize, and conversion back — unchanged. This catches
//! serialization/DTO drift one layer below the cross-binding harness.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Balance, Close, Directive, NaiveDate, Open, Posting, Price, Transaction,
};
use rustledger_plugin::{directive_to_wrapper, wrapper_to_directive};
use rustledger_plugin_types::DirectiveWrapper;

fn arb_date() -> impl Strategy<Value = NaiveDate> {
    (2000i32..2100, 1u32..13, 1u32..28)
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

fn arb_posting() -> impl Strategy<Value = Posting> {
    (arb_account(), arb_amount()).prop_map(|(a, amt)| Posting::new(a, amt))
}

fn arb_transaction() -> impl Strategy<Value = Transaction> {
    (
        arb_date(),
        prop::collection::vec(arb_posting(), 1..4),
        "[A-Za-z ]{0,12}",
    )
        .prop_map(|(d, postings, narration)| {
            let mut t = Transaction::new(d, narration);
            for p in postings {
                t = t.with_synthesized_posting(p);
            }
            t
        })
}

/// Directives built from constructors only (no metadata/flags/comments),
/// so the DTO roundtrip is value-preserving — any inequality is genuine
/// wire-format drift, not an un-serialized side field.
fn arb_directive() -> impl Strategy<Value = Directive> {
    prop_oneof![
        arb_transaction().prop_map(Directive::Transaction),
        (arb_date(), arb_account()).prop_map(|(d, a)| Directive::Open(Open::new(d, a))),
        (arb_date(), arb_account()).prop_map(|(d, a)| Directive::Close(Close::new(d, a))),
        (arb_date(), arb_account(), arb_amount())
            .prop_map(|(d, a, amt)| Directive::Balance(Balance::new(d, a, amt))),
        (arb_date(), arb_currency(), arb_amount())
            .prop_map(|(d, c, amt)| Directive::Price(Price::new(d, c, amt))),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn directive_survives_json_wire_roundtrip(d in arb_directive()) {
        let wrapper = directive_to_wrapper(&d);
        let json = serde_json::to_string(&wrapper).expect("serialize DTO");
        let wrapper2: DirectiveWrapper = serde_json::from_str(&json).expect("deserialize DTO");
        let d2 = wrapper_to_directive(&wrapper2).expect("convert DTO back to core");
        prop_assert_eq!(d2, d, "directive changed across the JSON wire roundtrip");
    }
}
