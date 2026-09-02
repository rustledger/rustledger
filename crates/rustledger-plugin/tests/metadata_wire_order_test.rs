//! Metadata reaches the plugin wire sorted by key, so identical metadata has
//! one representation.
//!
//! `Metadata` is an `FxHashMap`, but the wire type is a `Vec<(String,
//! MetaValueData)>` whose equality and `MessagePack` encoding are ordered.
//! Collecting the map directly made the wire depend on insertion order: two
//! directives carrying the same metadata could encode to different bytes.
//!
//! Found reviewing #2226, which adds `PartialEq` to these types — that is what
//! turned a latent nondeterminism into a visible one, since two equal
//! directives could then compare unequal. `FxHash` is not randomized, so this
//! was never run-to-run flakiness; it was silently reproducible, which reads
//! as a real difference rather than an artifact.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, MetaValue, NaiveDate, Open, Posting, Transaction};
use rustledger_plugin::convert::directive_to_wrapper;
use rustledger_plugin::types::{DirectiveData, DirectiveWrapper};

fn date() -> NaiveDate {
    rustledger_core::naive_date(2024, 1, 1).unwrap()
}

const KEYS: [&str; 6] = ["epsilon", "zeta", "delta", "alpha", "gamma", "beta"];

fn open_with(order: &[&str]) -> Directive {
    let mut o = Open::new(date(), "Assets:Bank");
    for k in order {
        o.meta
            .insert((*k).to_string(), MetaValue::String((*k).to_string()));
    }
    Directive::Open(o)
}

fn meta_keys(w: &DirectiveWrapper) -> Vec<String> {
    match &w.data {
        DirectiveData::Open(o) => o.metadata.iter().map(|(k, _)| k.clone()).collect(),
        _ => panic!("expected an Open"),
    }
}

/// Insertion order must not survive into the wire.
#[test]
fn metadata_reaches_the_wire_sorted_by_key() {
    let forward = directive_to_wrapper(&open_with(&KEYS));
    let mut reversed = KEYS;
    reversed.reverse();
    let backward = directive_to_wrapper(&open_with(&reversed));

    let sorted = {
        let mut k: Vec<String> = KEYS.iter().map(|s| (*s).to_string()).collect();
        k.sort();
        k
    };
    assert_eq!(meta_keys(&forward), sorted, "keys must arrive sorted");
    assert_eq!(
        meta_keys(&forward),
        meta_keys(&backward),
        "insertion order must not reach the wire",
    );
}

/// The encoded bytes must match too — the `Vec` order is what `MessagePack`
/// writes, so an unsorted wire made identical metadata encode differently.
/// Asserting on the keys alone would not catch a change that reordered the
/// values against them.
#[test]
fn identical_metadata_encodes_to_identical_bytes() {
    let forward = directive_to_wrapper(&open_with(&KEYS));
    let mut reversed = KEYS;
    reversed.reverse();
    let backward = directive_to_wrapper(&open_with(&reversed));

    let a = rmp_serde::to_vec(&forward).expect("encode");
    let b = rmp_serde::to_vec(&backward).expect("encode");
    assert_eq!(a, b, "equal metadata must encode to equal bytes");
}

/// Posting metadata goes through the same helper. Postings are converted by a
/// different function from directives, and the two once held separate copies
/// of this expression.
#[test]
fn posting_metadata_is_sorted_too() {
    let mut posting = Posting::new("Assets:Bank", Amount::new(dec!(1), "USD"));
    for k in KEYS.iter().rev() {
        posting
            .meta
            .insert((*k).to_string(), MetaValue::String((*k).to_string()));
    }
    let txn = Transaction::new(date(), "t").with_synthesized_posting(posting);
    let wrapper = directive_to_wrapper(&Directive::Transaction(txn));

    let DirectiveData::Transaction(t) = &wrapper.data else {
        panic!("expected a Transaction");
    };
    let keys: Vec<String> = t.postings[0]
        .metadata
        .iter()
        .map(|(k, _)| k.clone())
        .collect();
    let mut sorted = keys.clone();
    sorted.sort();
    assert_eq!(keys, sorted, "posting metadata must be sorted as well");
}
