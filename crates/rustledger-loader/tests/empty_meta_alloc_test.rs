//! Loading and booking a ledger whose transactions and postings carry no
//! metadata must leave every `MetaMap` unallocated (#2750 review).
//!
//! `MetaMap` used to implement `DerefMut` as get-or-create, so any pass
//! that merely visited `&mut posting.meta` (re-interning, clearing
//! booking's interpolation marks, neutralizing imported text) boxed an
//! empty map for every posting. `as_map_mut()` is `None` exactly when no
//! map is allocated, so it is the observable this test pins.

use rustledger_core::{Directive, MetaValue};
use rustledger_loader::{Ledger, LoadOptions, load, reintern_directives};

fn load_source(source: &str) -> Ledger {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("main.beancount");
    std::fs::write(&path, source).expect("write fixture");
    load(&path, &LoadOptions::default()).expect("the ledger loads")
}

/// `(transactions, postings)` whose meta map is allocated, by narration
/// and account.
fn allocated(ledger: &mut Ledger) -> (Vec<String>, Vec<String>) {
    let mut txns = Vec::new();
    let mut postings = Vec::new();
    for directive in &mut ledger.directives {
        if let Directive::Transaction(txn) = &mut directive.value {
            if txn.meta.as_map_mut().is_some() {
                txns.push(txn.narration.to_string());
            }
            for posting in &mut txn.postings {
                if posting.meta.as_map_mut().is_some() {
                    postings.push(posting.account.to_string());
                }
            }
        }
    }
    (txns, postings)
}

// A plugin runs so booking adds (and the loader then clears) the
// interpolation marks; the elided `Assets:Cash` legs are interpolated.
const LEDGER: &str = "\
plugin \"beancount.plugins.sellgains\"
2024-01-01 open Assets:Cash
2024-01-01 open Assets:Stock
2024-01-01 open Income:Gains
2024-01-01 open Expenses:Food

2024-01-02 * \"buy\"
  Assets:Stock  10 AAA {10.0 USD}
  Assets:Cash

2024-01-03 * \"Cafe\" \"lunch\" #food ^r1
  Expenses:Food  12.50 USD
  Assets:Cash

2024-01-05 * \"sell\"
  Assets:Stock  -3 AAA {10.0 USD} @ 13.00 USD
  Assets:Cash
  Income:Gains  -9.00 USD
";

#[test]
fn test_load_without_metadata_leaves_meta_maps_unallocated() {
    let mut ledger = load_source(LEDGER);
    assert!(
        ledger.errors.is_empty(),
        "{:?}",
        ledger.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
    let txn_count = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, Directive::Transaction(_)))
        .count();
    assert_eq!(txn_count, 3);

    assert_eq!(allocated(&mut ledger), (vec![], vec![]));

    // The re-intern pass the cache path runs visits every meta map too.
    reintern_directives(&mut ledger.directives);
    assert_eq!(allocated(&mut ledger), (vec![], vec![]));
}

/// Positive control: the observable does see a map that holds data.
#[test]
fn test_load_with_posting_metadata_allocates_only_that_map() {
    let mut ledger = load_source(
        "2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\n\
         2024-01-03 * \"lunch\"\n  Expenses:Food  12.50 USD\n    receipt: \"r1\"\n  Assets:Cash\n",
    );
    assert!(ledger.errors.is_empty());
    assert_eq!(
        allocated(&mut ledger),
        (vec![], vec!["Expenses:Food".to_string()])
    );
    let Directive::Transaction(txn) = &ledger.directives.last().expect("a txn").value else {
        panic!("last directive is the transaction");
    };
    assert_eq!(
        txn.postings[0].meta.get("receipt"),
        Some(&MetaValue::String("r1".into()))
    );
}

/// The `MetaMap` of any directive, borrowed mutably so `as_map_mut` can
/// report whether a map is allocated.
const fn meta_map_mut(directive: &mut Directive) -> &mut rustledger_core::MetaMap {
    match directive {
        Directive::Transaction(d) => &mut d.meta,
        Directive::Balance(d) => &mut d.meta,
        Directive::Open(d) => &mut d.meta,
        Directive::Close(d) => &mut d.meta,
        Directive::Commodity(d) => &mut d.meta,
        Directive::Pad(d) => &mut d.meta,
        Directive::Event(d) => &mut d.meta,
        Directive::Query(d) => &mut d.meta,
        Directive::Note(d) => &mut d.meta,
        Directive::Document(d) => &mut d.meta,
        Directive::Price(d) => &mut d.meta,
        Directive::Custom(d) => &mut d.meta,
    }
}

/// Every directive variant, none carrying source metadata.
const ALL_VARIANTS: &str = "\
option \"operating_currency\" \"USD\"
2024-01-01 commodity USD
2024-01-01 open Assets:Cash USD
2024-01-01 open Assets:Old
2024-01-01 open Equity:Opening
2024-01-02 pad Assets:Cash Equity:Opening
2024-01-03 balance Assets:Cash  100.00 USD
2024-01-03 price EUR 1.10 USD
2024-01-04 note Assets:Cash \"a note\"
2024-01-04 event \"location\" \"Paris\"
2024-01-04 query \"cash\" \"SELECT account\"
2024-01-04 custom \"budget\" Assets:Cash \"monthly\" 10.00 USD
2024-01-04 document Assets:Cash \"receipt.pdf\"
2024-01-05 close Assets:Old
2024-01-06 * \"spend\"
  Assets:Cash  -1.00 USD
  Equity:Opening
";

#[test]
fn test_load_every_variant_without_metadata_leaves_meta_maps_unallocated() {
    let dir = tempfile::tempdir().expect("temp dir");
    std::fs::write(dir.path().join("receipt.pdf"), b"").expect("write document");
    let path = dir.path().join("main.beancount");
    std::fs::write(&path, ALL_VARIANTS).expect("write fixture");
    let mut ledger = load(&path, &LoadOptions::default()).expect("the ledger loads");
    assert!(
        ledger.errors.is_empty(),
        "{:?}",
        ledger.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );

    let mut seen: Vec<&'static str> = ledger
        .directives
        .iter()
        .map(|d| d.value.type_name())
        .collect();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(seen.len(), 12, "the fixture covers every variant: {seen:?}");

    let allocated: Vec<&'static str> = ledger
        .directives
        .iter_mut()
        .filter_map(|d| {
            let name = d.value.type_name();
            meta_map_mut(&mut d.value)
                .as_map_mut()
                .is_some()
                .then_some(name)
        })
        .collect();
    assert!(
        allocated.is_empty(),
        "allocated meta maps on: {allocated:?}"
    );
}
