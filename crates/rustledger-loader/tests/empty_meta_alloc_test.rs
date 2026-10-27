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
