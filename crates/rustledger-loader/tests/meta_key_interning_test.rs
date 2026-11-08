//! Metadata keys are interned across the whole ledger (#2835).
//!
//! A key repeats on every directive an importer writes (`uuid`, `source`,
//! `memo`), so each one used to be its own heap `String`: four million
//! allocations on a million-transaction ledger. The loader's dedup pass
//! (`reintern_directives`, the same pass that shares accounts and
//! currencies) now points every equal key at one `Arc<str>`, in every file
//! of the ledger and on the cache-hit path alike. The observable is pointer
//! equality: equal keys on different directives share one allocation.

use rustledger_core::{Directive, InternedStr};
use rustledger_loader::{LoadOptions, load};

const MAIN: &str = "\
include \"other.beancount\"
2024-01-01 open Assets:Cash
2024-01-01 open Expenses:Food

2024-01-02 * \"a\"
  source: \"bank\"
  Expenses:Food  1 USD
    memo: \"in\"
  Assets:Cash

2024-01-03 * \"b\"
  source: \"card\"
  Expenses:Food  2 USD
    memo: \"in\"
  Assets:Cash
";

const OTHER: &str = "\
2024-01-04 * \"c\"
  source: \"cash\"
  Expenses:Food  3 USD
    memo: \"out\"
  Assets:Cash
";

/// Every occurrence of `key`, on transactions and postings, in load order.
fn occurrences<'a>(directives: impl Iterator<Item = &'a Directive>, key: &str) -> Vec<InternedStr> {
    let mut found = Vec::new();
    for d in directives {
        if let Directive::Transaction(txn) = d {
            if let Some((k, _)) = txn.meta.get_key_value(key) {
                found.push(k.clone());
            }
            for p in &txn.postings {
                if let Some((k, _)) = p.meta.get_key_value(key) {
                    found.push(k.clone());
                }
            }
        }
    }
    found
}

fn assert_shared(keys: &[InternedStr], key: &str, expected: usize) {
    assert_eq!(
        keys.len(),
        expected,
        "fixture should carry {expected} `{key}` keys"
    );
    for k in &keys[1..] {
        assert!(
            k.ptr_eq(&keys[0]),
            "every `{key}` key must share one allocation; the dedup pass did not intern it"
        );
    }
}

fn write_fixture(dir: &std::path::Path) -> std::path::PathBuf {
    let path = dir.join("main.beancount");
    std::fs::write(&path, MAIN).expect("write main");
    std::fs::write(dir.join("other.beancount"), OTHER).expect("write other");
    path
}

fn assert_keys_shared<'a>(directives: impl Iterator<Item = &'a Directive> + Clone) {
    // Across directives, transactions and postings, and the two files.
    assert_shared(&occurrences(directives.clone(), "source"), "source", 3);
    assert_shared(&occurrences(directives, "memo"), "memo", 3);
}

#[test]
fn test_load_metadata_keys_share_one_allocation() {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = write_fixture(dir.path());
    let ledger = load(&path, &LoadOptions::default()).expect("the ledger loads");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    assert_keys_shared(ledger.directives.iter().map(|d| &d.value));
}

#[test]
fn test_cache_hit_metadata_keys_share_one_allocation() {
    // The cache-hit path deserializes under an `InternScope` instead of
    // running the dedup pass, so it has to establish the same sharing.
    for var in [
        rustledger_loader::CACHE_FILENAME_ENV,
        rustledger_loader::DISABLE_CACHE_ENV,
    ] {
        assert!(
            std::env::var_os(var).is_none(),
            "unset {var} before running this test - it redirects or disables \
             the cache this test reads back",
        );
    }
    let dir = tempfile::tempdir().expect("temp dir");
    let path = write_fixture(dir.path());
    let loaded = rustledger_loader::Loader::new()
        .load(&path)
        .expect("the ledger loads");
    let entry = rustledger_loader::CacheEntry {
        directives: loaded.directives.clone(),
        options: rustledger_loader::CachedOptions::from(&loaded.options),
        plugins: Vec::new(),
        files: vec![path.to_string_lossy().into_owned()],
    };
    rustledger_loader::save_cache_entry(&path, &entry).expect("save");
    let back = rustledger_loader::load_cache_entry(&path).expect("cache hit");
    assert_keys_shared(back.directives.iter().map(|d| &d.value));
}
