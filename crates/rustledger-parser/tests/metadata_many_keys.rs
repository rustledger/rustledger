//! A directive with a huge number of metadata lines parses and formats in
//! near-linear time (#2835 review).
//!
//! `Metadata` is a vector with a linear-scan `insert`, so building it with one
//! insert per line made the parser quadratic: one transaction with 40,000
//! keys took 2.35 s to parse where the hash map took 0.08 s, and 100,000 took
//! 36 s. The parser reads untrusted text and the LSP reparses on every edit,
//! so it builds through `MetadataBuilder` instead. The exact bound lives in
//! `rustledger-core` (a key-comparison count); this is the end-to-end check
//! with a loose time bound: about 4 s for this test in a debug build on a
//! loaded machine, against 34 s for the quadratic build.

use rustledger_core::Directive;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::parse;
use std::time::{Duration, Instant};

const KEYS: usize = 50_000;

fn ledger() -> String {
    let mut src = String::from("2024-01-02 * \"many\"\n");
    for i in 0..KEYS {
        src.push_str(&format!("  key-{i}: {i}\n"));
    }
    // A repeated key keeps its first place and its last value.
    src.push_str("  key-0: \"last\"\n");
    src
}

fn check(path: &str, directives: &[rustledger_core::Spanned<Directive>]) {
    let Directive::Transaction(t) = &directives[0].value else {
        panic!("{path}: expected a transaction");
    };
    assert_eq!(t.meta.len(), KEYS, "{path}");
    let (first, value) = t.meta.iter().next().expect("a key");
    assert_eq!(first.as_str(), "key-0", "{path}");
    assert_eq!(value.to_string(), "\"last\"", "{path}");
}

#[test]
fn test_parse_many_metadata_keys_is_not_quadratic() {
    let src = ledger();
    let start = Instant::now();
    let green = parse(&src);
    let red = parse_red_only(&src);
    let elapsed = start.elapsed();
    check("green", &green.directives);
    check("red", &red.directives);
    assert!(
        elapsed < Duration::from_secs(15),
        "parsing one transaction with {KEYS} metadata keys (twice) took {elapsed:?}; \
         building `Metadata` one `insert` at a time is quadratic"
    );
}
