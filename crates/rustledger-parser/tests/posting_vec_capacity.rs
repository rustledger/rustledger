//! A transaction's postings `Vec` is sized to its postings on both conversion
//! paths (#2834). The green fast path counted them; the path taken by a
//! transaction with metadata or comments grew the vector by push, so two
//! postings held capacity 4: 256 unused bytes per transaction, retained for
//! the life of the ledger.

use rustledger_core::Directive;
use rustledger_parser::parse;

fn posting_capacities(src: &str) -> Vec<(usize, usize)> {
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    result
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some((t.postings.len(), t.postings.capacity())),
            _ => None,
        })
        .collect()
}

#[test]
fn test_parse_sizes_postings_exactly_on_both_conversion_paths() {
    for (label, src) in [
        (
            "plain",
            "2024-01-01 * \"x\"\n  Assets:A  1 USD\n  Assets:B\n",
        ),
        (
            "transaction metadata",
            "2024-01-01 * \"x\"\n  k1: \"v\"\n  Assets:A  1 USD\n  Assets:B\n",
        ),
        (
            "posting metadata",
            "2024-01-01 * \"x\"\n  Assets:A  1 USD\n    k1: \"v\"\n  Assets:B\n",
        ),
        (
            "comment between postings",
            "2024-01-01 * \"x\"\n  Assets:A  1 USD\n  ; note\n  Assets:B\n",
        ),
        (
            "three postings with metadata",
            "2024-01-01 * \"x\"\n  k1: \"v\"\n  Assets:A  1 USD\n  Assets:B  1 USD\n  Assets:C\n",
        ),
    ] {
        for (len, cap) in posting_capacities(src) {
            assert_eq!(cap, len, "{label}: {len} postings held capacity {cap}");
        }
    }
}
