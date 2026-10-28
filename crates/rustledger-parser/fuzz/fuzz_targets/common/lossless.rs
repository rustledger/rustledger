//! The lossless round-trip assertions, shared by `fuzz_parse` and
//! `fuzz_green_eq_red` through `#[path]` so both corpora check the same
//! property.
//!
//! `parse_structured` documents "round-trip byte-identical for every UTF-8
//! input", and the lossless token stream must cover the input exactly once,
//! in order. Both were broken by column-0 `#` comments (#2769, #2775)
//! without any fuzz target noticing, because none asserted them.

use rustledger_parser::logos_lexer::tokenize_lossless;
use rustledger_parser::parse_structured;

pub fn assert_lossless(input: &str) {
    assert_eq!(
        parse_structured(input).text().to_string(),
        input,
        "parse_structured is not lossless"
    );

    let mut at = 0;
    for (_, span) in tokenize_lossless(input) {
        assert_eq!(span.start, at, "lossless token stream has a gap or overlap");
        at = span.end;
    }
    assert_eq!(at, input.len(), "lossless token stream stops short");
}
