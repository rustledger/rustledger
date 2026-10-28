#![no_main]
//! Fuzz target for the main parser.
//!
//! This fuzzer tests the parser's robustness against arbitrary input.
//! It ensures the parser doesn't panic, crash, or exhibit undefined behavior
//! when processing malformed or malicious input.
//!
//! It also asserts the lossless guarantee `parse_structured` documents
//! ("round-trip byte-identical for every UTF-8 input") and that the lossless
//! token stream covers the input exactly once, in order. Both were broken
//! by column-0 `#` comments (#2769, #2775) without any fuzz target noticing,
//! because this one only checked for panics.

use libfuzzer_sys::fuzz_target;
use rustledger_parser::logos_lexer::tokenize_lossless;
use rustledger_parser::{parse, parse_structured};

fuzz_target!(|data: &[u8]| {
    // Only process valid UTF-8 strings
    if let Ok(input) = std::str::from_utf8(data) {
        // The parser should never panic, regardless of input
        // It may return errors, but should handle them gracefully
        let _ = parse(input);

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
});
