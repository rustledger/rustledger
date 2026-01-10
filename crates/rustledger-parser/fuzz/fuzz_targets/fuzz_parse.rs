#![no_main]
//! Fuzz target for the main parser.
//!
//! This fuzzer tests the parser's robustness against arbitrary input.
//! It ensures the parser doesn't panic, crash, or exhibit undefined behavior
//! when processing malformed or malicious input.

use libfuzzer_sys::fuzz_target;
use rustledger_parser::parse;

fuzz_target!(|data: &[u8]| {
    // Only process valid UTF-8 strings
    if let Ok(input) = std::str::from_utf8(data) {
        // The parser should never panic, regardless of input
        // It may return errors, but should handle them gracefully
        let _ = parse(input);
    }
});
