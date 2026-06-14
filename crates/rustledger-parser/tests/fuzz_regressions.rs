//! Regression tests for crashes found by the fuzzers.
//!
//! The parser must satisfy a no-panic invariant: for ANY UTF-8 input it may
//! return errors, but must never panic. Each test here pins a previously
//! crashing input from `cargo fuzz`.

/// `fuzz_parse` crash (char-boundary panic in `indented_directive_check`).
///
/// A top-level directive whose first content token starts inside a multi-byte
/// UTF-8 char made the indent check slice the source string at a byte index
/// that was not a char boundary — `stripped[..content_start]` in
/// `cst/convert.rs` panicked with "end byte index N is not a char boundary".
/// The parser must handle this gracefully.
#[test]
fn fuzz_parse_indented_directive_char_boundary_no_panic() {
    let data = include_bytes!("fuzz_regressions/crash_indented_directive_char_boundary.bin");
    // The fuzz target only parses valid UTF-8; this corpus entry is valid UTF-8.
    let input = std::str::from_utf8(data).expect("crash fixture is valid UTF-8");
    // Must not panic. We don't assert on the (error) result — only no panic.
    let _ = rustledger_parser::parse(input);
}
