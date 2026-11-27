#![no_main]
//! The formatter round-trip properties on arbitrary input: `format_source` is
//! idempotent and keeps what a file means (directives, comments, and which
//! lines are broken), and `try_format_source` agrees with it on clean input.
//! See `common/format_roundtrip.rs`, shared with the parser's
//! `format_roundtrip_properties` test.
//!
//! `fuzz.yml` seeds this target with `fuzz_parse`'s corpus as well as its own,
//! so the parser's fuzz corpus is replayed through the oracle on every run.
use libfuzzer_sys::fuzz_target;

#[path = "common/format_roundtrip.rs"]
mod format_roundtrip;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    if let Err(report) = format_roundtrip::check(src) {
        panic!("{report}");
    }
});
