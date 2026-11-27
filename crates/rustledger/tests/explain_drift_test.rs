//! Drift guard: `rledger explain` knows every diagnostic code `rledger check`
//! can print.
//!
//! `explain` once knew only the validator's `ErrorCode`s, so `check` printed
//! codes (`E7011`, every `P` code, the loader's `E0xxx`) that `explain`
//! called unknown. Each code is enumerated here from its canonical
//! definition, never from a list kept beside `explain`:
//!
//! - validation codes: [`ErrorCode::ALL`];
//! - parse codes: `P{kind_code:04}` for every [`ParseErrorKind`], via
//!   [`ParseError::every_kind_sample`] (the code `check` formats);
//! - option codes: [`OptionWarning::ALL_CODES`] (pinned against the sources
//!   that raise them by the loader's own tests);
//! - the booking fallback: [`rustledger_booking::BOOKING_FAILURE_CODE`];
//! - the load errors' codes: the arms of `LoadError::code` (the `E0xxx`
//!   codes and `LOAD`), which every surface reports them with;
//! - the codes written as literals where they are raised: every
//!   `rules.keep("...")` in `check` and every `LedgerError::error("...")` /
//!   `LedgerError::warning("...")` in the loader's processing pipeline
//!   (`E8xxx`, `PLUGIN`).
//!
//! A new code in any of these places fails this test until `explain` gains
//! an explanation for it.

use rustledger::cmd::explain::{Args, known_codes, run_with_writer};
use rustledger_loader::OptionWarning;
use rustledger_parser::{ParseError, Span};
use rustledger_validate::ErrorCode;
use std::collections::BTreeSet;

/// The string literal that starts at `rest` (after optional whitespace), if
/// it looks like a diagnostic code: uppercase letters and digits.
fn leading_code_literal(rest: &str) -> Option<&str> {
    let rest = rest.trim_start().strip_prefix('"')?;
    let end = rest.find('"')?;
    let code = &rest[..end];
    (!code.is_empty()
        && code
            .bytes()
            .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit()))
    .then_some(code)
}

/// Every code literal passed directly to one of `calls` in `source`.
fn literal_codes(source: &str, calls: &[&str]) -> BTreeSet<String> {
    let mut codes = BTreeSet::new();
    for call in calls {
        for (at, _) in source.match_indices(call) {
            if let Some(code) = leading_code_literal(&source[at + call.len()..]) {
                codes.insert(code.to_string());
            }
        }
    }
    codes
}

const CHECK_SOURCE: &str = include_str!("../src/cmd/check.rs");

const PROCESS_SOURCE: &str = include_str!("../../rustledger-loader/src/process.rs");

const LOADER_LIB_SOURCE: &str = include_str!("../../rustledger-loader/src/lib.rs");

/// The codes `LoadError::code` returns: the literals of its match arms.
fn load_error_codes() -> BTreeSet<String> {
    let start = LOADER_LIB_SOURCE
        .find("pub const fn code(&self)")
        .expect("LoadError::code");
    let body = &LOADER_LIB_SOURCE[start..];
    let body = &body[..body.find("\n    }\n").expect("end of LoadError::code")];
    literal_codes(body, &["=> "])
}

/// Every code `check` can emit, from the canonical definitions above.
fn every_emitted_code() -> BTreeSet<String> {
    let mut codes = BTreeSet::new();
    codes.extend(ErrorCode::ALL.iter().map(|ec| ec.code().to_string()));
    codes.extend(
        ParseError::every_kind_sample()
            .into_iter()
            .map(|kind| format!("P{:04}", ParseError::new(kind, Span::new(0, 0)).kind_code())),
    );
    codes.extend(OptionWarning::ALL_CODES.iter().map(ToString::to_string));
    codes.insert(rustledger_booking::BOOKING_FAILURE_CODE.to_string());
    codes.extend(literal_codes(CHECK_SOURCE, &["rules.keep("]));
    codes.extend(load_error_codes());
    codes.extend(literal_codes(
        PROCESS_SOURCE,
        &["LedgerError::error(", "LedgerError::warning("],
    ));
    codes
}

#[test]
fn test_literal_codes_scanner_finds_the_known_sites() {
    // The scan must actually see the sites it exists to watch; a scanner
    // that matched nothing would make the guard below vacuous.
    let load = load_error_codes();
    for code in [
        "E0001", "E0002", "E0003", "E0004", "E0005", "E0006", "E0007", "LOAD",
    ] {
        assert!(
            load.contains(code),
            "{code} not found in LoadError::code: {load:?}"
        );
    }
    let check = literal_codes(CHECK_SOURCE, &["rules.keep("]);
    assert!(check.contains("PLUGIN"), "{check:?}");
    let process = literal_codes(
        PROCESS_SOURCE,
        &["LedgerError::error(", "LedgerError::warning("],
    );
    for code in ["E8001", "E8002", "E8004", "E8005", "PLUGIN"] {
        assert!(
            process.contains(code),
            "{code} not found in process.rs: {process:?}"
        );
    }
}

#[test]
fn test_explain_knows_every_code_check_emits() {
    let known: BTreeSet<&str> = known_codes().into_iter().collect();
    let missing: Vec<String> = every_emitted_code()
        .into_iter()
        .filter(|code| !known.contains(code.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "`rledger explain` has no explanation for {missing:?}; add each to `OTHER` \
         in crates/rustledger/src/cmd/explain.rs (or to ErrorCode's title/explanation)"
    );
}

#[test]
fn test_run_with_writer_explains_every_emitted_code() {
    // Through the command's own lookup, not just the list: each code must
    // resolve and print its heading.
    for code in every_emitted_code() {
        let mut out = Vec::new();
        let status = run_with_writer(
            &Args {
                code: Some(code.clone()),
            },
            &mut out,
        )
        .expect("write to Vec cannot fail");
        let text = String::from_utf8(out).expect("UTF-8");
        assert_eq!(status, 0, "{code}: {text}");
        assert!(text.starts_with(&format!("{code}: ")), "{code}: {text}");
    }
}
