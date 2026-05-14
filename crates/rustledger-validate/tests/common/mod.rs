//! Shared test helpers for the validate crate's integration tests.
//!
//! The `rustledger-validate` crate used to expose `validate()`,
//! `validate_with_options()`, etc. as free-function shortcuts. They
//! were removed in favor of [`ValidationSession`] (see PR #1116). These
//! helpers preserve the old single-call shape for test code that
//! doesn't need to interleave booking between phases — they just
//! chain Early + Late + finalize through a fresh session.
//!
//! Integration test files include this module via `mod common;` and
//! import the helpers they need.

#![allow(dead_code)]

use rustledger_core::{Directive, NaiveDate};
use rustledger_parser::Spanned;
use rustledger_validate::{Phase, ValidationError, ValidationOptions, ValidationSession};

/// Default "today" for tests that don't otherwise care. Set in the
/// future relative to most fixtures so the future-date warning
/// doesn't fire unexpectedly.
///
/// Convention across the workspace:
/// - Tests / benches with fixtures: `2030-01-01` (mid-future anchor)
/// - WASM (no wall clock available): `2999-12-31` (far-future anchor)
/// - LSP / FFI / production: `jiff::Zoned::now().date()`
pub fn test_today() -> NaiveDate {
    rustledger_core::naive_date(2030, 1, 1).unwrap()
}

/// Wrapper that mirrors the deleted public `validate()` shortcut.
pub fn validate(directives: &[Directive]) -> Vec<ValidationError> {
    validate_with_options(directives, ValidationOptions::default())
}

/// Wrapper that mirrors the deleted public `validate_with_options()`.
pub fn validate_with_options(
    directives: &[Directive],
    options: ValidationOptions,
) -> Vec<ValidationError> {
    validate_with_today(directives, options, test_today())
}

/// Wrapper that mirrors the deleted public `validate_with_today()`.
pub fn validate_with_today(
    directives: &[Directive],
    options: ValidationOptions,
    today: NaiveDate,
) -> Vec<ValidationError> {
    let mut session = ValidationSession::new(options);
    let mut errors = session.run_phase(directives, Phase::Early, today);
    errors.extend(session.run_phase(directives, Phase::Late, today));
    errors.extend(session.finalize());
    errors
}

/// Wrapper that mirrors the deleted public `validate_spanned_with_options()`.
pub fn validate_spanned_with_options(
    directives: &[Spanned<Directive>],
    options: ValidationOptions,
) -> Vec<ValidationError> {
    let mut session = ValidationSession::new(options);
    let mut errors = session.run_phase_spanned(directives, Phase::Early, test_today());
    errors.extend(session.run_phase_spanned(directives, Phase::Late, test_today()));
    errors.extend(session.finalize());
    errors
}
