//! Internal helper functions for WASM bindings.

use std::path::Path;
use wasm_bindgen::prelude::*;

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_parser::{ParseResult as ParserResult, parse as parse_beancount};

use crate::types::{Error, LedgerOptions, Severity};
use crate::utils::LineLookup;

/// Convert a parser [`rustledger_parser::ParseError`] into the rich WASM
/// [`Error`]: stable code (`P####`), `phase: "parse"`, hint, and the full
/// source span (start + end line/column).
pub fn parse_error_to_wasm(
    e: &rustledger_parser::ParseError,
    lookup: &LineLookup,
    file: Option<String>,
) -> Error {
    Error::new(e.to_string())
        .with_code(format!("P{:04}", e.kind_code()))
        .with_phase("parse")
        .with_hint(e.hint.clone())
        .with_file(file)
        .with_span(
            lookup.byte_to_line_col(e.span.start),
            lookup.byte_to_line_col(e.span.end),
        )
}

/// Convert a [`rustledger_validate::ValidationError`] into the rich WASM
/// [`Error`]: stable code (`E####`), `phase: "validate"`, hint (the advisory
/// note, else context), and the source span when present. When the error has
/// no span, falls back to `fallback_line` (the directive's date→line) to
/// preserve the prior location behavior.
pub fn validation_error_to_wasm(
    e: &rustledger_validate::ValidationError,
    lookup: &LineLookup,
    file: Option<String>,
    fallback_line: Option<u32>,
) -> Error {
    // Map the validation code's own severity (Info/Warning/Error) to the WASM
    // 2-level severity, so advisory codes (FutureDate, SinglePosting, …) surface
    // as warnings instead of being reported as hard errors — matching `rledger
    // check`'s error/warning split.
    let base = if matches!(e.code.severity(), rustledger_validate::Severity::Error) {
        Error::new(e.message.clone())
    } else {
        Error::warning(e.message.clone())
    };
    let mut out = base
        .with_code(e.code.code())
        .with_phase("validate")
        .with_hint(e.note.clone().or_else(|| e.context.clone()))
        .with_file(file);
    if let Some(span) = e.span {
        out = out.with_span(
            lookup.byte_to_line_col(span.start),
            lookup.byte_to_line_col(span.end),
        );
    } else {
        out.line = fallback_line;
    }
    out
}

/// Result of loading and processing a source file.
pub struct ProcessedLedger {
    pub directives: Vec<Directive>,
    pub options: LedgerOptions,
    pub errors: Vec<Error>,
    /// Raw parse result, needed by editor features and `ParsedLedger`.
    pub parse_result: ParserResult,
    pub lookup: LineLookup,
}

/// Parse, book, and process a Beancount source string.
///
/// This is the common entry point for all processing functions.
/// Uses the shared `process()` pipeline for sorting, booking, and plugins,
/// but skips validation — callers that need it should call `run_validation()`.
pub fn load_and_book(source: &str) -> ProcessedLedger {
    // Keep raw parse result for editor features
    let parse_result = parse_beancount(source);
    let lookup = LineLookup::new(source);

    // If there are parse errors, return early without processing
    if !parse_result.errors.is_empty() {
        let errors: Vec<Error> = parse_result
            .errors
            .iter()
            .map(|e| parse_error_to_wasm(e, &lookup, None))
            .collect();

        let options = extract_options(&parse_result.options);

        return ProcessedLedger {
            directives: Vec::new(),
            options,
            errors,
            parse_result,
            lookup,
        };
    }

    // Use Loader with a single-file VFS to produce a LoadResult
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("input.beancount", source);
    let mut loader = Loader::new().with_filesystem(Box::new(vfs));

    let raw = match loader.load(Path::new("input.beancount")) {
        Ok(raw) => raw,
        Err(e) => {
            let options = extract_options(&parse_result.options);
            return ProcessedLedger {
                directives: Vec::new(),
                options,
                errors: vec![Error::new(format!("Load error: {e}"))],
                parse_result,
                lookup,
            };
        }
    };

    // Extract options before process() consumes raw
    let options = extract_loader_options(&raw.options);

    // Run the shared processing pipeline:
    // sort → synth-plugins → book → regular-plugins → finalize
    // Skip validation here — callers that need it will call run_validation()
    // (the validation pass itself is split into Early — before booking — and
    // Late — after regular plugins; both are invoked when `validate: true`).
    let load_options = LoadOptions {
        validate: false,
        ..Default::default()
    };

    match process(raw, &load_options) {
        Ok(ledger) => {
            let directives = ledger.directives.into_iter().map(|s| s.value).collect();

            let errors: Vec<Error> = ledger.errors.into_iter().map(Error::from).collect();

            ProcessedLedger {
                directives,
                options,
                errors,
                parse_result,
                lookup,
            }
        }
        Err(e) => ProcessedLedger {
            directives: Vec::new(),
            options,
            errors: vec![Error::new(format!("Processing error: {e}"))],
            parse_result,
            lookup,
        },
    }
}

/// Whether any entry is an actual error (`Severity::Error`), as opposed to a
/// warning. Warnings (e.g. the `unrealized` plugin's gain/loss notices) must
/// not abort processing or mark a ledger invalid — matching `rledger check`,
/// which exits 0 on warning-only ledgers.
#[must_use]
pub fn has_fatal(errors: &[Error]) -> bool {
    errors.iter().any(|e| e.severity == Severity::Error)
}

/// Run validation on a loaded ledger and return validation errors.
pub fn run_validation(load: &ProcessedLedger) -> Vec<Error> {
    use rustledger_validate::{ValidationOptions, ValidationSession};

    // Skip validation only when loading produced a genuine *error* (parse or
    // booking failure) — those make the directive stream unsound to validate.
    // A warning must NOT skip validation, or real diagnostics (E1001, balance
    // residuals, …) would be silently dropped for any ledger that also emits a
    // plugin warning.
    if has_fatal(&load.errors) {
        return Vec::new();
    }

    // Build date→line mapping from parse result for error locations
    let mut date_to_line: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
    for spanned in &load.parse_result.directives {
        let line = load.lookup.byte_to_line(spanned.span.start);
        let date = spanned.value.date().to_string();
        date_to_line.entry(date).or_insert(line);
    }

    // WASM target sees already-booked directives, so run both phases
    // back-to-back. Use a hardcoded far-future "today" to disable
    // future-date warnings — WASM has no reliable wall clock and the
    // legacy `validate()` shortcut also didn't fire these warnings
    // unless `warn_future_dates` was explicitly enabled (it isn't here).
    // 2999-12-31 is a valid Gregorian date, so `naive_date` is always `Some`.
    #[allow(clippy::unwrap_used)]
    let today = rustledger_core::naive_date(2999, 12, 31).unwrap();
    let session = ValidationSession::new(ValidationOptions::default());
    let (session, mut errors) = session.run_early(&load.directives, today);
    let (session, late_errs) = session.run_late(&load.directives, today);
    errors.extend(late_errs);
    errors.extend(session.finalize());

    errors
        .iter()
        .map(|err| {
            let fallback_line = date_to_line.get(&err.date.to_string()).copied();
            validation_error_to_wasm(err, &load.lookup, None, fallback_line)
        })
        .collect()
}

/// Serialize a value to `JsValue` using JSON-compatible settings.
///
/// This ensures:
/// - `None` serializes as `null` (not `undefined`)
/// - Maps serialize as plain objects (not ES2015 `Map`)
pub fn to_js<T: serde::Serialize>(value: &T) -> Result<JsValue, JsError> {
    let serializer = serde_wasm_bindgen::Serializer::json_compatible();
    value
        .serialize(&serializer)
        .map_err(|e| JsError::new(&e.to_string()))
}

/// Extract [`LedgerOptions`] from parsed option directives (parser format).
/// Derive the configured [`rustledger_core::AccountTypes`] from raw parsed
/// option tuples (`name_assets` etc. over the standard defaults).
///
/// The wasm wire `LedgerOptions` deliberately carries only title/currencies,
/// so query surfaces must NOT go through it for classification — they take
/// the account types from here (single-file paths) or from the loader's
/// `Options::to_account_types` (multi-file), or `POSSIGN`/`ACCOUNT_SORTKEY`
/// silently misclassify renamed ledgers (the L5 bug class).
pub fn account_types_from_raw(
    options: &[(String, String, rustledger_parser::Span)],
) -> rustledger_core::AccountTypes {
    let mut at = rustledger_core::AccountTypes::default();
    for (key, value, _span) in options {
        match key.as_str() {
            "name_assets" => at.assets.clone_from(value),
            "name_liabilities" => at.liabilities.clone_from(value),
            "name_equity" => at.equity.clone_from(value),
            "name_income" => at.income.clone_from(value),
            "name_expenses" => at.expenses.clone_from(value),
            _ => {}
        }
    }
    at
}

pub fn extract_options(options: &[(String, String, rustledger_parser::Span)]) -> LedgerOptions {
    let mut ledger_options = LedgerOptions::default();

    for (key, value, _span) in options {
        match key.as_str() {
            "title" => ledger_options.title = Some(value.clone()),
            "operating_currency" => {
                ledger_options.operating_currencies.push(value.clone());
            }
            _ => {}
        }
    }

    ledger_options
}

/// Extract [`LedgerOptions`] from loader's [`Options`] struct.
fn extract_loader_options(options: &rustledger_loader::Options) -> LedgerOptions {
    LedgerOptions {
        title: options.title.clone(),
        operating_currencies: options.operating_currency.clone(),
    }
}

#[cfg(test)]
mod warning_severity_tests {
    use super::*;

    #[test]
    fn has_fatal_ignores_warnings() {
        assert!(!has_fatal(&[Error::warning("w".to_string())]));
        assert!(has_fatal(&[Error::new("e")]));
        assert!(has_fatal(&[
            Error::warning("w".to_string()),
            Error::new("e")
        ]));
    }

    /// A plugin warning must NOT cause validation to be skipped — otherwise a
    /// genuine error on a ledger that also warns is silently dropped.
    #[test]
    fn run_validation_not_skipped_by_warning() {
        let src = "plugin \"unrealized\" \"Equity:Unrealized\"\n\
                   2020-01-01 open Assets:Stock\n2020-01-01 open Assets:Cash\n\
                   2020-01-01 open Equity:Unrealized\n\
                   2020-01-02 * \"buy\"\n  Assets:Stock  10 AAPL {100.00 USD}\n  Assets:Cash  -1000.00 USD\n\
                   2020-06-01 price AAPL 150.00 USD\n\
                   2020-07-01 * \"x\"\n  Assets:Cash  -5.00 USD\n  Expenses:NeverOpened  5.00 USD\n";
        let load = load_and_book(src);
        assert!(
            load.errors.iter().any(|e| e.severity == Severity::Warning),
            "expected an unrealized warning in load.errors"
        );
        assert!(!has_fatal(&load.errors), "a warning must not be fatal");
        let validation = run_validation(&load);
        let e = validation
            .iter()
            .find(|e| e.message.contains("NeverOpened"))
            .expect("validation must run despite the warning and report E1001");
        // #1597: validation errors now carry a stable code + phase + location.
        assert_eq!(e.phase.as_deref(), Some("validate"), "phase");
        assert!(
            e.code.as_deref().is_some_and(|c| c.starts_with('E')),
            "expected an E#### code, got {:?}",
            e.code
        );
        assert!(e.line.is_some(), "validation error should carry a line");
    }

    /// #1597: parse errors carry a `P####` code, `phase: "parse"`, and the full
    /// start + end span.
    #[test]
    fn parse_error_carries_rich_fields() {
        // A top-level directive indented past column 0 is a parse error.
        let load = load_and_book("  2020-01-01 open Assets:A\n");
        let e = load
            .errors
            .iter()
            .find(|e| e.phase.as_deref() == Some("parse"))
            .expect("expected a parse-phase error");
        assert!(
            e.code.as_deref().is_some_and(|c| c.starts_with('P')),
            "expected a P#### code, got {:?}",
            e.code
        );
        assert!(
            e.line.is_some() && e.column.is_some(),
            "parse error should have start line+column"
        );
        assert!(
            e.end_line.is_some() && e.end_column.is_some(),
            "parse error should have an end position"
        );
    }

    /// #1597: a validation error's WASM severity now follows its code's own
    /// severity — advisory codes surface as `Warning` (so they don't invalidate
    /// a ledger), real codes as `Error`.
    #[test]
    fn validation_severity_follows_code() {
        use rustledger_validate::{ErrorCode, ValidationError};
        let lookup = LineLookup::new("x");
        let date = rustledger_core::naive_date(2020, 1, 1).unwrap();
        let mk = |code| ValidationError::new(code, "m", date);
        // FutureDate is a warning code; AccountNotOpen (E1001) is an error.
        let warn = validation_error_to_wasm(&mk(ErrorCode::FutureDate), &lookup, None, Some(1));
        assert_eq!(warn.severity, Severity::Warning);
        let err = validation_error_to_wasm(&mk(ErrorCode::AccountNotOpen), &lookup, None, Some(1));
        assert_eq!(err.severity, Severity::Error);
    }
}

#[cfg(test)]
mod account_types_tests {
    use super::account_types_from_raw;

    #[test]
    fn raw_options_override_defaults() {
        let span = rustledger_parser::Span::ZERO;
        let opts = vec![
            ("name_income".to_string(), "Revenue".to_string(), span),
            ("title".to_string(), "x".to_string(), span),
        ];
        let at = account_types_from_raw(&opts);
        assert_eq!(at.income, "Revenue");
        assert_eq!(at.assets, "Assets"); // untouched types keep defaults
        assert!(at.is_credit_normal("Revenue:Sales"));
        assert!(!at.is_credit_normal("Income:Sales")); // renamed away
    }
}
