//! Internal helper functions for WASM bindings.

use std::path::Path;
use wasm_bindgen::prelude::*;

use rustledger_core::Directive;
use rustledger_loader::{LoadError, LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_parser::{ParseResult as ParserResult, parse as parse_beancount};

use crate::types::{Error, LedgerOptions, Severity};
use crate::utils::LineLookup;

/// Convert a parser [`rustledger_parser::ParseError`] into the rich WASM
/// [`Error`]: stable code (`P####`), `phase: "parse"`, hint, and the full
/// source span (start + end line/column).
///
/// Located through the loader's [`rustledger_loader::LineIndex`], so the
/// columns count characters as `rledger check` counts them; they counted
/// bytes, and read high after a BOM or a multi-byte character (#2946).
pub fn parse_error_to_wasm(
    e: &rustledger_parser::ParseError,
    index: &rustledger_loader::LineIndex<'_>,
    file: Option<String>,
) -> Error {
    parse_error_fields(e).with_file(file).with_span(
        line_col_u32(index.line_col(e.span.start)),
        line_col_u32(index.line_col(e.span.end)),
    )
}

/// A parse error's message, code (`P` and its four-digit kind code), phase
/// (`parse`) and hint, unlocated: WASM's one mapping of them, which
/// [`parse_error_to_wasm`] and the multi-file
/// [`crate::api::load_errors_to_errors`] both build on.
///
/// A deliberate copy of the loader's
/// [`rustledger_loader::parse_errors_to_ledger_errors`] (behind the FFI),
/// not a call to it: that gives a `LedgerError`, which has no end position,
/// and wants a `LoadError` and its `SourceMap`, which the single-source
/// surfaces (`parse`, `format`, `validateSource`) never build. That function
/// points back here, and `parse_error_mapping_parity` below pins the two to
/// agree on message, code, phase, hint, file, line and column. Revisit if
/// `LedgerError` gains an end position, at which point WASM should map from
/// it.
pub fn parse_error_fields(e: &rustledger_parser::ParseError) -> Error {
    Error::new(e.message())
        .with_code(format!("P{:04}", e.kind_code()))
        .with_phase("parse")
        .with_hint(e.hint.clone())
}

/// Every parse error of `source` as [`parse_error_to_wasm`] reports it. The
/// line index is built only when there is an error to locate.
pub fn parse_errors_to_wasm<'e>(
    errors: impl IntoIterator<Item = &'e rustledger_parser::ParseError>,
    source: &str,
) -> Vec<Error> {
    let mut index = None;
    errors
        .into_iter()
        .map(|e| {
            let index = index.get_or_insert_with(|| rustledger_loader::LineIndex::new(source));
            parse_error_to_wasm(e, index, None)
        })
        .collect()
}

/// A loader `(line, column)` as the WASM `Error`'s `u32`s.
fn line_col_u32((line, column): (usize, usize)) -> (u32, u32) {
    (
        u32::try_from(line).unwrap_or(u32::MAX),
        u32::try_from(column).unwrap_or(u32::MAX),
    )
}

/// Convert a [`rustledger_validate::ValidationError`] into the rich WASM
/// [`Error`]: stable code (`E####`), `phase: "validate"`, hint (the advisory
/// note, else context), and the source span when present. When the error has
/// no span, falls back to `fallback_line` (the directive's date→line) to
/// preserve the prior location behavior.
///
/// The span is located in `source_map` (the load's, holding the source as
/// file 0) through the loader's canonical, [`rustledger_loader::SourceMap::locate`],
/// so the line and column are the ones `rledger check` and the FFI report;
/// the column counted bytes before (#2946).
pub fn validation_error_to_wasm(
    e: &rustledger_validate::ValidationError,
    source_map: &rustledger_loader::SourceMap,
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
        .with_hint(
            e.hint
                .clone()
                .or_else(|| e.note.clone())
                .or_else(|| e.context.clone()),
        )
        .with_file(file);
    // A span is a place in the one source text (file id 0) only; one a
    // plugin's directive carries (a placeholder id) says nothing about it.
    // The FFI component's `semantic_validation_errors`
    // (`rustledger-ffi-component/src/convert.rs`) applies the same file-id
    // rule and points back here; change both together (#2935). The location
    // is not a copy: both read it from `SourceMap::locate`.
    let located = e
        .span
        .filter(|_| e.file_id.is_none_or(|id| id == 0))
        .and_then(|span| {
            Some((
                source_map.locate(0, span.start)?,
                source_map.locate(0, span.end)?,
            ))
        });
    if let Some((start, end)) = located {
        out = out.with_span(
            line_col_u32((start.line, start.column)),
            line_col_u32((end.line, end.column)),
        );
    } else {
        out.line = fallback_line;
    }
    out
}

/// Result of loading and processing a source file.
pub struct ProcessedLedger {
    pub directives: Vec<Directive>,
    /// Each directive's span and file id, in `directives` order, so a query
    /// can resolve the `filename` / `lineno` / `location` columns (#2825).
    pub directive_spans: Vec<DirectiveSpan>,
    /// The loader's source map: the text, named `<string>`, and the
    /// placeholder locations plugins gave the directives they created, so a
    /// query resolves both (#2825). Empty when the source did not load.
    pub source_map: rustledger_loader::SourceMap,
    /// The transactions booking refused, as indices into `directives`
    /// ([`rustledger_loader::Ledger::booking_refused`]): [`run_validation`]
    /// sets them aside as the validating loader does. Empty when the source
    /// did not load.
    pub booking_refused: Vec<usize>,
    pub options: LedgerOptions,
    pub errors: Vec<Error>,
    /// Option diagnostics (E7001, E7002, E7003, E7009, ...), kept apart from
    /// `errors` on purpose.
    ///
    /// `errors` is what [`has_fatal`] gates on: whether a surface may work
    /// with the directive stream, and whether a ledger is valid. An invalid
    /// option is reported but does not make the directives unsound, so it is
    /// kept out of that gate. ([`run_validation`] no longer gates on `errors`
    /// at all: it validates whatever loaded, as `rledger check` does, #2937.)
    /// Surfaces that *report* diagnostics merge this in; surfaces that gate on
    /// soundness do not.
    pub option_errors: Vec<Error>,
    /// The option diagnostics a query lists
    /// ([`rustledger_loader::Ledger::query_option_errors`], the rule every
    /// query surface shares with the FFI's): `option_errors` with a rejected
    /// `booking_method`'s E7002 replaced by the refusal that says why the
    /// query does not answer (#2911, #2929). `option_errors` itself where the
    /// source did not load (a load or processing failure; a parse error no
    /// longer stops the load, #2949), as no option refuses then.
    pub query_option_errors: Vec<Error>,
    /// Whether a query over the source refuses: it failed to parse, a
    /// transaction failed to book
    /// ([`rustledger_loader::LedgerError::blocks_queries`], the rule the
    /// file-based query surfaces share, #2861, #2882), or it did not load at
    /// all. Every other load error, a plugin's or an unresolved include's, is
    /// reported beside the rows. This is the query rule, not the soundness
    /// gate [`has_fatal`] reads, which also stops on a plugin's error.
    pub query_blocked: bool,
    /// Raw parse result, needed by editor features and `ParsedLedger`.
    pub parse_result: ParserResult,
    pub lookup: LineLookup,
}

impl ProcessedLedger {
    /// Everything a caller should be shown: load diagnostics plus option
    /// diagnostics.
    ///
    /// Every surface that *reports* goes through here, and every surface that
    /// *gates on soundness* reads [`ProcessedLedger::errors`] directly. Keeping
    /// those two questions apart is the whole point of the split — see the
    /// `option_errors` field docs for what folding them together breaks.
    ///
    /// It is a method rather than something each entry point assembles because
    /// the alternative is what #2299 was: one surface deciding what a caller
    /// sees while the next one decides differently. `query`, `expandPads`, and
    /// `applyPlugin` each already carry non-fatal load warnings through every
    /// result path; a second diagnostics channel they did not know to carry
    /// would have left them silent on options while `validateSource` reported.
    #[must_use]
    pub fn reported_errors(&self) -> Vec<Error> {
        let mut all = self.errors.clone();
        all.extend(self.option_errors.iter().cloned());
        all
    }

    /// What a query over the source lists: load diagnostics plus option
    /// diagnostics as a query lists them ([`Self::query_option_errors`]), so a
    /// rejected `booking_method`'s E7002 is the refusal that says why the
    /// query does not answer, as the FFI's query surfaces list it (#2929).
    /// [`Self::reported_errors`] for every surface that reports the load.
    #[must_use]
    pub fn reported_query_errors(&self) -> Vec<Error> {
        let mut all = self.errors.clone();
        all.extend(self.query_option_errors.iter().cloned());
        all
    }
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

    // A parse error does not stop the load: the loader keeps every entry that
    // did parse, and `process` books them (and `run_validation` validates
    // them), as `rledger check` and bean-check do (#2949). This used to return
    // here with no directives, so one syntax error hid every other finding.

    // Use Loader with a single-file VFS to produce a LoadResult
    let mut vfs = VirtualFileSystem::new();
    // Named `<string>`, as beancount's `load_string` names an in-memory
    // source: the name a query's `filename` column reports (#2825).
    vfs.add_file("<string>", source);
    let mut loader = Loader::new().with_filesystem(Box::new(vfs));

    let mut raw = match loader.load(Path::new("<string>")) {
        Ok(raw) => raw,
        Err(e) => {
            let options = extract_options(&parse_result.options);
            let option_errors = validate_option_tuples(&parse_result.options, &lookup);
            return ProcessedLedger {
                directives: Vec::new(),
                directive_spans: Vec::new(),
                source_map: rustledger_loader::SourceMap::new(),
                booking_refused: Vec::new(),
                options,
                errors: vec![Error::new(format!("Load error: {e}"))],
                query_option_errors: option_errors.clone(),
                option_errors,
                query_blocked: true,
                parse_result,
                lookup,
            };
        }
    };

    // Extract options before process() consumes raw
    let options = extract_loader_options(&raw.options);
    // Same, for the warnings `Options::set` raised while building them. The
    // loader ran, so these already exist — the single-source path used to drop
    // them on the floor here, which is why E7001/E7002 were invisible on every
    // entry point built on this function (#2299).
    let option_errors = without_files(option_warnings_to_errors(&raw.options.warnings));

    // The parse errors, reported one by one with their code, line and span
    // (`parse_errors_to_wasm`, so at character columns), and kept out of `process`
    // (`LoadResult::take_parse_errors`).
    let parse_failures = raw.take_parse_errors();
    let parse_blocks_queries = parse_failures.iter().any(LoadError::blocks_queries);
    let parse_errors = parse_errors_to_wasm(
        parse_failures.iter().flat_map(|e| match e {
            LoadError::ParseErrors { errors, .. } => errors.as_slice(),
            _ => &[],
        }),
        source,
    );

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
            // The whole query rule (`Ledger::blocks_queries`), read before the
            // fields move out: a blocking error, or a rejected
            // `booking_method` (#2911), whose E7002 is in `option_errors`.
            let query_blocked = parse_blocks_queries || ledger.blocks_queries();
            // The option diagnostics as a query lists them, through the
            // canonical (`Ledger::query_option_errors`), as the FFI lists them:
            // the rejected `booking_method`'s E7002 is the refusal.
            let query_option_errors = without_files(
                ledger
                    .query_option_errors()
                    .into_iter()
                    .map(Error::from)
                    .collect(),
            );
            let booking_refused = ledger.booking_refused;
            let source_map = ledger.source_map;
            let (directives, directive_spans) = ledger
                .directives
                .into_iter()
                .map(|s| (s.value, (s.span, s.file_id)))
                .unzip();

            let mut errors = parse_errors;
            errors.extend(ledger.errors.into_iter().map(Error::from));

            ProcessedLedger {
                directives,
                directive_spans,
                source_map,
                booking_refused,
                options,
                errors,
                option_errors,
                query_option_errors,
                query_blocked,
                parse_result,
                lookup,
            }
        }
        Err(e) => {
            let mut errors = parse_errors;
            errors.push(Error::new(format!("Processing error: {e}")));
            ProcessedLedger {
                directives: Vec::new(),
                directive_spans: Vec::new(),
                source_map: rustledger_loader::SourceMap::new(),
                booking_refused: Vec::new(),
                options,
                errors,
                query_option_errors: option_errors.clone(),
                option_errors,
                query_blocked: true,
                parse_result,
                lookup,
            }
        }
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

/// A validating load's errors as WASM [`Error`]s, leaving out the
/// advisory-only ones ([`rustledger_validate::is_advisory_only_code`]: E1004,
/// closing an account with a balance), which `rledger check` and bean-check
/// do not report either; `rledger lint closed-nonempty` does (#2937). For the
/// surfaces that validate through the loader (`validateMultiFile`,
/// `validateWithHost`, `Ledger.fromFiles`); [`run_validation`] leaves them out
/// the same way.
pub fn reported_ledger_errors(errors: Vec<rustledger_loader::LedgerError>) -> Vec<Error> {
    errors
        .into_iter()
        .filter(|e| !rustledger_validate::is_advisory_only_code(&e.code))
        .map(Error::from)
        .collect()
}

/// Run validation on a loaded ledger and return validation errors.
///
/// Which errors stop validation is `rledger check`'s rule, the validating
/// loader's: none do. A transaction booking refused is set aside
/// ([`rustledger_loader::Ledger::booking_refused`]): Early sees it as written
/// and Late does not, and the session reports the account errors Early held
/// for it, as `process` does. This used to return nothing on any
/// severity-error in `load.errors`, so a STRICT ledger with an ambiguous
/// reduction reported its booking error and not the `Balance failed` that
/// follows it, which `check` and bean-check both report (#2937). A parse
/// error does not stop it either: the entries that parsed are validated, as
/// `check` and bean-check validate them (#2949). A source that failed to load
/// at all has no directives here, so nothing is validated for it.
///
/// Advisory-only diagnostics
/// ([`rustledger_validate::ErrorCode::is_advisory_only`]: E1004, closing an
/// account with a balance) are left out, as `check` and bean-check leave them
/// out; `rledger lint closed-nonempty` reports them (#2937).
pub fn run_validation(load: &ProcessedLedger) -> Vec<Error> {
    use rustledger_validate::ValidationSession;

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
    // The options `rledger check` validates with, from the ledger's own
    // (the canonical `validation_options_from_options`): a default set
    // ignored `tolerance_multiplier`, so a balance a pad left within the
    // ledger's tolerance was reported as one `check` passes (#2901). And the
    // source map's positions, for beancount's entry order.
    let session = ValidationSession::new(
        rustledger_loader::validation_options_from_options(&options_from_raw(
            &load.parse_result.options,
        ))
        .with_source_lines(rustledger_loader::source_lines(&load.source_map)),
    );
    // With the kept spans, as `rledger check` and the FFI validate: the pad
    // rule reads them as beancount's line order, so an "Attempt to pad an
    // entry with cost" lists tied positions as they do (#2901).
    let refused = |index: &usize| load.booking_refused.binary_search(index).is_ok();
    // `load_and_book` keeps one span per directive (it unzips them from the
    // loader's stream), so the spans always line up; the refused indices are
    // positions in that same stream, and a refused transaction is noted by its
    // span, so a stream without them could not be validated as `check` does.
    debug_assert_eq!(
        load.directive_spans.len(),
        load.directives.len(),
        "load_and_book keeps one span per directive"
    );
    let spanned = spanned_directives(&load.directives, &load.directive_spans);
    let (mut session, mut errors) = session.run_early_spanned(&spanned, today);
    let mut booked = Vec::with_capacity(spanned.len());
    for (index, directive) in spanned.into_iter().enumerate() {
        if refused(&index) {
            session.note_refused_by_booking(&directive);
        } else {
            booked.push(directive);
        }
    }
    let (session, late_errs) = session.run_late_spanned(&booked, today);
    errors.extend(late_errs);
    errors.extend(session.finalize());

    errors
        .iter()
        .filter(|err| !err.code.is_advisory_only())
        .map(|err| {
            let fallback_line = date_to_line.get(&err.date.to_string()).copied();
            validation_error_to_wasm(err, &load.source_map, None, fallback_line)
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
/// Read through the loader's [`rustledger_loader::Options`], like
/// [`booking_method_from_raw`], so a rename the loader rejects (E7008) is not
/// applied here either. This used to copy each raw `name_*` value in, so an
/// invalid root the loader kept at its default still renamed the root on this
/// surface (#2911).
///
/// The wasm wire `LedgerOptions` deliberately carries only title/currencies,
/// so query surfaces must NOT go through it for classification — they take
/// the account types from here (single-file paths) or from the loader's
/// `Options::to_account_types` (multi-file), or `POSSIGN`/`ACCOUNT_SORTKEY`
/// silently misclassify renamed ledgers (the L5 bug class).
pub fn account_types_from_raw(
    options: &[(String, String, rustledger_parser::Span)],
) -> rustledger_core::AccountTypes {
    options_from_raw(options).to_account_types()
}

/// Option warnings as WASM [`Error`]s, through the loader's canonical
/// [`rustledger_loader::option_warnings_to_errors`] and the
/// `From<LedgerError>` every other loader error takes.
///
/// Nothing about an option diagnostic is decided here: severity, code,
/// phase, message and location all come from the loader's mapping, which
/// `rledger check` and the LSP read too (#2291, #2297, #2298, #2299, #2925;
/// the history is on the loader function).
///
/// The location is a point, as on every `LedgerError`-derived error: `file`,
/// `line` and `column` (1) are set when the option has a site, and
/// `end_line` / `end_column` are null. A multi-file ledger names the file
/// each option is in, an included one among them; the single-source entry
/// points drop it with [`without_files`], as their other errors carry none
/// (see [`Error::file`]).
///
/// [`OptionWarning`]: rustledger_loader::OptionWarning
pub fn option_warnings_to_errors(warnings: &[rustledger_loader::OptionWarning]) -> Vec<Error> {
    rustledger_loader::option_warnings_to_errors(warnings)
        .into_iter()
        .map(Error::from)
        .collect()
}

/// `errors` with no `file`, for the single-source entry points, whose errors
/// name no file (the source is `<string>`); the line stays.
pub fn without_files(errors: Vec<Error>) -> Vec<Error> {
    errors.into_iter().map(|e| e.with_file(None)).collect()
}

/// Validate raw parsed `option` tuples and return the resulting diagnostics.
///
/// For entry points that never build a loader [`Options`] — `parse()`, and the
/// early-return paths of [`load_and_book`] where loading did not get far enough
/// to produce one. Running the keys and values through [`Options::set`] is what
/// raises E7001/E7002, and it is cheap: no file IO, no booking, no plugins, so
/// a syntax-only entry point stays syntax-only in cost.
///
/// [`Options`]: rustledger_loader::Options
/// [`Options::set`]: rustledger_loader::Options::set
pub fn validate_option_tuples(
    options: &[(String, String, rustledger_parser::Span)],
    lookup: &LineLookup,
) -> Vec<Error> {
    let mut opts = rustledger_loader::Options::new();
    for (key, value, span) in options {
        // Each option's line, as the loader gives it; the file is not named
        // on these single-source entry points.
        let site = rustledger_loader::OptionSite {
            file: String::new(),
            line: lookup.byte_to_line(span.start) as usize,
        };
        opts.set_scoped_at(key, value, true, Some(site));
    }
    // E7010, which needs every option set first, as the loader raises it.
    let rooted = opts.rooted_leaf_warnings();
    opts.warnings.extend(rooted);
    without_files(option_warnings_to_errors(&opts.warnings))
}

/// The effective booking method of a single-source ledger, read from its raw
/// option tuples: `option "booking_method"` when set, else STRICT (the
/// `LoadOptions` default every wasm entry point books with).
///
/// For entry points that keep the parse result but not the loader's
/// `Ledger::booking_method` (`ParsedLedger`, including `fromCache`). Going
/// through [`rustledger_loader::Options`] rather than matching the key here
/// keeps the parse and last-wins rules the loader's, so a query realizes with
/// the method the ledger was booked with (#2386).
pub fn booking_method_from_raw(
    options: &[(String, String, rustledger_parser::Span)],
) -> rustledger_core::BookingMethod {
    options_from_raw(options).effective_booking_method(LoadOptions::default().booking_method)
}

/// The `account_previous_*` accounts a single-source ledger's raw option
/// tuples name, which `FROM ... OPEN ON` summarizes into (#2401). Read through
/// the loader's [`rustledger_loader::Options`], like [`booking_method_from_raw`].
pub fn summary_accounts_from_raw(
    options: &[(String, String, rustledger_parser::Span)],
) -> rustledger_query::executor::SummaryAccounts {
    rustledger_query::executor::SummaryAccounts::from_options(&options_from_raw(options))
}

/// The `tolerance_multiplier` a single-source ledger's raw option tuples
/// set, which the padding a query inserts measures a balance's tolerance with
/// (#2901). Read through the loader's [`rustledger_loader::Options`], like
/// [`booking_method_from_raw`].
pub fn tolerance_multiplier_from_raw(
    options: &[(String, String, rustledger_parser::Span)],
) -> rustledger_core::Decimal {
    options_from_raw(options).inferred_tolerance_multiplier
}

/// The loader's [`rustledger_loader::Options`] for raw option tuples, applied
/// in order through [`rustledger_loader::Options::set`] so its parse and
/// last-wins rules hold.
fn options_from_raw(
    options: &[(String, String, rustledger_parser::Span)],
) -> rustledger_loader::Options {
    let mut opts = rustledger_loader::Options::new();
    for (key, value, _span) in options {
        opts.set(key, value);
    }
    opts
}

/// [`LedgerOptions`] for raw parsed option tuples, read through the loader's
/// [`rustledger_loader::Options`] like every other raw-option reader here, so
/// no surface reads an option value the loader would treat differently
/// (#2911).
pub fn extract_options(options: &[(String, String, rustledger_parser::Span)]) -> LedgerOptions {
    extract_loader_options(&options_from_raw(options))
}

/// Extract [`LedgerOptions`] from loader's [`rustledger_loader::Options`] struct.
fn extract_loader_options(options: &rustledger_loader::Options) -> LedgerOptions {
    LedgerOptions {
        title: options.title.clone(),
        operating_currencies: options.operating_currency.clone(),
    }
}

/// A directive's span and file id, kept beside the plain directive so a
/// query can resolve its source columns (#2825).
pub type DirectiveSpan = (rustledger_core::Span, u16);

/// Pair `directives` with their kept spans for a query; see
/// [`rustledger_query::executor::spanned_from_parts`].
#[must_use]
pub fn spanned_directives(
    directives: &[Directive],
    spans: &[DirectiveSpan],
) -> Vec<rustledger_core::Spanned<Directive>> {
    rustledger_query::executor::spanned_from_parts(directives, spans)
}

/// The pad expansion every WASM surface answers with: `directives` padded
/// with each one's place in beancount's entry order
/// ([`rustledger_booking::process_pads_at`]), so an "Attempt to pad an entry
/// with cost" lists tied positions in the order the validation does
/// (#2901). `positions` runs parallel to `directives`: [`source_positions`]
/// of the kept spans, or a restored ledger's kept positions. A ledger
/// restored from a cache that kept none pads by its stream order.
#[must_use]
pub fn pad_expansion(
    directives: &[Directive],
    positions: &[rustledger_booking::SourcePosition],
    tolerance_multiplier: rustledger_core::Decimal,
) -> rustledger_booking::PadResult {
    if positions.len() == directives.len() {
        rustledger_booking::process_pads_at(directives, positions, tolerance_multiplier)
    } else {
        rustledger_booking::process_pads(directives, tolerance_multiplier)
    }
}

/// The positions [`pad_expansion`] reads, from the kept spans and the
/// source map they index, as the validation reads them
/// ([`rustledger_loader::source_lines`]): a source directive's line and
/// file, and a plugin's directive at the line the plugin gave it.
#[must_use]
pub fn source_positions(
    spans: &[DirectiveSpan],
    source_map: &rustledger_loader::SourceMap,
) -> Vec<rustledger_booking::SourcePosition> {
    let lines = rustledger_loader::source_lines(source_map);
    spans
        .iter()
        .map(|(span, file_id)| lines.position(*file_id, span.start))
        .collect()
}

/// The source map a query over an unnamed in-memory source reads its source
/// columns from: the one text, named `<string>` as beancount's `load_string`
/// names it (#2825). File id 0, the id the source's directives carry.
#[must_use]
pub fn string_source_map(source: &str) -> rustledger_loader::SourceMap {
    let mut map = rustledger_loader::SourceMap::new();
    map.add_file(Path::new("<string>").to_path_buf(), source.into());
    map
}

/// `source_map`'s placeholder locations (name, line), in id order: the
/// locations of directives a plugin created, such as `<auto_accounts>`, 0.
/// [`restore_placeholders`] gives each the same id again, so a cached
/// ledger's spans still resolve (#2825).
#[must_use]
pub fn placeholder_locations(source_map: &rustledger_loader::SourceMap) -> Vec<(String, u32)> {
    (rustledger_parser::FIRST_PLACEHOLDER_FILE_ID..rustledger_parser::SYNTHESIZED_FILE_ID)
        .map_while(|id| source_map.placeholder(id))
        .map(|(name, line)| (name.display().to_string(), line))
        .collect()
}

/// Register `locations` (from [`placeholder_locations`]) in a map that has
/// none yet, so each gets the id it had.
pub fn restore_placeholders(
    source_map: &rustledger_loader::SourceMap,
    locations: &[(String, u32)],
) {
    for (name, line) in locations {
        source_map.placeholder_file_id(Path::new(name), *line);
    }
}

/// The context of a query over a source that was loaded WITHOUT validation:
/// `#balances.discrepancy` is computed from `source_map` only when a query
/// reads it, and kept in `memo` (#2823; see
/// [`rustledger_query::executor::BalanceDiscrepancies::recomputed_from`]).
#[must_use]
pub fn lazy_query_context<'a>(
    source_map: &'a rustledger_loader::SourceMap,
    memo: &'a std::sync::OnceLock<Vec<rustledger_loader::BalanceDiscrepancy>>,
    account_types: rustledger_core::AccountTypes,
    booking_method: rustledger_core::BookingMethod,
    summary_accounts: rustledger_query::executor::SummaryAccounts,
) -> rustledger_query::executor::LedgerContext<'a> {
    rustledger_query::executor::LedgerContext {
        account_types,
        booking_method,
        summary_accounts,
        balance_discrepancies: rustledger_query::executor::BalanceDiscrepancies::recomputed_from(
            source_map,
            LoadOptions::default(),
            memo,
        ),
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
        let map = rustledger_loader::SourceMap::new();
        let date = rustledger_core::naive_date(2020, 1, 1).unwrap();
        let mk = |code| ValidationError::new(code, "m", date);
        // FutureDate is a warning code; AccountNotOpen (E1001) is an error.
        let warn = validation_error_to_wasm(&mk(ErrorCode::FutureDate), &map, None, Some(1));
        assert_eq!(warn.severity, Severity::Warning);
        let err = validation_error_to_wasm(&mk(ErrorCode::AccountNotOpen), &map, None, Some(1));
        assert_eq!(err.severity, Severity::Error);
    }

    /// #2946: a validation finding and a parse error are at their CHARACTER
    /// columns, as `rledger check` reports them: a BOM (three bytes) and an
    /// `Ü` (two) each count once. They counted bytes (4 and 27).
    #[test]
    fn test_error_columns_count_characters() {
        let load =
            load_and_book("\u{FEFF}2024-01-02 balance Assets:X 1 USD\n2024-01-01 open Assets:Y\n");
        let mut got: Vec<_> = run_validation(&load)
            .into_iter()
            .map(|e| (e.code, e.line, e.column))
            .collect();
        got.sort();
        assert_eq!(
            got,
            [
                (Some("E1001".to_string()), Some(1), Some(2)),
                (Some("E2001".to_string()), Some(1), Some(2)),
            ]
        );

        let load = load_and_book("2024-01-03 open Assets:Ü 10\n");
        let got: Vec<_> = load.errors.iter().map(|e| (e.line, e.column)).collect();
        assert_eq!(got, [(Some(1), Some(26))]);
    }

    /// The end of a parse error's and of a finding's span is where the span
    /// really ends, counted in characters, not a copy of its start.
    #[test]
    fn test_error_end_positions_are_where_the_span_ends() {
        let load =
            load_and_book("\u{FEFF}2024-01-02 balance Assets:X 1 USD\n2024-01-01 open Assets:Y\n");
        let mut got: Vec<_> = run_validation(&load)
            .into_iter()
            .map(|e| (e.code, e.line, e.column, e.end_line, e.end_column))
            .collect();
        got.sort();
        // The finding is the balance directive: its span runs to the start of
        // the next line, past its newline.
        assert_eq!(
            got,
            [
                (
                    Some("E1001".to_string()),
                    Some(1),
                    Some(2),
                    Some(2),
                    Some(1)
                ),
                (
                    Some("E2001".to_string()),
                    Some(1),
                    Some(2),
                    Some(2),
                    Some(1)
                ),
            ]
        );

        let load = load_and_book("2024-01-03 open Assets:Ü 10\n");
        let got: Vec<_> = load
            .errors
            .iter()
            .map(|e| (e.line, e.column, e.end_line, e.end_column))
            .collect();
        // The unexpected `10`, up to just past it: column 28 in characters,
        // 29 in bytes.
        assert_eq!(got, [(Some(1), Some(26), Some(1), Some(28))]);
    }

    /// A finding on a plugin's directive (a placeholder file id) is not
    /// placed in the source text: its span says nothing about it. The FFI's
    /// `test_a_plugin_directives_finding_maps_to_no_source_line`
    /// (`rustledger-ffi-component/src/convert.rs`) pins the same rule there.
    #[test]
    fn test_a_plugin_directives_finding_maps_to_no_source_line() {
        const SOURCE: &str = "plugin \"beancount.plugins.check_closing\"\n\
             2024-01-01 open Assets:A\n\
             2024-01-01 open Income:X\n\
             2024-01-02 * \"x\"\n  Assets:A  10 USD\n    closing: TRUE\n  Income:X\n";
        let load = load_and_book(SOURCE);
        let errors = run_validation(&load);
        let balance = errors
            .iter()
            .find(|e| e.message.starts_with("Balance failed for Assets:A"))
            .unwrap_or_else(|| panic!("check_closing's balance fails: {errors:?}"));
        assert_eq!(
            (
                balance.line,
                balance.column,
                balance.end_line,
                balance.file.as_deref()
            ),
            (None, None, None, None),
            "{balance:?}"
        );
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

    /// #2911: a root the loader rejects is not applied here either; the
    /// root keeps its earlier valid value, as in the loader and beancount.
    #[test]
    fn test_account_types_from_raw_rejected_root_keeps_earlier_value() {
        let span = rustledger_parser::Span::ZERO;
        let opts = vec![
            ("name_income".to_string(), "Revenue".to_string(), span),
            ("name_income".to_string(), "bad".to_string(), span),
            ("name_equity".to_string(), "Cap ital".to_string(), span),
        ];
        let at = account_types_from_raw(&opts);
        assert_eq!(at.income, "Revenue");
        assert_eq!(at.equity, "Equity");
    }
}

#[cfg(test)]
mod option_diagnostic_tests {
    use super::*;

    /// An invalid option, plus a posting to an account that was never opened.
    /// The second is a genuine validation error, and it is what proves the
    /// first does not suppress it.
    const BAD_OPTION_AND_BAD_ACCOUNT: &str = "option \"nonsense_option\" \"x\"\n\
2024-01-01 open Assets:Cash USD\n\
2024-01-02 * \"p\"\n  Assets:Cash 1 USD\n  Assets:NeverOpened -1 USD\n";

    const BAD_OPTION: &str = "option \"nonsense_option\" \"x\"\n\
2024-01-01 open Assets:Cash USD\n";

    fn codes(errors: &[Error]) -> Vec<&str> {
        errors.iter().filter_map(|e| e.code.as_deref()).collect()
    }

    /// The bug: the loader raised E7001 and `load_and_book` dropped it, so
    /// every single-source entry point built on it reported a clean ledger
    /// where `rledger check` errors and exits 1 (#2299).
    #[test]
    fn load_and_book_surfaces_the_option_error_the_loader_raised() {
        let load = load_and_book(BAD_OPTION);
        assert!(
            codes(&load.option_errors).contains(&"E7001"),
            "E7001 must reach the caller, got {:?}",
            load.option_errors
        );
    }

    /// An invalid option must not cost the ledger its real validation errors,
    /// the drop #2292 fixed for plugin warnings. `run_validation` used to skip
    /// on any error in `load.errors`; it no longer gates on them (#2937), and
    /// this pins that the option error does not suppress validation either way.
    #[test]
    fn an_invalid_option_does_not_suppress_validation() {
        let load = load_and_book(BAD_OPTION_AND_BAD_ACCOUNT);
        assert!(
            codes(&load.option_errors).contains(&"E7001"),
            "precondition: the option error is reported"
        );
        assert!(
            !run_validation(&load).is_empty(),
            "the undefined-account error must still be found; an invalid \
             option does not make the directive stream unsound"
        );
    }

    /// `parse()` never builds a loader `Options`, so it needs its own call to
    /// `Options::set` rather than warnings to read off a `LoadResult`.
    #[test]
    fn validate_option_tuples_raises_on_an_unknown_option() {
        let parsed = parse_beancount(BAD_OPTION);
        let errors = validate_option_tuples(&parsed.options, &LineLookup::new(BAD_OPTION));
        assert!(codes(&errors).contains(&"E7001"), "got {errors:?}");
    }

    #[test]
    fn validate_option_tuples_is_quiet_on_a_valid_option() {
        let src = "option \"title\" \"My Ledger\"\n";
        let parsed = parse_beancount(src);
        assert!(
            validate_option_tuples(&parsed.options, &LineLookup::new(src)).is_empty(),
            "a valid option must not produce a diagnostic"
        );
    }

    /// The two paths reach the warnings differently — `parse()` recomputes them
    /// through `Options::set`, `load_and_book` reads what the loader already
    /// produced — so the thing worth pinning is that they agree, and for every
    /// code rather than just the one in the bug report. E7002 in particular is
    /// raised on a *value*, which is a different arm than E7001's unknown key.
    #[test]
    fn both_paths_agree_for_every_option_code() {
        // The line too: both paths give each option diagnostic its option's
        // line (#2925), and neither names a file on this single-source path.
        type Seen = (
            Option<String>,
            String,
            Severity,
            Option<u32>,
            Option<String>,
        );
        let cases: &[(&str, &str)] = &[
            ("E7001", "option \"nonsense_option\" \"x\"\n"),
            ("E7002", "option \"booking_method\" \"not_a_method\"\n"),
            ("E7011", "option \"render_commas\" \"not_a_bool\"\n"),
            ("E7003", "option \"title\" \"a\"\noption \"title\" \"b\"\n"),
            ("E7004", "option \"allow_pipe_separator\" \"TRUE\"\n"),
            ("none", "option \"title\" \"t\"\n"),
        ];

        let seen = |errors: &[Error]| -> Vec<Seen> {
            errors
                .iter()
                .map(|e| {
                    (
                        e.code.clone(),
                        e.message.clone(),
                        e.severity,
                        e.line,
                        e.file.clone(),
                    )
                })
                .collect()
        };

        for (expected, opt) in cases {
            let src = format!("{opt}2024-01-01 open Assets:Cash USD\n");
            let recomputed =
                validate_option_tuples(&parse_beancount(&src).options, &LineLookup::new(&src));
            let from_loader = load_and_book(&src).option_errors;

            assert_eq!(
                seen(&recomputed),
                seen(&from_loader),
                "the recomputed option warnings must match what the loader \
                 raised, for {expected}"
            );
            if *expected == "none" {
                assert!(recomputed.is_empty(), "a valid option must be quiet");
            } else {
                assert!(
                    codes(&recomputed).contains(expected),
                    "fixture must actually raise {expected}; got {:?}",
                    codes(&recomputed)
                );
                assert!(
                    recomputed.iter().all(|e| e.line.is_some_and(|l| l >= 1)),
                    "every option diagnostic has its line: {recomputed:?}"
                );
            }
        }
    }

    /// `reported_errors` is what every reporting surface reads and `errors` is
    /// what every soundness gate reads. If option diagnostics ever leak into
    /// the second, a typo'd option makes a ledger unsound to work with; if they
    /// ever fall out of the first, surfaces go silent again. Both directions,
    /// pinned.
    #[test]
    fn option_diagnostics_are_reported_but_do_not_gate() {
        let load = load_and_book(BAD_OPTION);

        assert!(
            codes(&load.reported_errors()).contains(&"E7001"),
            "reported_errors must carry the option error; got {:?}",
            codes(&load.reported_errors())
        );
        assert!(
            !codes(&load.errors).contains(&"E7001"),
            "`errors` is the soundness gate's input and must NOT carry it; got {:?}",
            codes(&load.errors)
        );
        assert!(
            !has_fatal(&load.errors),
            "an invalid option must not read as an unsound directive stream"
        );
    }
}

/// The drift guard of [`parse_error_fields`]' deliberate copy of the
/// loader's [`rustledger_loader::parse_errors_to_ledger_errors`] (behind the
/// FFI and, inline, `rledger check`): the same parse errors, through the
/// loader's mapping, the multi-file [`crate::api::load_errors_to_errors`] and
/// the single-source [`parse_errors_to_wasm`], agree on message, code, phase,
/// hint, file, line and column. After a BOM and a multi-byte character, so
/// the columns count characters on every side.
#[cfg(test)]
mod parse_error_mapping_parity {
    use super::*;

    /// Message, code, phase, hint, file, line, column.
    type Row = (
        String,
        Option<String>,
        Option<String>,
        Option<String>,
        Option<String>,
        Option<u32>,
        Option<u32>,
    );

    const MAIN: &str = "main.beancount";
    const SOURCE: &str = "\u{FEFF}2024-01-01 open Assets:A\n\
        2024-01-03 open Assets:Ü 10\n\
        \x20 2024-01-04 open Assets:B\n\
        2024-01-05 open\n\
        2024-01-06 * \u{FEFF}\"ab\"\n";

    fn wasm_row(e: Error) -> Row {
        (e.message, e.code, e.phase, e.hint, e.file, e.line, e.column)
    }

    #[test]
    fn test_parse_error_mapping_agrees_with_the_loaders() {
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file(MAIN, SOURCE);
        let raw = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(Path::new(MAIN))
            .expect("loads");
        let failure = raw
            .errors
            .iter()
            .find(|e| matches!(e, LoadError::ParseErrors { .. }))
            .expect("the source fails to parse");

        let canonical: Vec<Row> =
            rustledger_loader::parse_errors_to_ledger_errors(failure, &raw.source_map)
                .into_iter()
                .map(|e| {
                    let location = e.location.expect("located");
                    (
                        e.message,
                        Some(e.code),
                        Some(e.phase),
                        e.hint,
                        Some(location.file.display().to_string()),
                        u32::try_from(location.line).ok(),
                        u32::try_from(location.column).ok(),
                    )
                })
                .collect();
        // Sharp enough to catch a drift: several errors, one with a hint.
        assert!(
            canonical.len() >= 3 && canonical.iter().any(|row| row.3.is_some()),
            "{canonical:?}"
        );

        let multi_file: Vec<Row> =
            crate::api::load_errors_to_errors(std::slice::from_ref(failure), &raw.source_map)
                .into_iter()
                .map(|mut e| {
                    // The path prefix of issue #2961.
                    e.message = e
                        .message
                        .strip_prefix("main.beancount: ")
                        .unwrap_or_else(|| panic!("prefixed: {}", e.message))
                        .to_string();
                    wasm_row(e)
                })
                .collect();
        assert_eq!(multi_file, canonical, "load_errors_to_errors");

        let single_source: Vec<Row> = parse_errors_to_wasm(&parse_beancount(SOURCE).errors, SOURCE)
            .into_iter()
            .map(|mut e| {
                // The single-source surfaces name no file.
                assert_eq!(e.file, None);
                e.file = Some(MAIN.to_string());
                wasm_row(e)
            })
            .collect();
        assert_eq!(single_source, canonical, "parse_errors_to_wasm");
    }
}
