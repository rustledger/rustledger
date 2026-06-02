//! Processing pipeline: sort → synth-plugins → Early → book → regular-plugins → Late → finalize.
//!
//! This module orchestrates the full processing pipeline for a beancount ledger,
//! equivalent to Python's `loader.load_file()` function.

use crate::{LoadError, LoadResult, Options, Plugin, SourceMap};
use rustledger_core::{BookingMethod, Directive, DisplayContext};
use rustledger_parser::Spanned;
use std::path::Path;
use thiserror::Error;

/// A CLI-supplied (or programmatic) extra plugin invocation.
///
/// Bundles the plugin name with its optional config string so the two
/// can't drift apart — the previous parallel-Vec representation could
/// silently misalign a config with the wrong plugin.
#[derive(Debug, Clone)]
pub struct ExtraPlugin {
    /// Plugin name (short or fully-qualified module path).
    pub name: String,
    /// Plugin-specific config string, if any.
    pub config: Option<String>,
}

/// Options for loading and processing a ledger.
#[derive(Debug, Clone)]
pub struct LoadOptions {
    /// Booking method for lot matching (default: Strict).
    pub booking_method: BookingMethod,
    /// Run plugins declared in the file (default: true).
    pub run_plugins: bool,
    /// Run `auto_accounts` plugin (default: false).
    pub auto_accounts: bool,
    /// Additional plugins to run (CLI `--plugin` or programmatic API),
    /// each with an optional config string.
    pub extra_plugins: Vec<ExtraPlugin>,
    /// Run validation after processing (default: true).
    pub validate: bool,
    /// Enable path security (prevent include traversal).
    pub path_security: bool,
}

impl Default for LoadOptions {
    fn default() -> Self {
        Self {
            booking_method: BookingMethod::Strict,
            run_plugins: true,
            auto_accounts: false,
            extra_plugins: Vec::new(),
            validate: true,
            path_security: false,
        }
    }
}

impl LoadOptions {
    /// Create options for raw loading (no booking, no plugins, no validation).
    #[must_use]
    pub const fn raw() -> Self {
        Self {
            booking_method: BookingMethod::Strict,
            run_plugins: false,
            auto_accounts: false,
            extra_plugins: Vec::new(),
            validate: false,
            path_security: false,
        }
    }
}

/// Errors that can occur during ledger processing.
#[derive(Debug, Error)]
pub enum ProcessError {
    /// Loading failed.
    #[error("loading failed: {0}")]
    Load(#[from] LoadError),

    /// Booking/interpolation error.
    #[cfg(feature = "booking")]
    #[error("booking error: {message}")]
    Booking {
        /// Error message.
        message: String,
        /// Date of the transaction.
        date: rustledger_core::NaiveDate,
        /// Narration of the transaction.
        narration: String,
    },

    /// Plugin execution error.
    #[cfg(feature = "plugins")]
    #[error("plugin error: {0}")]
    Plugin(String),

    /// Validation error.
    #[cfg(feature = "validation")]
    #[error("validation error: {0}")]
    Validation(String),

    /// Plugin output conversion error.
    #[cfg(feature = "plugins")]
    #[error("failed to convert plugin output: {0}")]
    PluginConversion(String),
}

/// A fully processed ledger.
///
/// This is the result of loading and processing a beancount file,
/// equivalent to the tuple returned by Python's `loader.load_file()`.
#[derive(Debug)]
pub struct Ledger {
    /// Processed directives (sorted, booked, plugins applied).
    pub directives: Vec<Spanned<Directive>>,
    /// Options parsed from the file.
    pub options: Options,
    /// Plugins declared in the file.
    pub plugins: Vec<Plugin>,
    /// Source map for error reporting.
    pub source_map: SourceMap,
    /// Errors encountered during processing.
    pub errors: Vec<LedgerError>,
    /// Display context for formatting numbers.
    pub display_context: DisplayContext,
}

/// Unified error type for ledger processing.
///
/// This encompasses all error types that can occur during loading,
/// booking, plugin execution, and validation.
#[derive(Debug)]
#[non_exhaustive]
pub struct LedgerError {
    /// Error severity.
    pub severity: ErrorSeverity,
    /// Error code (e.g., "E0001", "W8002").
    pub code: String,
    /// Human-readable error message.
    pub message: String,
    /// Source location, if available.
    pub location: Option<ErrorLocation>,
    /// Byte span (inclusive start, exclusive end) in the source file,
    /// used by rich renderers (e.g. miette) to draw a snippet around
    /// the offending directive. Consumers that only need `file:line:col`
    /// should use `location`; those that want to show the surrounding
    /// source text want this.
    pub source_span: Option<(usize, usize)>,
    /// Source file ID — index into the ledger's [`SourceMap`]. Used
    /// alongside `source_span` for snippet rendering.
    pub file_id: Option<u16>,
    /// Processing phase that produced this error: "parse", "validate", or "plugin".
    pub phase: String,
}

/// Error severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorSeverity {
    /// Error - indicates a problem that should be fixed.
    Error,
    /// Warning - indicates a potential issue.
    Warning,
}

/// Source location for an error.
#[derive(Debug, Clone)]
pub struct ErrorLocation {
    /// File path.
    pub file: std::path::PathBuf,
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (1-indexed).
    pub column: usize,
}

impl LedgerError {
    /// Create a new error with the given phase.
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: ErrorSeverity::Error,
            code: code.into(),
            message: message.into(),
            location: None,
            source_span: None,
            file_id: None,
            phase: "validate".to_string(),
        }
    }

    /// Create a new warning.
    pub fn warning(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: ErrorSeverity::Warning,
            code: code.into(),
            message: message.into(),
            location: None,
            source_span: None,
            file_id: None,
            phase: "validate".to_string(),
        }
    }

    /// Attach a source span and file ID so rich renderers can draw a snippet.
    #[must_use]
    pub const fn with_source_span(mut self, span: (usize, usize), file_id: u16) -> Self {
        self.source_span = Some(span);
        self.file_id = Some(file_id);
        self
    }

    /// Set the processing phase for this error.
    #[must_use]
    pub fn with_phase(mut self, phase: impl Into<String>) -> Self {
        self.phase = phase.into();
        self
    }

    /// Add a location to this error.
    #[must_use]
    pub fn with_location(mut self, location: ErrorLocation) -> Self {
        self.location = Some(location);
        self
    }
}

/// Process a raw load result into a fully processed ledger.
///
/// Pipeline (see numbered comments below for the rationale of each step):
///
/// ```text
///   1. sort                         (canonical display order)
///   2. synth plugins                (auto_accounts, document_discovery)
///   3. Early validation             (account presence, structural, lifecycle)
///   4. booking                      (cost spec resolution, interpolation)
///   5. partition                    (set aside failed-booking txns)
///   6. regular plugins              (file plugins + extras, on booked only)
///   7. Late validation              (balance, currency, inventory, on booked only)
///   8. finalize                     (unused-pad warnings)
///   9. re-merge                     (booked + failed → final Ledger.directives)
/// ```
pub fn process(raw: LoadResult, options: &LoadOptions) -> Result<Ledger, ProcessError> {
    let mut errors: Vec<LedgerError> = Vec::new();

    // Convert load errors to ledger errors (parse phase). Iterate by
    // reference so `raw` stays borrowable for the rest of the pipeline
    // (the phase transitions and validator setup below borrow it).
    for load_err in &raw.errors {
        errors.push(LedgerError::error("LOAD", load_err.to_string()).with_phase("parse"));
    }

    // Phase-typed pipeline (issue #1166). The phantom-typed
    // `Directives<P>` wrapper makes the sequence
    //
    //     Raw → Sorted → Synthed → EarlyValidated → Booked
    //         → RegularPluginsApplied → LateValidated → Finalized
    //
    // a compile-time property of the type system. Each transition
    // method consumes one phase and produces the next; the compiler
    // rejects any call-site that drops a phase, swaps two, or invokes
    // a later phase on raw input. See `crates/rustledger-loader/src/phase.rs`.
    //
    // The transitions themselves wrap the existing subsystem entry
    // points (`run_booking`, `run_plugins`, validators) without
    // changing their semantics — this PR is the structural refactor
    // only; behavior is bit-identical to the pre-#1166 pipeline.

    // Resolve the effective booking method once, before the pipeline
    // starts, so both the validator (early/late phases — needs it to
    // seed each opened account's per-account booking method, see
    // issue #1182) and the booking engine see the same value. File-
    // level `option "booking_method"` wins when explicitly set;
    // otherwise the API-level `LoadOptions.booking_method` is used.
    #[cfg(any(feature = "validation", feature = "booking"))]
    let effective_booking_method = resolve_effective_booking_method(&raw, options);

    #[cfg(feature = "validation")]
    let validation_session = if options.validate {
        Some(rustledger_validate::ValidationSession::new(
            build_validation_options(&raw.options, &raw.source_map, effective_booking_method),
        ))
    } else {
        None
    };

    // Compute `today` once for both phases — avoids a midnight-crossing
    // race where Early and Late could disagree on what day it is, and
    // gives `FutureDate` warnings a single coherent reference point.
    #[cfg(feature = "validation")]
    let today = jiff::Zoned::now().date();

    let synthed = crate::Directives::<crate::Raw>::from_parser(raw.directives)
        .sort()
        .apply_synth_plugins(
            &raw.plugins,
            &raw.options,
            options,
            &raw.source_map,
            &mut errors,
        )?;

    // The validation feature changes `early_validate`'s shape: with
    // it on we thread the `Option<ValidationSession<Pending>>` in and
    // catch the returned `Option<ValidationSession<EarlyDone>>` for
    // `late_validate` (typestate-moved per #1236); without it we just
    // get the next-phase `Directives` back. Branching here keeps each
    // cfg's signature small and prevents the call site from having to
    // know the typestate phase parameters in the disabled case.
    #[cfg(feature = "validation")]
    let (directives, validation_session) =
        synthed.early_validate(validation_session, today, &raw.source_map, &mut errors);
    #[cfg(not(feature = "validation"))]
    let directives = synthed.early_validate(&raw.source_map, &mut errors);

    let (booked, failed) = directives.book(
        #[cfg(feature = "booking")]
        effective_booking_method,
        #[cfg(feature = "booking")]
        &mut errors,
    );

    let regular_applied = booked.apply_regular_plugins(
        &raw.plugins,
        &raw.options,
        options,
        &raw.source_map,
        &mut errors,
    )?;

    #[cfg(feature = "validation")]
    let late_validated =
        regular_applied.late_validate(validation_session, today, &raw.source_map, &mut errors);
    #[cfg(not(feature = "validation"))]
    let late_validated = regular_applied.late_validate(&raw.source_map, &mut errors);

    let finalized = late_validated.finalize(failed);

    Ok(Ledger {
        directives: finalized.into_inner(),
        options: raw.options,
        plugins: raw.plugins,
        source_map: raw.source_map,
        errors,
        display_context: raw.display_context,
    })
}

/// Resolve the booking method from `LoadOptions` + file-level option.
///
/// Factored out of `process()` so both the validator session (which
/// needs it to seed per-account booking) and the booking engine see
/// the same value. File-level `option "booking_method"` wins when
/// explicitly set; otherwise the API-level default is used.
#[cfg(any(feature = "validation", feature = "booking"))]
fn resolve_effective_booking_method(
    raw: &LoadResult,
    options: &LoadOptions,
) -> rustledger_core::BookingMethod {
    let file_set = raw.options.set_options.contains("booking_method");
    if file_set {
        raw.options
            .booking_method
            .parse()
            .unwrap_or(options.booking_method)
    } else {
        options.booking_method
    }
}

// ============================================================================
// Phase transitions
// ============================================================================
//
// Each transition consumes a `Directives<P>` of one phase and
// produces a `Directives<NextP>` of the next phase. Bodies wrap the
// existing subsystem calls (`run_booking`, `run_plugins`, validators)
// without changing their semantics — only the type-level sequencing
// is new. See `phase.rs` for the phase markers and overall rationale.

/// Canonical display-order sort key: `(date, priority, file_id, span.start)`.
/// What BQL / JSON / format output expects and what Python beancount
/// produces. Used by `sort` (initial ordering) and `finalize` (re-sort
/// after merging failed bookings back in).
type CanonicalSortKey = (
    rustledger_core::NaiveDate,
    rustledger_core::DirectivePriority,
    u16,
    usize,
);

#[inline]
const fn canonical_sort_key(d: &Spanned<Directive>) -> CanonicalSortKey {
    (d.value.date(), d.value.priority(), d.file_id, d.span.start)
}

impl crate::Directives<crate::Raw> {
    /// Sort directives into canonical display order — see
    /// [`canonical_sort_key`].
    ///
    /// Booking needs a different iteration order (augmentations
    /// BEFORE reductions on the same `(date, priority)`) but doesn't
    /// need the underlying vec reordered — `run_booking` walks via
    /// a transient `Vec<usize>` index. This sort goes once, here,
    /// and the display order survives the rest of the pipeline.
    #[must_use]
    pub(crate) fn sort(mut self) -> crate::Directives<crate::Sorted> {
        self.as_vec_mut().sort_by_key(canonical_sort_key);
        crate::Directives::new_unchecked(std::mem::take(self.as_vec_mut()))
    }
}

impl crate::Directives<crate::Sorted> {
    /// Run synth-only plugins (`auto_accounts`, `document_discovery`)
    /// BEFORE early validation so the synthesizers inject Opens /
    /// Documents that Early checks depend on (E1001 account
    /// presence, E5001 missing-document file).
    ///
    /// Only this narrow synth subset runs here; everything else
    /// waits until after booking (post-booking plugin pass) so
    /// cost-spec-reading plugins see filled-in per-unit values on
    /// `CostNumber::PerUnitFromTotal`. See `PluginPass` rustdoc for
    /// the detailed split rationale.
    pub(crate) fn apply_synth_plugins(
        mut self,
        plugins: &[crate::Plugin],
        file_options: &crate::Options,
        options: &LoadOptions,
        source_map: &SourceMap,
        errors: &mut Vec<LedgerError>,
    ) -> Result<crate::Directives<crate::Synthed>, ProcessError> {
        // `run_plugins` early-returns when no plugin entry matches the
        // pass; no outer gate needed (and any outer gate risked
        // missing one of the implicit-synth triggers — auto_accounts,
        // document_discovery via `option "documents"`, file-declared
        // synth plugins).
        #[cfg(feature = "plugins")]
        run_plugins(
            self.as_vec_mut(),
            plugins,
            file_options,
            options,
            source_map,
            errors,
            PluginPass::PreBookingSynth,
        )?;
        // Suppress unused-arg warnings when `plugins` feature is off.
        #[cfg(not(feature = "plugins"))]
        {
            let _ = (plugins, file_options, options, source_map, errors);
        }
        Ok(crate::Directives::new_unchecked(std::mem::take(
            self.as_vec_mut(),
        )))
    }
}

impl crate::Directives<crate::Synthed> {
    /// Run the early-phase validators. Account-presence /
    /// lifecycle / structural errors are collected into `errors`
    /// (via the `LedgerError` stream); the directive list itself is
    /// unchanged by validation.
    ///
    /// Runs on pre-booking directives, AFTER synth plugins so
    /// account-presence checks (E1001) see any Opens that plugins
    /// like `auto_accounts` injected. This is what lets booking
    /// match Python's "prune zero-interp postings" behavior without
    /// losing E1001 on the elided-zero-to-unopened-account case
    /// (rustledger#877).
    #[cfg(feature = "validation")]
    pub(crate) fn early_validate(
        mut self,
        validation_session: Option<
            rustledger_validate::ValidationSession<rustledger_validate::Pending>,
        >,
        today: rustledger_core::NaiveDate,
        source_map: &SourceMap,
        errors: &mut Vec<LedgerError>,
    ) -> (
        crate::Directives<crate::EarlyValidated>,
        Option<rustledger_validate::ValidationSession<rustledger_validate::EarlyDone>>,
    ) {
        // Typestate move: consume `Pending`, return `EarlyDone`. The
        // session must be threaded by value rather than `&mut`-borrowed
        // because the phase parameter on `ValidationSession<P>` changes
        // as a result of the call (#1236). The caller in `process()`
        // captures the returned session and passes it to
        // `late_validate`.
        let session_out = validation_session.map(|session| {
            let (session, phase_errors) = session.run_early_spanned(self.as_slice(), today);
            ledger_errors_extend(errors, phase_errors, source_map);
            session
        });
        (
            crate::Directives::new_unchecked(std::mem::take(self.as_vec_mut())),
            session_out,
        )
    }

    #[cfg(not(feature = "validation"))]
    pub(crate) fn early_validate(
        mut self,
        source_map: &SourceMap,
        errors: &mut Vec<LedgerError>,
    ) -> crate::Directives<crate::EarlyValidated> {
        let _ = (source_map, errors);
        crate::Directives::new_unchecked(std::mem::take(self.as_vec_mut()))
    }
}

impl crate::Directives<crate::EarlyValidated> {
    /// Run booking/interpolation. Returns the successfully-booked
    /// directives plus a typed wrapper holding failed transactions.
    ///
    /// Failed transactions are in pre-booking shape (unresolved cost
    /// specs, unfilled elided slots, possibly unbalanced); they
    /// don't flow into regular plugins or Late validation — booking
    /// already reported the root cause and the downstream checks
    /// would cascade misleading errors. They get re-merged at
    /// [`crate::Directives::<crate::LateValidated>::finalize`].
    ///
    /// When the `booking` feature is disabled this is an identity
    /// transition: directives pass through unchanged and the failed
    /// set is always empty. The same method exists in both feature
    /// configurations so the caller in `process()` doesn't need a
    /// `#[cfg]` match — the booking-specific arguments appear or
    /// disappear via per-parameter `#[cfg]` attributes, mirroring
    /// `early_validate` / `late_validate`.
    pub(crate) fn book(
        mut self,
        #[cfg(feature = "booking")] effective_method: rustledger_core::BookingMethod,
        #[cfg(feature = "booking")] errors: &mut Vec<LedgerError>,
    ) -> (
        crate::Directives<crate::Booked>,
        crate::phase::FailedBookings,
    ) {
        #[cfg(feature = "booking")]
        let (booked, failed) =
            run_booking(std::mem::take(self.as_vec_mut()), effective_method, errors);
        #[cfg(not(feature = "booking"))]
        let (booked, failed): (Vec<Spanned<Directive>>, Vec<Spanned<Directive>>) =
            (std::mem::take(self.as_vec_mut()), Vec::new());
        (
            crate::Directives::new_unchecked(booked),
            crate::phase::FailedBookings::new(failed),
        )
    }
}

impl crate::Directives<crate::Booked> {
    /// Run post-booking plugins — file-declared + CLI extras.
    /// Cost-spec-reading plugins (`implicit_prices`,
    /// `capital_gains_classifier`, `check_average_cost`,
    /// `sell_gains`, `unrealized`, `valuation`) see filled-in
    /// per-unit values on `CostNumber::PerUnitFromTotal` because
    /// booking has run.
    ///
    /// Matches Python beancount's plugins-after-booking ordering
    /// and closes rustledger#1117. Failed transactions were
    /// partitioned out by `book`; plugins only see
    /// successfully-booked input.
    pub(crate) fn apply_regular_plugins(
        mut self,
        plugins: &[crate::Plugin],
        file_options: &crate::Options,
        options: &LoadOptions,
        source_map: &SourceMap,
        errors: &mut Vec<LedgerError>,
    ) -> Result<crate::Directives<crate::RegularPluginsApplied>, ProcessError> {
        // `run_plugins` early-returns when no plugin entry matches
        // the pass; no outer gate needed.
        #[cfg(feature = "plugins")]
        run_plugins(
            self.as_vec_mut(),
            plugins,
            file_options,
            options,
            source_map,
            errors,
            PluginPass::PostBooking,
        )?;
        #[cfg(not(feature = "plugins"))]
        {
            let _ = (plugins, file_options, options, source_map, errors);
        }
        Ok(crate::Directives::new_unchecked(std::mem::take(
            self.as_vec_mut(),
        )))
    }
}

impl crate::Directives<crate::RegularPluginsApplied> {
    /// Run the late-phase validators on booked + plugin-processed
    /// directives. Reuses the `ValidationSession` from
    /// `early_validate` so account / commodity / pad bookkeeping
    /// carries forward.
    #[cfg(feature = "validation")]
    pub(crate) fn late_validate(
        mut self,
        validation_session: Option<
            rustledger_validate::ValidationSession<rustledger_validate::EarlyDone>,
        >,
        today: rustledger_core::NaiveDate,
        source_map: &SourceMap,
        errors: &mut Vec<LedgerError>,
    ) -> crate::Directives<crate::LateValidated> {
        // Typestate move: consume `EarlyDone`, drive through `LateDone`
        // to `finalize()`. The compile-time enforcement here is that
        // we cannot call `late_validate` with a fresh `Pending` session
        // (no `From<Pending>` to `EarlyDone`), so the loader caller
        // must have routed the session through `early_validate` first
        // (#1236).
        if let Some(session) = validation_session {
            let (session, phase_errors) = session.run_late_spanned(self.as_slice(), today);
            ledger_errors_extend(errors, phase_errors, source_map);
            let finalize_errors = session.finalize();
            ledger_errors_extend(errors, finalize_errors, source_map);
        }
        crate::Directives::new_unchecked(std::mem::take(self.as_vec_mut()))
    }

    #[cfg(not(feature = "validation"))]
    pub(crate) fn late_validate(
        mut self,
        source_map: &SourceMap,
        errors: &mut Vec<LedgerError>,
    ) -> crate::Directives<crate::LateValidated> {
        let _ = (source_map, errors);
        crate::Directives::new_unchecked(std::mem::take(self.as_vec_mut()))
    }
}

impl crate::Directives<crate::LateValidated> {
    /// Re-merge failed (un-booked) transactions back into the
    /// directive list for output. The user wrote them and expects
    /// to see them in `Ledger.directives`; we kept them isolated
    /// from post-booking processing.
    ///
    /// Re-sorts to restore canonical display order — `booked`
    /// retained order during plugin transformation; the sort
    /// restores the failed entries' positions.
    pub(crate) fn finalize(
        mut self,
        failed: crate::phase::FailedBookings,
    ) -> crate::Directives<crate::Finalized> {
        let mut v = std::mem::take(self.as_vec_mut());
        v.extend(failed.into_inner());
        v.sort_by_key(canonical_sort_key);
        crate::Directives::new_unchecked(v)
    }
}

/// Run booking and interpolation on transactions, returning the
/// directives partitioned into `(booked, failed)`.
///
/// The caller has already sorted `directives` into canonical display
/// order `(date, priority, file_id, span.start)`. Booking needs the
/// extra constraint that cost-reduction transactions process AFTER
/// augmentations on the same `(date, priority)` so lots exist when
/// matched. Rather than re-sorting the whole vec, we walk it via a
/// transient `Vec<usize>` of indices sorted by booking order. Stable
/// sort preserves display-order tiebreaks between transactions with
/// the same `has_cost_reduction` flag.
///
/// Failed transactions are partitioned out into the second return
/// value so they don't flow into regular plugins or Late validation
/// (they're in pre-booking shape — postings have unresolved cost
/// specs and unfilled elided slots, so downstream processing would
/// cascade misleading errors). The caller is responsible for
/// re-merging `failed` into the final `Ledger.directives` for output
/// so the user still sees their original input.
#[cfg(feature = "booking")]
fn run_booking(
    mut directives: Vec<Spanned<Directive>>,
    booking_method: BookingMethod,
    errors: &mut Vec<LedgerError>,
) -> (Vec<Spanned<Directive>>, Vec<Spanned<Directive>>) {
    use rustledger_booking::BookingEngine;

    let mut engine = BookingEngine::with_method(booking_method);
    engine.register_account_methods(directives.iter().map(|s| &s.value));

    // Build an index ordered for booking: stable sort by
    // `has_cost_reduction` only (display order — `(date, priority,
    // file_id, span.start)` — is already encoded in the existing
    // positional order, and stable_sort preserves that as the tiebreak).
    let mut order: Vec<usize> = (0..directives.len()).collect();
    order.sort_by_key(|&i| {
        let d = &directives[i].value;
        (d.date(), d.priority(), d.has_cost_reduction())
    });

    let mut failed_indices: Vec<usize> = Vec::new();
    for &i in &order {
        let spanned = &mut directives[i];
        if let Directive::Transaction(txn) = &mut spanned.value {
            match engine.book_and_interpolate(txn) {
                Ok(result) => {
                    engine.apply(&result.transaction);
                    *txn = result.transaction;
                }
                Err(e) => {
                    errors.push(LedgerError::error(
                        "BOOK",
                        format!("{} ({}, \"{}\")", e, txn.date, txn.narration),
                    ));
                    failed_indices.push(i);
                }
            }
        }
    }

    // Partition into (booked, failed). Indices are valid in the current
    // `directives` vec (no mutation has happened since they were
    // collected); after this consuming iteration the vec is gone and
    // partition is fait accompli — no window where a caller could
    // accidentally mutate between collection and partition.
    let failed_set: rustc_hash::FxHashSet<usize> = failed_indices.iter().copied().collect();
    let mut booked = Vec::with_capacity(directives.len() - failed_indices.len());
    let mut failed = Vec::with_capacity(failed_indices.len());
    for (i, d) in directives.into_iter().enumerate() {
        if failed_set.contains(&i) {
            failed.push(d);
        } else {
            booked.push(d);
        }
    }
    (booked, failed)
}

/// Which subset of plugins to run.
///
/// The loader pipeline calls `run_plugins` twice: once with
/// [`PluginPass::PreBookingSynth`] before the Early validation phase
/// (so synthesizers can inject Opens / Documents that early checks
/// depend on), and once with [`PluginPass::PostBooking`] after booking
/// (so cost-spec-reading plugins like `implicit_prices`,
/// `capital_gains_classifier`, `check_average_cost`, `sell_gains`,
/// `unrealized`, and `valuation` see filled-in per-unit values on the
/// `CostNumber::PerUnitFromTotal` variant).
///
/// Standalone callers (LSP / FFI / tests on already-booked input) pass
/// [`PluginPass::PostBooking`] — synth plugins are a loader-internal
/// concern and would re-Open already-opened accounts if run a second
/// time.
#[cfg(feature = "plugins")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PluginPass {
    /// Only plugins that synthesize directives the Early validator
    /// depends on: `auto_accounts` (synthesizes Open directives) and
    /// the built-in document discovery walker (synthesizes Document
    /// directives the early phase checks for missing files).
    PreBookingSynth,
    /// All file-declared plugins and CLI `extra_plugins`, EXCLUDING
    /// `auto_accounts` and `document_discovery` (those ran pre-booking).
    /// Includes the 28 plugins that don't depend on synth state but
    /// may depend on booked cost specs.
    PostBooking,
}

/// Run plugins on directives.
///
/// Executes native plugins (and document discovery) on the given directives,
/// modifying them in-place. Plugin errors are appended to `errors`.
///
/// A single plugin invocation in `run_plugins`'s unified dispatch
/// list. `force_python` ("python:..." prefix) overrides native
/// resolution; `config` is the plugin-specific string passed to
/// `PluginInput.config`.
#[cfg(feature = "plugins")]
struct PluginInvocation {
    name: String,
    config: Option<String>,
    force_python: bool,
}

/// `pass` selects which subset of plugins to run — see [`PluginPass`].
/// The loader pipeline calls this twice (synth pass before Early,
/// regular pass after booking).
#[cfg(feature = "plugins")]
pub fn run_plugins(
    directives: &mut Vec<Spanned<Directive>>,
    file_plugins: &[Plugin],
    file_options: &Options,
    options: &LoadOptions,
    source_map: &SourceMap,
    errors: &mut Vec<LedgerError>,
    pass: PluginPass,
) -> Result<(), ProcessError> {
    use rustledger_plugin::{NativePlugin, NativePluginRegistry, PluginInput, PluginOptions};

    // Resolve document directories relative to the main file's directory.
    // Used to build doc_discovery's per-call config in the synth pass.
    let base_dir = source_map
        .files()
        .first()
        .and_then(|f| f.path.parent())
        .unwrap_or_else(|| std::path::Path::new("."));

    // Access the process-wide registry singleton. The registry is
    // immutable and stateless, so the same instance services every
    // call.
    let registry = NativePluginRegistry::global();

    // Build the unified list of plugins to invoke for this pass:
    //   1. Implicit synth plugins triggered by `LoadOptions` /
    //      `file_options` (auto_accounts via `options.auto_accounts`;
    //      document_discovery via non-empty `file_options.documents`).
    //   2. File-declared plugins from `plugin "..."` directives.
    //   3. CLI `--plugin` extras.
    // Pass classification happens here — once — via `registry.find_synth`.
    // A plugin enters the list iff its pass matches the requested `pass`.
    let mut entries: Vec<PluginInvocation> = Vec::new();

    if matches!(pass, PluginPass::PreBookingSynth) {
        // Implicit synth: API-level auto_accounts flag.
        if options.auto_accounts {
            entries.push(PluginInvocation {
                name: rustledger_plugin::AUTO_ACCOUNTS_NAME.to_string(),
                config: None,
                force_python: false,
            });
        }
        // Implicit synth: document_discovery, driven by `option "documents"`.
        // The plugin sits in the registry as a ZST; we hand it the
        // resolved directories + base_dir via its config JSON.
        if options.run_plugins && !file_options.documents.is_empty() {
            let resolved: Vec<String> = file_options
                .documents
                .iter()
                .map(|d| {
                    let path = std::path::Path::new(d);
                    if path.is_absolute() {
                        d.clone()
                    } else {
                        base_dir.join(path).to_string_lossy().to_string()
                    }
                })
                .collect();
            entries.push(PluginInvocation {
                name: rustledger_plugin::DOCUMENT_DISCOVERY_NAME.to_string(),
                config: Some(rustledger_plugin::document_discovery_config(
                    base_dir, &resolved,
                )),
                force_python: false,
            });
        }
    }

    // A plugin name belongs in the current pass iff its synth-marker
    // membership matches `pass`. Non-native plugins (WASM/Python) are
    // never in the synth registry and therefore always fall into the
    // PostBooking pass.
    let want_synth = matches!(pass, PluginPass::PreBookingSynth);

    // File-declared plugins.
    if options.run_plugins {
        for plugin in file_plugins {
            if registry.find_synth(&plugin.name).is_some() == want_synth {
                entries.push(PluginInvocation {
                    name: plugin.name.clone(),
                    config: plugin.config.clone(),
                    force_python: plugin.force_python,
                });
            }
        }
    }

    // CLI extra plugins.
    for extra in &options.extra_plugins {
        if registry.find_synth(&extra.name).is_some() == want_synth {
            entries.push(PluginInvocation {
                name: extra.name.clone(),
                config: extra.config.clone(),
                force_python: false,
            });
        }
    }

    if entries.is_empty() {
        return Ok(());
    }

    let plugin_options = PluginOptions {
        operating_currencies: file_options.operating_currency.clone(),
        title: file_options.title.clone(),
    };

    // Dispatch each entry. Native plugins resolve through the typed
    // registry (`find_synth` / `find_regular`) keyed on the pass — the
    // returned reference type reflects the pass. Anything that doesn't
    // resolve falls through to the WASM/Python branches.
    for invocation in &entries {
        let PluginInvocation {
            name: raw_name,
            config: plugin_config,
            force_python,
        } = invocation;

        // Dispatch via the typed registry. `find_synth`/`find_regular`
        // internally take the short name (last `.`-separated segment),
        // so prefixed names like `"beancount.plugins.implicit_prices"`
        // resolve through the same call — no explicit prefix-stripping
        // needed. Returns `Some` only if the plugin exists AND its
        // marker trait matches the requested pass: a `RegularPlugin`
        // won't be returned from `find_synth` (and vice versa), even
        // on a name collision. Anything that returns `None` (WASM,
        // Python, unknown names, wrong-pass natives) falls through
        // to the WASM/Python branches below.
        let native_plugin: Option<&dyn NativePlugin> = if *force_python {
            None
        } else {
            match pass {
                PluginPass::PreBookingSynth => registry
                    .find_synth(raw_name)
                    .map(|p| p as &dyn NativePlugin),
                PluginPass::PostBooking => registry
                    .find_regular(raw_name)
                    .map(|p| p as &dyn NativePlugin),
            }
        };

        if let Some(plugin) = native_plugin {
            let wrappers = build_wrappers(directives, source_map);
            let input = PluginInput {
                directives: wrappers,
                options: plugin_options.clone(),
                config: plugin_config.clone(),
            };
            let output = plugin.process(input);
            record_plugin_errors(errors, output.errors, source_map);
            apply_plugin_ops(directives, output.ops, errors, source_map)?;
        } else {
            // Not a native plugin — categorize and handle
            let plugin_path = std::path::Path::new(raw_name);
            let ext = plugin_path
                .extension()
                .and_then(|e| e.to_str())
                .unwrap_or("")
                .to_lowercase();

            // The closure is only invoked from inside the wasm-plugins /
            // python-plugins cfg blocks below. The whole function is
            // already `#[cfg(feature = "plugins")]`, so this only matters
            // when `plugins` is enabled but neither child feature is
            // (e.g. `--features native-plugins`). Allow `unused_variables`
            // for exactly that configuration. Underscore-prefixing the
            // binding would have been the wrong fix because we DO call
            // the closure in builds with one of the features enabled,
            // which would trip `no_effect_underscore_binding` instead.
            #[cfg_attr(
                not(any(feature = "wasm-plugins", feature = "python-plugins")),
                allow(unused_variables)
            )]
            let resolve_path = |name: &str| -> Result<std::path::PathBuf, String> {
                let p = std::path::Path::new(name);
                let resolved = if p.is_absolute() {
                    p.to_path_buf()
                } else {
                    base_dir.join(name)
                };

                // Path security: prevent plugins from outside the ledger directory
                if options.path_security
                    && let (Ok(canon_base), Ok(canon_plugin)) =
                        (base_dir.canonicalize(), resolved.canonicalize())
                    && !canon_plugin.starts_with(&canon_base)
                {
                    return Err(format!(
                        "plugin path '{name}' is outside the ledger directory"
                    ));
                }

                Ok(resolved)
            };

            if ext == "wasm" {
                // WASM plugin
                #[cfg(feature = "wasm-plugins")]
                {
                    let wasm_path = match resolve_path(raw_name) {
                        Ok(p) => p,
                        Err(e) => {
                            errors.push(LedgerError::error("PLUGIN", e).with_phase("plugin"));
                            continue;
                        }
                    };
                    let wrappers = build_wrappers(directives, source_map);
                    match run_wasm_plugin(&wasm_path, &wrappers, &plugin_options, plugin_config) {
                        Ok((ops, plugin_errors)) => {
                            for err in plugin_errors {
                                errors.push(err);
                            }
                            apply_plugin_ops(directives, ops, errors, source_map)?;
                        }
                        Err(e) => {
                            errors.push(
                                LedgerError::error(
                                    "PLUGIN",
                                    format!("WASM plugin {} failed: {e}", wasm_path.display()),
                                )
                                .with_phase("plugin"),
                            );
                        }
                    }
                }
                #[cfg(not(feature = "wasm-plugins"))]
                {
                    errors.push(
                        LedgerError::error(
                            "PLUGIN",
                            format!("WASM plugin '{raw_name}' requires the wasm-plugins feature"),
                        )
                        .with_phase("plugin"),
                    );
                }
            } else if *force_python
                || ext == "py"
                || raw_name.contains(std::path::MAIN_SEPARATOR)
                || raw_name.contains('.')
            {
                // Python module or file-based plugin (or force_python via "python:" prefix)
                #[cfg(feature = "python-plugins")]
                {
                    let resolved = match resolve_path(raw_name) {
                        Ok(p) => p,
                        Err(e) => {
                            errors.push(LedgerError::error("PLUGIN", e).with_phase("plugin"));
                            continue;
                        }
                    };
                    let wrappers = build_wrappers(directives, source_map);
                    match run_python_plugin(
                        raw_name,
                        &resolved,
                        base_dir,
                        &wrappers,
                        &plugin_options,
                        plugin_config,
                    ) {
                        Ok((ops, plugin_errors)) => {
                            for err in plugin_errors {
                                errors.push(err);
                            }
                            apply_plugin_ops(directives, ops, errors, source_map)?;
                        }
                        Err(e) => {
                            errors.push(LedgerError::error("E8002", e).with_phase("plugin"));
                        }
                    }
                }
                #[cfg(not(feature = "python-plugins"))]
                {
                    errors.push(
                        LedgerError::error(
                            "E8005",
                            format!(
                                "Python plugin \"{raw_name}\" requires the python-plugins feature",
                            ),
                        )
                        .with_phase("plugin"),
                    );
                }
            } else {
                // Completely unknown plugin name — try to suggest a module path
                #[cfg(feature = "python-plugins")]
                {
                    use rustledger_plugin::python::{is_python_available, suggest_module_path};
                    let suggestion = if is_python_available() {
                        suggest_module_path(raw_name)
                    } else {
                        None
                    };
                    if let Some(module_path) = suggestion {
                        errors.push(
                                LedgerError::error(
                                    "E8004",
                                    format!(
                                        "Cannot resolve Python module '{raw_name}'. Replace with: plugin \"{module_path}\""
                                    ),
                                )
                                .with_phase("plugin"),
                            );
                    } else {
                        errors.push(
                            LedgerError::error(
                                "E8001",
                                format!("Plugin not found: \"{raw_name}\""),
                            )
                            .with_phase("plugin"),
                        );
                    }
                }
                #[cfg(not(feature = "python-plugins"))]
                {
                    errors.push(
                        LedgerError::error("E8001", format!("Plugin not found: \"{raw_name}\""))
                            .with_phase("plugin"),
                    );
                }
            }
        }
    }
    // No final wrapper→directive conversion needed: `apply_plugin_ops`
    // updates `directives` in place after each plugin call, preserving
    // original spans on Keep/Modify ops. Plugin-synthesized directives
    // (Insert ops) get `SYNTHESIZED_FILE_ID` and a zero span.
    Ok(())
}

/// Build a fresh `Vec<DirectiveWrapper>` from the current directives,
/// carrying filename + line number for plugin-side error reporting.
/// Spans don't need to round-trip through the wrappers — the loader
/// preserves them via `apply_plugin_ops` matching on op index.
#[cfg(feature = "plugins")]
fn build_wrappers(
    directives: &[Spanned<Directive>],
    source_map: &SourceMap,
) -> Vec<rustledger_plugin::DirectiveWrapper> {
    use rustledger_plugin::directive_to_wrapper_with_location;

    directives
        .iter()
        .map(|spanned| {
            let (filename, lineno) = if let Some(file) = source_map.get(spanned.file_id as usize) {
                let (line, _col) = file.line_col(spanned.span.start);
                (Some(file.path.display().to_string()), Some(line as u32))
            } else {
                (None, None)
            };
            directive_to_wrapper_with_location(&spanned.value, filename, lineno)
        })
        .collect()
}

/// Push plugin errors into the ledger's error stream, tagged with
/// `phase: "plugin"` and — when the plugin set `source_file` /
/// `line_number` on the error — an attached `ErrorLocation` so
/// downstream renderers (CLI, LSP, JSON output) can pinpoint where
/// the plugin objected.
///
/// Source-location resolution: if the wrapper's `source_file` resolves
/// to a real file in the source map, use that for `ErrorLocation.file`
/// and treat `line_number` as the line index. Plugin-synthesized
/// filenames (e.g. `"<auto_accounts>"`) that don't match any real
/// file are passed through as `PathBuf::from(name)` so the rendered
/// location still attributes the error to the originating plugin —
/// better than silently dropping the field.
#[cfg(feature = "plugins")]
fn record_plugin_errors(
    errors: &mut Vec<LedgerError>,
    plugin_errors: Vec<rustledger_plugin::PluginError>,
    source_map: &SourceMap,
) {
    for err in plugin_errors {
        let mut ledger_err = match err.severity {
            rustledger_plugin::PluginErrorSeverity::Error => {
                LedgerError::error("PLUGIN", err.message).with_phase("plugin")
            }
            rustledger_plugin::PluginErrorSeverity::Warning => {
                LedgerError::warning("PLUGIN", err.message).with_phase("plugin")
            }
        };
        // Propagate plugin-set source location into `ErrorLocation`.
        // Column defaults to 1 — plugin errors don't carry column info
        // through the wrapper protocol.
        if let (Some(file), Some(line)) = (&err.source_file, err.line_number) {
            let resolved_path = source_map
                .get_by_path(std::path::Path::new(file))
                .map_or_else(|| std::path::PathBuf::from(file), |f| f.path.clone());
            ledger_err = ledger_err.with_location(ErrorLocation {
                file: resolved_path,
                line: line as usize,
                column: 1,
            });
        }
        errors.push(ledger_err);
    }
}

/// Apply a plugin's `Vec<PluginOp>` to `directives` in place.
///
/// Validates that the op set forms a complete partition of the input
/// indices (each input index appears in exactly one `Keep` / `Modify` /
/// `Delete` op). Protocol violations produce a `PLUGIN` error in
/// `errors` and leave `directives` untouched.
///
/// For `Keep(i)` / `Modify(i, w)`, the resulting `Spanned<Directive>`
/// inherits `directives[i]`'s span and `file_id` — this is the core of
/// the ops protocol's correctness guarantee (plugin-transformed
/// directives keep their original source identity for error reporting).
/// `Insert(w)` directives get `(Span::ZERO, SYNTHESIZED_FILE_ID)`.
///
/// Inner posting spans returned by plugins are sanitized against the
/// host's `SourceMap` (see [`sanitize_inner_posting_spans`]) so a
/// misbehaving plugin cannot smuggle out-of-bounds spans into the LSP.
#[cfg(feature = "plugins")]
fn apply_plugin_ops(
    directives: &mut Vec<Spanned<Directive>>,
    ops: Vec<rustledger_plugin::PluginOp>,
    errors: &mut Vec<LedgerError>,
    source_map: &SourceMap,
) -> Result<(), ProcessError> {
    use rustledger_plugin::PluginOp;
    use rustledger_plugin::wrapper_to_directive;

    let n = directives.len();

    // Validate: every input index in {Keep, Modify, Delete} exactly once.
    let mut seen = vec![false; n];
    for op in &ops {
        let idx = match op {
            PluginOp::Keep(i) | PluginOp::Modify(i, _) | PluginOp::Delete(i) => Some(*i),
            PluginOp::Insert(_) => None,
        };
        if let Some(i) = idx {
            if i >= n {
                errors.push(
                    LedgerError::error(
                        "PLUGIN",
                        format!(
                            "plugin op references out-of-bounds input index {i} (input has {n} directives)"
                        ),
                    )
                    .with_phase("plugin"),
                );
                return Ok(());
            }
            if seen[i] {
                errors.push(
                    LedgerError::error(
                        "PLUGIN",
                        format!("plugin op references input index {i} more than once"),
                    )
                    .with_phase("plugin"),
                );
                return Ok(());
            }
            seen[i] = true;
        }
    }
    for (i, was_seen) in seen.iter().enumerate() {
        if !was_seen {
            errors.push(
                LedgerError::error(
                    "PLUGIN",
                    format!(
                        "plugin omitted input directive {i} (must appear in exactly one of Keep/Modify/Delete)"
                    ),
                )
                .with_phase("plugin"),
            );
            return Ok(());
        }
    }

    // Materialize new directives, preserving spans for Keep/Modify.
    let mut new_directives = Vec::with_capacity(ops.len());
    for op in ops {
        match op {
            PluginOp::Keep(i) => {
                new_directives.push(directives[i].clone());
            }
            PluginOp::Modify(i, wrapper) => {
                let mut directive = wrapper_to_directive(&wrapper)
                    .map_err(|e| ProcessError::PluginConversion(e.to_string()))?;
                // Plugins are not trusted to return well-formed inner
                // posting spans — a misbehaving plugin can synthesize a
                // file_id pointing at a nonexistent source or a span
                // that runs past EOF. The LSP later builds TextEdits
                // from these spans, so an out-of-bounds posting span
                // would produce a corrupt edit. Reset any inner posting
                // span that doesn't refer to a real loaded file or that
                // exceeds the file's length to `Spanned::synthesized`.
                sanitize_inner_posting_spans(&mut directive, source_map);
                new_directives.push(Spanned {
                    value: directive,
                    span: directives[i].span,
                    file_id: directives[i].file_id,
                });
            }
            PluginOp::Insert(wrapper) => {
                // Same trust caveat as Modify: don't let an Insert smuggle
                // bogus inner-posting spans through.
                // (Wrapper-derived outer span is validated below.)
                // Resolve the wrapper's filename + line number, if set,
                // into a real (file_id, span) when the filename
                // corresponds to a loaded source file. Falls back to
                // SYNTHESIZED_FILE_ID + zero span otherwise — including
                // for plugin-only attribution like `"<auto_accounts>"`
                // (which never matches a loaded file).
                let (span, file_id) = match (&wrapper.filename, wrapper.lineno) {
                    (Some(filename), Some(lineno)) => {
                        if let Some(file) = source_map.get_by_path(std::path::Path::new(filename)) {
                            let span_start = file.line_start(lineno as usize).unwrap_or(0);
                            (
                                rustledger_parser::Span::new(span_start, span_start),
                                file.id as u16,
                            )
                        } else {
                            (
                                rustledger_parser::Span::ZERO,
                                rustledger_parser::SYNTHESIZED_FILE_ID,
                            )
                        }
                    }
                    _ => (
                        rustledger_parser::Span::ZERO,
                        rustledger_parser::SYNTHESIZED_FILE_ID,
                    ),
                };
                let mut directive = wrapper_to_directive(&wrapper)
                    .map_err(|e| ProcessError::PluginConversion(e.to_string()))?;
                sanitize_inner_posting_spans(&mut directive, source_map);
                new_directives.push(Spanned::new(directive, span).with_file_id(file_id as usize));
            }
            PluginOp::Delete(_) => {}
        }
    }

    *directives = new_directives;
    Ok(())
}

/// Reset any inner `Spanned<Posting>` whose location does not refer to a
/// real loaded source range to [`Spanned::synthesized`]. Plugins are not
/// trusted to return well-formed `file_id` + byte ranges; without this,
/// a misbehaving plugin could induce out-of-bounds LSP text edits.
///
/// A span is considered valid when:
/// - `file_id == SYNTHESIZED_FILE_ID` (genuine synthesis), OR
/// - the `file_id` resolves in `SourceMap` AND `0 <= start <= end <= len`
///   for that file's source.
///
/// Everything else collapses to `Spanned::synthesized(posting)`. As a
/// final pass, synthesized postings that arrived with a non-zero span
/// are normalized to `Span::ZERO` so the in-memory state matches the
/// `Spanned::synthesized` constructor's contract (`file_id` +
/// `Span::ZERO`).
#[cfg(feature = "plugins")]
fn sanitize_inner_posting_spans(directive: &mut Directive, source_map: &SourceMap) {
    use rustledger_core::Span;
    use rustledger_parser::SYNTHESIZED_FILE_ID;
    if let Directive::Transaction(txn) = directive {
        for p in &mut txn.postings {
            let ok = if p.file_id == SYNTHESIZED_FILE_ID {
                true
            } else {
                source_map
                    .get(p.file_id as usize)
                    .is_some_and(|f| p.span.start <= p.span.end && p.span.end <= f.source.len())
            };
            if !ok {
                let inner = std::mem::replace(
                    &mut p.value,
                    rustledger_core::Posting::auto(rustledger_core::InternedStr::from("")),
                );
                *p = rustledger_core::Spanned::synthesized(inner);
            } else if p.file_id == SYNTHESIZED_FILE_ID && p.span != Span::ZERO {
                // Synthesized → span is meaningless; normalize so the
                // state is consistent with `Spanned::synthesized`.
                p.span = Span::ZERO;
            }
        }
    }
}

/// Build a [`ValidationOptions`] from loader-level file options.
///
/// Factored out of the old `run_validation` so both the early and
/// late phases in `process()` can share the same `ValidationSession`
/// configuration. Document-dir resolution is relative to the main
/// file's parent directory.
#[cfg(feature = "validation")]
fn build_validation_options(
    file_options: &Options,
    source_map: &SourceMap,
    default_booking_method: BookingMethod,
) -> rustledger_validate::ValidationOptions {
    use rustledger_validate::ValidationOptions;

    // Resolve document directories relative to the main file's
    // directory. Absolute paths pass through; relative paths are
    // joined onto the source map's first file's parent. Matches the
    // pre-refactor `run_validation` behavior exactly.
    let base_dir = source_map
        .files()
        .first()
        .and_then(|f| f.path.parent())
        .unwrap_or_else(|| std::path::Path::new("."));

    let resolved_document_dirs: Vec<std::path::PathBuf> = file_options
        .documents
        .iter()
        .map(|d| {
            let path = std::path::Path::new(d);
            if path.is_absolute() {
                path.to_path_buf()
            } else {
                base_dir.join(path)
            }
        })
        .collect();

    let account_types: Vec<String> = file_options
        .account_types()
        .iter()
        .map(|s| (*s).to_string())
        .collect();

    ValidationOptions::default()
        .with_account_types(account_types)
        .with_document_dirs(resolved_document_dirs)
        .with_infer_tolerance_from_cost(file_options.infer_tolerance_from_cost)
        .with_tolerance_multiplier(file_options.inferred_tolerance_multiplier)
        .with_inferred_tolerance_default(file_options.inferred_tolerance_default.clone())
        .with_default_booking_method(default_booking_method)
}

/// Convert a batch of [`rustledger_validate::ValidationError`]s into
/// loader-level [`LedgerError`]s (with resolved `file:line:column`
/// locations) and append to the existing list.
///
/// Factored out so both validation phases in `process()` share the
/// same conversion path.
#[cfg(feature = "validation")]
fn ledger_errors_extend(
    errors: &mut Vec<LedgerError>,
    validation_errors: Vec<rustledger_validate::ValidationError>,
    source_map: &SourceMap,
) {
    for err in validation_errors {
        let phase = if err.code.is_parse_phase() {
            "parse"
        } else {
            "validate"
        };
        let severity_level = if err.code.is_warning() {
            ErrorSeverity::Warning
        } else {
            ErrorSeverity::Error
        };
        // Fold the advisory note (if any) into the message so it propagates
        // through every downstream format (LedgerError, JSON diagnostic, CLI
        // report, LSP diagnostic) without each one needing a dedicated field.
        let message = match &err.note {
            Some(note) => format!("{err}\n  note: {note}"),
            None => err.to_string(),
        };
        // Resolve span + file_id into a file/line/column triple so CLI and
        // LSP consumers can render `file:line:col` headers without having
        // to do the lookup themselves (issue #901).
        let location = err.span.and_then(|span| {
            let fid = err.file_id? as usize;
            let file = source_map.get(fid)?;
            let (line, column) = file.line_col(span.start);
            Some(ErrorLocation {
                file: file.path.clone(),
                line,
                column,
            })
        });
        errors.push(LedgerError {
            severity: severity_level,
            code: err.code.code().to_string(),
            message,
            location,
            source_span: err.span.map(|s| (s.start, s.end)),
            file_id: err.file_id,
            phase: phase.to_string(),
        });
    }
}

/// Load and fully process a beancount file.
///
/// This is the main entry point, equivalent to Python's `loader.load_file()`.
/// It performs: parse → sort → synth-plugins → Early → book → regular-plugins → Late → finalize.
///
/// # Example
///
/// ```ignore
/// use rustledger_loader::{load, LoadOptions};
/// use std::path::Path;
///
/// let ledger = load(Path::new("ledger.beancount"), LoadOptions::default())?;
/// for error in &ledger.errors {
///     eprintln!("{}: {}", error.code, error.message);
/// }
/// ```
pub fn load(path: &Path, options: &LoadOptions) -> Result<Ledger, ProcessError> {
    let mut loader = crate::Loader::new();

    if options.path_security {
        loader = loader.with_path_security(true);
    }

    let raw = loader.load(path)?;
    process(raw, options)
}

/// Load a beancount file without processing.
///
/// This returns raw directives without sorting, booking, or plugins.
/// Use this when you need the original parse output.
pub fn load_raw(path: &Path) -> Result<LoadResult, LoadError> {
    crate::Loader::new().load(path)
}

/// Run a WASM plugin and return its output ops and errors.
#[cfg(feature = "wasm-plugins")]
fn run_wasm_plugin(
    wasm_path: &std::path::Path,
    directives: &[rustledger_plugin::DirectiveWrapper],
    options: &rustledger_plugin::PluginOptions,
    config: &Option<String>,
) -> Result<(Vec<rustledger_plugin::PluginOp>, Vec<LedgerError>), String> {
    use rustledger_plugin::{PluginInput, PluginManager};

    let mut mgr = PluginManager::new();
    let plugin_idx = mgr
        .load(wasm_path)
        .map_err(|e| format!("failed to load: {e}"))?;

    let input = PluginInput {
        directives: directives.to_vec(),
        options: options.clone(),
        config: config.clone(),
    };

    let output = mgr
        .execute(plugin_idx, &input)
        .map_err(|e| format!("execution failed: {e}"))?;

    let mut errors = Vec::new();
    for err in output.errors {
        let ledger_err = match err.severity {
            rustledger_plugin::PluginErrorSeverity::Error => {
                LedgerError::error("PLUGIN", err.message).with_phase("plugin")
            }
            rustledger_plugin::PluginErrorSeverity::Warning => {
                LedgerError::warning("PLUGIN", err.message).with_phase("plugin")
            }
        };
        errors.push(ledger_err);
    }

    Ok((output.ops, errors))
}

/// Run a Python module plugin via the WASI-based Python runtime.
#[cfg(feature = "python-plugins")]
fn run_python_plugin(
    module_name: &str,
    resolved_path: &std::path::Path,
    base_dir: &std::path::Path,
    directives: &[rustledger_plugin::DirectiveWrapper],
    options: &rustledger_plugin::PluginOptions,
    config: &Option<String>,
) -> Result<(Vec<rustledger_plugin::PluginOp>, Vec<LedgerError>), String> {
    use rustledger_plugin::{PluginInput, python::PythonRuntime};

    let runtime = PythonRuntime::new().map_err(|e| format!("Python runtime unavailable: {e}"))?;

    let input = PluginInput {
        directives: directives.to_vec(),
        options: options.clone(),
        config: config.clone(),
    };

    // Try file-based execution first, then module-based
    let is_file = resolved_path.exists()
        || std::path::Path::new(module_name)
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("py"))
        || module_name.contains(std::path::MAIN_SEPARATOR);

    let output = if is_file {
        runtime
            .execute_module(module_name, &input, Some(base_dir))
            .map_err(|e| format!("Python plugin execution failed: {e}"))?
    } else {
        runtime
            .execute_module(module_name, &input, Some(base_dir))
            .map_err(|e| format!("Python plugin '{module_name}' execution failed: {e}"))?
    };

    let mut errors = Vec::new();
    for err in output.errors {
        let ledger_err = match err.severity {
            rustledger_plugin::PluginErrorSeverity::Error => {
                LedgerError::error("PLUGIN", err.message).with_phase("plugin")
            }
            rustledger_plugin::PluginErrorSeverity::Warning => {
                LedgerError::warning("PLUGIN", err.message).with_phase("plugin")
            }
        };
        errors.push(ledger_err);
    }

    Ok((output.ops, errors))
}

#[cfg(all(test, feature = "plugins"))]
mod sanitize_tests {
    use super::sanitize_inner_posting_spans;
    use crate::source_map::SourceMap;
    use rust_decimal_macros::dec;
    use rustledger_core::{
        Amount, Directive, IncompleteAmount, Posting, SYNTHESIZED_FILE_ID, Span, Spanned,
        Transaction,
    };
    use std::path::PathBuf;
    use std::sync::Arc;

    fn txn_with_postings(postings: Vec<Spanned<Posting>>) -> Directive {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let mut txn = Transaction::new(date, "x");
        txn.postings = postings;
        Directive::Transaction(txn)
    }

    fn posting_at(file_id: u16, span: Span) -> Spanned<Posting> {
        let p = Posting::with_incomplete(
            "Assets:Cash",
            IncompleteAmount::Complete(Amount::new(dec!(1), "USD")),
        );
        Spanned::new(p, span).with_file_id(file_id as usize)
    }

    fn source_map_with_one_file(source: &str) -> (SourceMap, u16) {
        let mut sm = SourceMap::new();
        let id = sm.add_file(PathBuf::from("test.bean"), Arc::from(source));
        (sm, id as u16)
    }

    #[test]
    fn span_within_real_file_is_preserved() {
        let (sm, fid) = source_map_with_one_file("0123456789");
        let mut d = txn_with_postings(vec![posting_at(fid, Span::new(2, 6))]);
        sanitize_inner_posting_spans(&mut d, &sm);
        let Directive::Transaction(t) = &d else {
            unreachable!()
        };
        assert_eq!(t.postings[0].file_id, fid);
        assert_eq!(t.postings[0].span, Span::new(2, 6));
    }

    #[test]
    fn span_past_eof_is_reset_to_synthesized() {
        // Bug case: a misbehaving plugin claims the posting extends past
        // the file's actual length. The sanitizer must reject it so the
        // LSP can't be tricked into producing an out-of-bounds TextEdit.
        let (sm, fid) = source_map_with_one_file("0123456789"); // 10 bytes
        let mut d = txn_with_postings(vec![posting_at(fid, Span::new(0, 9999))]);
        sanitize_inner_posting_spans(&mut d, &sm);
        let Directive::Transaction(t) = &d else {
            unreachable!()
        };
        assert_eq!(t.postings[0].file_id, SYNTHESIZED_FILE_ID);
        assert_eq!(t.postings[0].span, Span::ZERO);
    }

    #[test]
    fn unknown_file_id_is_reset_to_synthesized() {
        // Plugin claims a file_id that the host's SourceMap doesn't know.
        let (sm, _real) = source_map_with_one_file("hello");
        let mut d = txn_with_postings(vec![posting_at(123, Span::new(0, 5))]);
        sanitize_inner_posting_spans(&mut d, &sm);
        let Directive::Transaction(t) = &d else {
            unreachable!()
        };
        assert_eq!(t.postings[0].file_id, SYNTHESIZED_FILE_ID);
        assert_eq!(t.postings[0].span, Span::ZERO);
    }

    #[test]
    fn start_after_end_is_reset_to_synthesized() {
        let (sm, fid) = source_map_with_one_file("abcdef");
        let mut d = txn_with_postings(vec![posting_at(fid, Span::new(5, 2))]);
        sanitize_inner_posting_spans(&mut d, &sm);
        let Directive::Transaction(t) = &d else {
            unreachable!()
        };
        assert_eq!(t.postings[0].file_id, SYNTHESIZED_FILE_ID);
        assert_eq!(t.postings[0].span, Span::ZERO);
    }

    #[test]
    fn synthesized_file_id_is_left_alone_but_span_normalized() {
        // file_id == SYNTHESIZED_FILE_ID with a non-zero span: the
        // sanitizer leaves it synthesized (span is meaningless for
        // synth postings) but normalizes to Span::ZERO for tidy state.
        let (sm, _fid) = source_map_with_one_file("x");
        let mut d = txn_with_postings(vec![posting_at(SYNTHESIZED_FILE_ID, Span::new(100, 200))]);
        sanitize_inner_posting_spans(&mut d, &sm);
        let Directive::Transaction(t) = &d else {
            unreachable!()
        };
        assert_eq!(t.postings[0].file_id, SYNTHESIZED_FILE_ID);
        assert_eq!(t.postings[0].span, Span::ZERO, "synth span normalized");
    }

    #[test]
    fn boundary_span_eq_source_len_is_valid() {
        // end == source.len() is the canonical "to-end-of-file" span;
        // must not be rejected.
        let (sm, fid) = source_map_with_one_file("abcd");
        let mut d = txn_with_postings(vec![posting_at(fid, Span::new(0, 4))]);
        sanitize_inner_posting_spans(&mut d, &sm);
        let Directive::Transaction(t) = &d else {
            unreachable!()
        };
        assert_eq!(t.postings[0].file_id, fid);
        assert_eq!(t.postings[0].span, Span::new(0, 4));
    }

    #[test]
    fn non_transaction_directive_is_left_alone() {
        // Sanitizer only walks transactions; other directive types have
        // no inner posting spans.
        let (sm, _fid) = source_map_with_one_file("x");
        let mut d = Directive::Open(rustledger_core::Open {
            date: rustledger_core::naive_date(2024, 1, 1).unwrap(),
            account: "Assets:Bank".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        });
        sanitize_inner_posting_spans(&mut d, &sm); // no panic, no change
        assert!(matches!(d, Directive::Open(_)));
    }
}
