//! Beancount validation rules.
//!
//! This crate implements validation checks for beancount ledgers:
//!
//! - Account lifecycle (opened before use, not used after close)
//! - Balance assertions
//! - Transaction balancing
//! - Currency constraints
//! - Booking validation (lot matching, sufficient units)
//!
//! # Error Codes
//!
//! All error codes follow the spec in `spec/validation.md`:
//!
//! | Code | Description |
//! |------|-------------|
//! | E1001 | Account not opened |
//! | E1002 | Account already open |
//! | E1003 | Account already closed |
//! | E1004 | Account close with non-zero balance |
//! | E1005 | Invalid account name |
//! | E2001 | Balance assertion failed |
//! | E2002 | Balance exceeds explicit tolerance |
//! | E2003 | Pad without subsequent balance |
//! | E2004 | Multiple pads for same balance |
//! | E3001 | Transaction does not balance |
//! | E3002 | Multiple missing amounts in transaction |
//! | E3003 | Transaction has no postings |
//! | E3004 | Transaction has single posting (warning) |
//! | E4001 | No matching lot for reduction |
//! | E4002 | Insufficient units in lot |
//! | E4003 | Ambiguous lot match |
//! | E4005 | Negative cost amount |
//! | E5001 | Currency not declared |
//! | E5002 | Currency not allowed in account |
//! | E5003 | Invalid `precision` metadata on commodity directive (warning) |
//! | E7001 | Unknown option |
//! | E7002 | Invalid option value |
//! | E7003 | Duplicate option |
//! | E8001 | Document file not found |
//! | E10001 | Date out of order (info) |
//! | E10002 | Entry dated in the future (warning) |

#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod error;
mod validators;

pub use error::{ErrorCode, Severity, ValidationError, is_advisory_only_code};
pub use validators::balance::balance_tolerance;

/// Which phase of two-phase validation to run.
///
/// The loader pipeline splits validation around booking. Checks that
/// don't need filled-in amounts (account presence, account lifecycle,
/// structural integrity, date ordering, document presence, commodity
/// metadata) run as [`Phase::Early`] AFTER synthesizer plugins
/// (`auto_accounts`, `document_discovery`) but BEFORE booking, so
/// they see elided postings to unopened accounts (with any Opens
/// plugins injected) before booking drops zero-value interpolations.
/// Checks that need filled-in amounts (currency constraints, balance
/// residuals, inventory updates, balance assertions) run as
/// [`Phase::Late`] AFTER booking AND after the regular plugin pass
/// (so cost-spec-reading plugins like `implicit_prices` see filled
/// per-unit values on the `CostNumber::PerUnitFromTotal` variant).
///
/// The pipeline is therefore:
///     sort → synth-plugins → Early → book → regular-plugins → Late → finalize
///
/// Standalone callers (LSP, tests, FFI) that don't run booking between
/// phases typically chain `Early` → `Late` → [`ValidationSession::finalize`]
/// through a single session — there is no shortcut entry point anymore.
///
/// See the "Python Compatibility Policy" section in `CLAUDE.md` for the
/// rationale on why we deliberately catch elided-zero-to-unopened-account
/// references that Python beancount silently accepts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    /// Pre-booking checks: account presence (E1001), account lifecycle,
    /// structural integrity, date ordering, future-date warnings,
    /// document presence, commodity metadata.
    Early,
    /// Post-booking checks: currency constraints on filled postings,
    /// transaction balance, balance assertions, inventory updates with
    /// lot matching / capital gains, residual checks.
    Late,
}

use validators::{
    register_open_late, validate_balance_early, validate_balance_late, validate_close,
    validate_close_late, validate_document, validate_note, validate_open, validate_pad,
    validate_transaction_early, validate_transaction_late,
};

use rayon::prelude::*;
use rustledger_core::NaiveDate;

/// Threshold for using parallel sort. For small collections, sequential sort
/// is faster due to reduced threading overhead.
const PARALLEL_SORT_THRESHOLD: usize = 5000;

/// Threshold for fanning the per-Document `Path::exists()` pre-pass
/// out via rayon. Below this, the dispatch overhead outweighs the
/// per-syscall savings.
const PARALLEL_DOC_EXISTS_THRESHOLD: usize = 64;
use rust_decimal::Decimal;
use rustc_hash::{FxHashMap, FxHashSet};
use rustledger_core::{BookingMethod, Commodity, Directive, Inventory};
use rustledger_parser::{SYNTHESIZED_FILE_ID, Spanned};

/// Account state for tracking lifecycle.
#[derive(Debug, Clone)]
struct AccountState {
    /// Date opened.
    opened: NaiveDate,
    /// Date closed (if closed).
    closed: Option<NaiveDate>,
    /// Allowed currencies (empty = any).
    currencies: FxHashSet<rustledger_core::Currency>,
    /// Booking method for this account (from `open` directive).
    /// Used by `update_inventories()` for lot matching during validation.
    booking: BookingMethod,
}

/// Validation options.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct ValidationOptions {
    /// Whether to require commodity declarations.
    pub require_commodities: bool,
    /// Whether to check if document files exist.
    pub check_documents: bool,
    /// Whether to warn about future-dated entries.
    pub warn_future_dates: bool,
    /// Base directory for resolving relative document paths.
    pub document_base: Option<std::path::PathBuf>,
    /// Document directories from `option "documents"`.
    /// Relative document paths are resolved against these directories.
    /// Paths are resolved against the ledger file's directory at load time.
    pub document_dirs: Vec<std::path::PathBuf>,
    /// Directory of each source file, indexed by `file_id` (the `u16` carried
    /// by `Spanned<Directive>`). A relative `document` path with no
    /// `document_base`/`documents` option is resolved against its own
    /// directive's source-file directory — matching Beancount, which
    /// normalizes the path at parse time, and `include`, which resolves
    /// relative to the including file. Empty for callers that don't supply
    /// source locations (the resolution then falls back to the process CWD,
    /// the pre-fix behavior).
    pub document_source_dirs: Vec<std::path::PathBuf>,
    /// Valid account type prefixes (from options like `name_assets`, `name_liabilities`, etc.).
    /// Defaults to `["Assets", "Liabilities", "Equity", "Income", "Expenses"]`.
    pub account_types: Vec<String>,
    /// Whether to infer tolerance from cost (matches Python beancount's `infer_tolerance_from_cost`).
    /// When true, tolerance for cost-based postings is calculated as: `units_quantum * cost_per_unit`.
    pub infer_tolerance_from_cost: bool,
    /// Tolerance multiplier (matches Python beancount's `inferred_tolerance_multiplier`).
    /// Default is 0.5.
    pub tolerance_multiplier: Decimal,
    /// Per-currency default tolerances (matches Python beancount's `inferred_tolerance_default`).
    /// e.g., `{"GBP": 0.004}` means GBP transactions tolerate up to 0.004 residual.
    pub inferred_tolerance_default: FxHashMap<String, Decimal>,
    /// Default booking method for accounts without an explicit method on
    /// their `open` directive. Sourced from the file-level
    /// `option "booking_method"` (or the API-level `LoadOptions`
    /// default). Mirrors the resolved `effective_method` the booking
    /// engine sees — without this, the validator's per-account
    /// lot-matching pass falls back to `BookingMethod::default()`
    /// (i.e., STRICT) regardless of the file's stated method,
    /// re-raising the very `NoMatchingLot`/`AmbiguousMatch` errors
    /// the booker just decided to skip under `NONE` (issue #1182).
    pub default_booking_method: BookingMethod,
}

impl Default for ValidationOptions {
    fn default() -> Self {
        Self {
            require_commodities: false,
            check_documents: true, // Python beancount validates document files by default
            warn_future_dates: false,
            document_base: None,
            document_dirs: Vec::new(),
            document_source_dirs: Vec::new(),
            account_types: vec![
                "Assets".to_string(),
                "Liabilities".to_string(),
                "Equity".to_string(),
                "Income".to_string(),
                "Expenses".to_string(),
            ],
            // Match Python beancount defaults
            infer_tolerance_from_cost: false,
            tolerance_multiplier: Decimal::new(5, 1), // 0.5
            inferred_tolerance_default: FxHashMap::default(),
            default_booking_method: BookingMethod::default(),
        }
    }
}

impl ValidationOptions {
    /// Set account types.
    #[must_use]
    pub fn with_account_types(mut self, types: Vec<String>) -> Self {
        self.account_types = types;
        self
    }

    /// Set whether to require commodity declarations.
    #[must_use]
    pub const fn with_require_commodities(mut self, require: bool) -> Self {
        self.require_commodities = require;
        self
    }

    /// Set whether to check if document files exist.
    #[must_use]
    pub const fn with_check_documents(mut self, check: bool) -> Self {
        self.check_documents = check;
        self
    }

    /// Set whether to warn about future-dated entries.
    #[must_use]
    pub const fn with_warn_future_dates(mut self, warn: bool) -> Self {
        self.warn_future_dates = warn;
        self
    }

    /// Set document directories (resolved paths).
    #[must_use]
    pub fn with_document_dirs(mut self, dirs: Vec<std::path::PathBuf>) -> Self {
        self.document_dirs = dirs;
        self
    }

    /// Set per-`file_id` source-file directories, used to resolve relative
    /// `document` paths against their own directive's file (see the field doc
    /// on [`ValidationOptions::document_source_dirs`]).
    #[must_use]
    pub fn with_document_source_dirs(mut self, dirs: Vec<std::path::PathBuf>) -> Self {
        self.document_source_dirs = dirs;
        self
    }

    /// Set whether to infer tolerance from cost.
    #[must_use]
    pub const fn with_infer_tolerance_from_cost(mut self, infer: bool) -> Self {
        self.infer_tolerance_from_cost = infer;
        self
    }

    /// Set tolerance multiplier.
    #[must_use]
    pub const fn with_tolerance_multiplier(mut self, multiplier: Decimal) -> Self {
        self.tolerance_multiplier = multiplier;
        self
    }

    /// Set per-currency default tolerances.
    #[must_use]
    pub fn with_inferred_tolerance_default(mut self, defaults: FxHashMap<String, Decimal>) -> Self {
        self.inferred_tolerance_default = defaults;
        self
    }

    /// Set the default booking method (file-level
    /// `option "booking_method"`). Accounts without an explicit method
    /// on their `open` directive inherit this rather than falling
    /// through to `BookingMethod::default()`.
    #[must_use]
    pub const fn with_default_booking_method(mut self, method: BookingMethod) -> Self {
        self.default_booking_method = method;
        self
    }
}

/// Pending pad directive info.
#[derive(Debug, Clone)]
struct PendingPad {
    /// Source account for padding.
    source_account: rustledger_core::Account,
    /// Date of the pad directive.
    date: NaiveDate,
    /// Currencies for which this pad has already inserted padding.
    /// A single Pad can serve multiple currency-specific Balance
    /// assertions on the same target account (e.g. `pad → balance USD
    /// → balance EUR`), so we track per-currency rather than a single
    /// `used` flag. Empty set = no balance has consumed this pad yet
    /// (drives E2003 in `check_unused_pads`).
    padded_currencies: FxHashSet<rustledger_core::Currency>,
    /// Source span + file id of the `pad` directive, when validating
    /// `Spanned` directives. Carried so `check_unused_pads` can anchor the
    /// deferred E2003 to the pad's own line instead of `<unknown>`.
    location: Option<(rustledger_parser::Span, u16)>,
}

/// Ledger state for validation.
#[derive(Debug, Default)]
pub struct LedgerState {
    /// Account states.
    accounts: FxHashMap<rustledger_core::Account, AccountState>,
    /// Account inventories.
    inventories: FxHashMap<rustledger_core::Account, Inventory>,
    /// Declared commodities.
    commodities: FxHashSet<rustledger_core::Currency>,
    /// Pending pad directives (account -> list of pads).
    pending_pads: FxHashMap<rustledger_core::Account, Vec<PendingPad>>,
    /// Validation options.
    options: ValidationOptions,
    /// Track previous directive date for out-of-order detection.
    last_date: Option<NaiveDate>,
    /// `(account, close_date)` pairs whose late-phase Close check has
    /// already fired. Guards against duplicate same-day Close
    /// directives running the non-empty-balance check twice (the early
    /// phase only rejects the duplicate with `AccountClosed`; without
    /// this set, `validate_close_late`'s `closed == Some(close.date)`
    /// guard would let both through).
    ///
    /// Keyed by `(account, date)` rather than account alone so that if
    /// reopen-after-close is ever supported, a legitimate later close on
    /// the same account still runs the inventory check.
    pub(crate) late_close_processed: FxHashSet<(rustledger_core::Account, NaiveDate)>,
    /// Per-posting identities `(file_id, span)` for which the early phase already
    /// emitted `AccountNotOpen` (E1001) on an *elided* posting to an unopened
    /// account. Elided postings must be checked early — booking interpolates
    /// them, so the account has to exist before booking (the Python
    /// #877-equivalent case). Explicit postings are deferred to the late phase
    /// so account-rewriting regular plugins (e.g. `rename_accounts`,
    /// `split_expenses`), which run after early, aren't falsely flagged on their
    /// pre-rewrite account name. The late phase consults this set to skip the
    /// *same* posting (a booked-from-elided one still unopened after plugins),
    /// keyed by source identity so a different posting that merely shares an
    /// account/date is still reported.
    pub(crate) account_not_open_early: FxHashSet<(u16, rustledger_core::Span)>,
}

impl LedgerState {
    /// Create a new ledger state.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new ledger state with options.
    #[must_use]
    pub fn with_options(options: ValidationOptions) -> Self {
        Self {
            options,
            ..Default::default()
        }
    }

    /// Set whether to require commodity declarations.
    pub const fn set_require_commodities(&mut self, require: bool) {
        self.options.require_commodities = require;
    }

    /// Set whether to check document files.
    pub const fn set_check_documents(&mut self, check: bool) {
        self.options.check_documents = check;
    }

    /// Set whether to warn about future dates.
    pub const fn set_warn_future_dates(&mut self, warn: bool) {
        self.options.warn_future_dates = warn;
    }

    /// Set the document base directory.
    pub fn set_document_base(&mut self, base: impl Into<std::path::PathBuf>) {
        self.options.document_base = Some(base.into());
    }

    /// Get the inventory for an account.
    #[must_use]
    pub fn inventory(&self, account: &str) -> Option<&Inventory> {
        self.inventories.get(account)
    }

    /// Get all account names.
    pub fn accounts(&self) -> impl Iterator<Item = &str> {
        self.accounts.keys().map(rustledger_core::Account::as_str)
    }

    /// Import option warnings from the loader and convert them to validation errors.
    ///
    /// The loader collects option warnings (E7001 unknown option, E7002 invalid value,
    /// E7003 duplicate option) during option processing. Call this method to include
    /// those warnings as validation errors.
    ///
    /// Each tuple is `(code, message)` where code is "E7001", "E7002", or "E7003".
    pub fn import_option_warnings(
        &self,
        warnings: &[(&str, &str)],
        errors: &mut Vec<ValidationError>,
    ) {
        for &(code, message) in warnings {
            let error_code = match code {
                "E7001" => ErrorCode::UnknownOption,
                "E7002" => ErrorCode::InvalidOptionValue,
                "E7003" => ErrorCode::DuplicateOption,
                _ => continue,
            };
            errors.push(ValidationError::new(
                error_code,
                message.to_string(),
                // Options don't have dates — use epoch as sentinel
                NaiveDate::default(),
            ));
        }
    }
}

/// Internal trait that lets [`validate_phase_inner`] operate over both plain
/// `Directive`s and `Spanned<Directive>`s without duplicating the loop
/// body. The two inputs differ only in whether errors get a span/file
/// stamp at the end of each iteration — encoded here as the return of
/// [`Self::span_info`].
///
/// `Sync` bound: needed so `&D` is `Send`, which `rayon::par_sort_by`
/// requires for the large-collection sort path.
trait ValidatableDirective: Sync {
    fn directive(&self) -> &Directive;
    /// Span + file id for this directive's source location, if any.
    /// Plain `Directive` always returns `None`; `Spanned<Directive>`
    /// returns the carried info.
    fn span_info(&self) -> Option<(rustledger_parser::Span, u16)>;
}

impl ValidatableDirective for Directive {
    fn directive(&self) -> &Directive {
        self
    }
    fn span_info(&self) -> Option<(rustledger_parser::Span, u16)> {
        None
    }
}

impl ValidatableDirective for Spanned<Directive> {
    fn directive(&self) -> &Directive {
        &self.value
    }
    fn span_info(&self) -> Option<(rustledger_parser::Span, u16)> {
        Some((self.span, self.file_id))
    }
}

/// Internal: run ONE validation phase over a sorted view of `directives`,
/// reading from / writing to `state`.
///
/// The same `state` is threaded through `Early` then `Late` so the
/// account/commodity/pad bookkeeping accumulated by `Early` is visible
/// to `Late`'s balance/inventory checks.
///
/// Date-ordering and future-date checks run only in `Early` (date is
/// independent of booking), so callers running both phases don't get
/// duplicate `DateOutOfOrder` / `FutureDate` warnings.
fn validate_phase_inner<D: ValidatableDirective>(
    directives: &[D],
    state: &mut LedgerState,
    phase: Phase,
    today: NaiveDate,
) -> Vec<ValidationError> {
    // Document existence is checked in the Early phase; skip the I/O
    // pre-pass when we're running Late.
    let document_exists_cache = if phase == Phase::Early {
        build_document_exists_cache(directives, &state.options)
    } else {
        FxHashMap::default()
    };

    // Reset `last_date` at the start of each phase so the date-ordering
    // check (which runs in Early) doesn't get confused by a previous
    // Late pass having advanced past every directive.
    if phase == Phase::Early {
        state.last_date = None;
    }

    let mut errors = Vec::new();

    // Sort directives by date, then by type priority
    // (e.g., balance assertions before transactions on the same day).
    // Parallel sort only for large collections (threading overhead
    // otherwise).
    let mut sorted: Vec<&D> = Vec::with_capacity(directives.len());
    sorted.extend(directives.iter());
    let sort_fn = |a: &&D, b: &&D| {
        let ad = a.directive();
        let bd = b.directive();
        ad.date()
            .cmp(&bd.date())
            .then_with(|| ad.priority().cmp(&bd.priority()))
            .then_with(|| ad.has_cost_reduction().cmp(&bd.has_cost_reduction()))
    };
    if sorted.len() >= PARALLEL_SORT_THRESHOLD {
        sorted.par_sort_by(sort_fn);
    } else {
        sorted.sort_by(sort_fn);
    }

    for d in sorted {
        let directive = d.directive();
        let date = directive.date();

        // Snapshot before ANY errors are pushed for this directive so the
        // downstream patching loop can enrich every error tied to this
        // directive — including the ordering / future-date checks below,
        // not just the ones produced by the per-kind validators
        // (issue #896). No cost for the unspanned path; the skip-then-
        // patch loop is bypassed when `span_info()` returns `None`.
        let error_count_before = errors.len();

        // Date-ordering and future-date checks only run in Early. Date
        // is independent of booking, and we don't want duplicate errors
        // when both phases iterate.
        if phase == Phase::Early {
            if let Some(last) = state.last_date
                && date < last
            {
                errors.push(ValidationError::new(
                    ErrorCode::DateOutOfOrder,
                    format!("Directive date {date} is before previous directive {last}"),
                    date,
                ));
            }
            state.last_date = Some(date);

            if state.options.warn_future_dates && date > today {
                errors.push(ValidationError::new(
                    ErrorCode::FutureDate,
                    format!("Entry dated in the future: {date}"),
                    date,
                ));
            }
        }

        match (phase, directive) {
            // ── Early-only kinds (state setup, structural / presence checks) ──
            (Phase::Early, Directive::Open(open)) => {
                validate_open(state, open, &mut errors);
            }
            // Late sees plugin-generated Opens (regular plugins run after early),
            // so the deferred account-presence check on plugin-added postings
            // recognizes them. No-op for originals already in state from early.
            (Phase::Late, Directive::Open(open)) => {
                register_open_late(state, open);
            }
            (Phase::Early, Directive::Close(close)) => {
                validate_close(state, close, &mut errors);
            }
            (Phase::Late, Directive::Close(close)) => {
                validate_close_late(state, close, &mut errors);
            }
            (Phase::Early, Directive::Commodity(comm)) => {
                state.commodities.insert(comm.currency.clone());
                validate_commodity_precision_meta(comm, &mut errors);
            }
            (Phase::Early, Directive::Pad(pad)) => {
                validate_pad(state, pad, d.span_info(), &mut errors);
            }
            (Phase::Early, Directive::Document(doc)) => {
                let file_id = d.span_info().map(|(_, fid)| fid);
                validate_document(state, doc, file_id, &document_exists_cache, &mut errors);
            }
            (Phase::Early, Directive::Note(note)) => {
                validate_note(state, note, &mut errors);
            }
            // ── Phase-split kinds ──
            (Phase::Early, Directive::Transaction(txn)) => {
                validate_transaction_early(state, txn, &mut errors);
            }
            (Phase::Late, Directive::Transaction(txn)) => {
                validate_transaction_late(state, txn, &mut errors);
            }
            (Phase::Early, Directive::Balance(bal)) => {
                validate_balance_early(state, bal, &mut errors);
            }
            (Phase::Late, Directive::Balance(bal)) => {
                validate_balance_late(state, bal, &mut errors);
            }
            // ── Everything else: skipped in this phase ──
            _ => {}
        }

        // Patch any new errors with location info from the current directive,
        // and tag plugin-synthesized directives with an advisory note so users
        // can trace errors that don't correspond to anything in their source
        // files back to a plugin (see issue #896). Only runs for the
        // spanned-input path; `Directive`'s `span_info()` returns `None`
        // so this whole block is a no-op for the CLI / unspanned callers.
        if let Some((span, file_id)) = d.span_info() {
            for error in errors.iter_mut().skip(error_count_before) {
                if error.span.is_none() {
                    error.span = Some(span);
                    error.file_id = Some(file_id);
                }
                if error.note.is_none() && file_id == SYNTHESIZED_FILE_ID {
                    error.note = Some(SYNTHESIZED_DIRECTIVE_NOTE.to_string());
                }
            }
        }
    }

    errors
}

/// Collect unused-pad errors (E2003). Called once after both phases
/// have run — pads can be marked `used` by either phase's balance
/// applications.
/// Advisory note attached to errors anchored to a plugin-synthesized directive
/// (`file_id == SYNTHESIZED_FILE_ID`), so the user can trace an error that maps
/// to nothing in their source files back to a plugin. Shared by the
/// per-directive patching loop and the deferred [`check_unused_pads`].
const SYNTHESIZED_DIRECTIVE_NOTE: &str = "directive was synthesized by a plugin (no source location \
     in your files); the responsible plugin is either an \
     enabled auto-plugin (e.g. `auto_accounts`, or document \
     discovery via `option \"documents\"`) or one of your \
     `plugin \"…\"` declarations";

fn check_unused_pads(state: &LedgerState) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    for (target_account, pads) in &state.pending_pads {
        for pad in pads {
            if pad.padded_currencies.is_empty() {
                let mut error = ValidationError::new(
                    ErrorCode::PadWithoutBalance,
                    "Unused Pad entry".to_string(),
                    pad.date,
                )
                .with_context(format!(
                    "   {} pad {} {}",
                    pad.date, target_account, pad.source_account
                ));
                // Anchor the deferred error to the pad's own line (when known)
                // so it renders with a location instead of `<unknown>:`. A pad
                // synthesized by a plugin gets the same advisory note the
                // per-directive patching loop attaches to in-phase errors, so
                // deferred and in-phase errors stay consistent.
                if let Some((span, file_id)) = pad.location {
                    error.span = Some(span);
                    error.file_id = Some(file_id);
                    if file_id == SYNTHESIZED_FILE_ID {
                        error.note = Some(SYNTHESIZED_DIRECTIVE_NOTE.to_string());
                    }
                }
                errors.push(error);
            }
        }
    }
    errors
}

/// Pre-resolve each unique `Document` directive's path so the main
/// per-directive loop can answer "does this document exist?" with a
/// hashmap lookup instead of a syscall.
///
/// Returns a `doc.path -> found` map. Resolution mirrors
/// [`validators::document::validate_document`]: absolute paths check
/// themselves; relative paths try `document_base`, then each entry of
/// `document_dirs` in order with short-circuit on first hit, then fall
/// back to the path as-is. Two `Document` directives with the same
/// `path` resolve identically, so the map dedupes naturally.
///
/// The per-document resolutions run via [`rayon::par_iter`] above
/// [`PARALLEL_DOC_EXISTS_THRESHOLD`]; below that, the dispatch
/// overhead outweighs the I/O parallelism. Crucially the unit of
/// parallel work is **one Document**, not one candidate path — this
/// preserves the short-circuit on `document_dirs` so we don't issue
/// more total syscalls than the pre-fix sequential code did. Caught
/// by Copilot review on PR #1082.
///
/// When `check_documents` is disabled the function short-circuits to
/// an empty map.
fn build_document_exists_cache<'a, D: ValidatableDirective>(
    directives: &'a [D],
    options: &ValidationOptions,
) -> FxHashMap<(&'a str, Option<u16>), bool> {
    if !options.check_documents {
        return FxHashMap::default();
    }

    // Collect unique (doc.path, file_id) pairs. Resolution depends on the
    // directive's source file (see `document_file_exists`), so the key
    // includes `file_id` — the same relative path in two differently-located
    // files can resolve to different files. Deduping still saves syscalls
    // when one (path, file) pair is referenced by multiple directives.
    let mut keys: FxHashSet<(&str, Option<u16>)> = FxHashSet::default();
    for d in directives {
        if let Directive::Document(doc) = d.directive() {
            let file_id = d.span_info().map(|(_, fid)| fid);
            keys.insert((doc.path.as_str(), file_id));
        }
    }
    let keys: Vec<(&str, Option<u16>)> = keys.into_iter().collect();

    // One closure-per-key resolves it through the same priority chain the
    // validator uses (see `document_file_exists`). Stops on the first hit so a
    // Document found in `document_dirs[0]` still costs exactly one syscall —
    // matching pre-fix sequential I/O cost, but in parallel across Documents.
    // Keys borrow `&'a str` from the `directives` slice, so neither the cache
    // build nor the validator lookup allocates a `String`.
    let resolve = |(s, file_id): (&'a str, Option<u16>)| {
        ((s, file_id), document_file_exists(s, file_id, options))
    };

    if keys.len() >= PARALLEL_DOC_EXISTS_THRESHOLD {
        keys.into_par_iter().map(resolve).collect()
    } else {
        keys.into_iter().map(resolve).collect()
    }
}

/// Resolve whether a `document` directive's file exists, using one priority
/// chain shared by the pre-pass cache and the validator:
///   1. absolute path → check as-is;
///   2. `document_base` set → resolve against it;
///   3. `documents` option dirs non-empty → found if any contains it;
///   4. otherwise → resolve against the directive's own source-file directory
///      (matching Beancount, which normalizes at parse time, and `include`),
///      falling back to the process CWD only when the source directory is
///      unknown (unspanned directives, or no source map supplied).
fn document_file_exists(path: &str, file_id: Option<u16>, options: &ValidationOptions) -> bool {
    let doc_path = std::path::Path::new(path);
    if doc_path.is_absolute() {
        doc_path.exists()
    } else if let Some(base) = &options.document_base {
        base.join(doc_path).exists()
    } else if !options.document_dirs.is_empty() {
        options
            .document_dirs
            .iter()
            .any(|dir| dir.join(doc_path).exists())
    } else if let Some(dir) = file_id.and_then(|id| options.document_source_dirs.get(id as usize)) {
        dir.join(doc_path).exists()
    } else {
        doc_path.exists()
    }
}

// ── Validation entry: [`ValidationSession`] ──────────────────────────────
//
// The single supported entry to the validator is [`ValidationSession`].
// Callers that just want "validate this list of directives, give me all
// errors" wire four calls: `ValidationSession::new(options)` (constructs
// `Pending`), `run_early(_, today)` (consumes `Pending`, produces
// `EarlyDone`), `run_late(_, today)` (consumes `EarlyDone`, produces
// `LateDone`), `finalize()` (consumes `LateDone`). The visible verbosity
// is deliberate: it surfaces the phase split so callers can choose
// where to insert booking between phases (the loader does this) or run
// all four back-to-back on already-booked input (LSP / FFI / tests do
// this).
//
// Prior versions of this crate exposed `validate()`, `validate_with_options()`,
// `validate_with_today()`, and spanned variants as free-function
// shortcuts. They were removed in the validate-phase-split refactor
// (#1115 / #1116). The runtime phase-ordering bitmask + `debug_assert!`
// were then replaced with the typestate-driven `Pending` / `EarlyDone`
// / `LateDone` markers (#1236) so the phase invariant is checked at
// compile time rather than at runtime.

/// Phantom-typed phase markers for [`ValidationSession`].
///
/// These markers track the session's lifecycle position at the type
/// level. The phase transitions [`ValidationSession::run_early`],
/// [`ValidationSession::run_late`], and [`ValidationSession::finalize`]
/// consume the session by value and produce one bound to the next
/// marker. A caller cannot call `run_late` before `run_early`, cannot
/// call either phase twice, and cannot call `finalize` before `run_late`
/// because the relevant method does not exist on the wrong-phase type.
///
/// Pre-#1236 the same invariant was enforced at runtime via a bitmask
/// on `ValidationSession` (`debug_assert!` in debug builds, silent
/// no-op in release). Compile-time enforcement closes the release-mode
/// gap and makes the contract self-documenting at call sites.
///
/// Known follow-up scope (see issue #1236): the typestate guards the
/// session lifecycle, but the directive list itself is still a plain
/// `&[Directive]` / `&[Spanned<Directive>]`. A caller can still pass
/// pre-booking directives to [`ValidationSession::<EarlyDone>::run_late`]
/// without a compile-time error. That gap requires phase markers on
/// the directive collection (mirroring `rustledger-loader`'s
/// `Directives<Phase>`), which would cross the validate/loader crate
/// boundary; deferred to a follow-up PR.
pub mod phase {
    mod sealed {
        pub trait Sealed {}
    }

    /// Marker trait for [`super::ValidationSession`] phase markers.
    /// Sealed: only the markers in this module implement it.
    pub trait SessionPhase: sealed::Sealed {}

    macro_rules! define_phase {
        ($name:ident, $doc:expr) => {
            #[doc = $doc]
            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            pub struct $name;
            impl sealed::Sealed for $name {}
            impl SessionPhase for $name {}
        };
    }

    define_phase!(
        Pending,
        "Neither phase has run yet; the session was just constructed by [`super::ValidationSession::new`]."
    );
    define_phase!(
        EarlyDone,
        "[`super::Phase::Early`] has run; [`super::ValidationSession::run_late`] is the only legal next step."
    );
    define_phase!(
        LateDone,
        "Both phases have run; [`super::ValidationSession::finalize`] is the only legal next step."
    );
}

pub use phase::{EarlyDone, LateDone, Pending, SessionPhase};

/// Stateful two-phase validation harness for callers (like the loader)
/// that need to interleave validation with other pipeline steps.
///
/// The session's phase is tracked at the type level via `P:`
/// [`SessionPhase`] (see the [`phase`] module for the marker types and
/// the rationale). The standard sequence is:
///
/// 1. [`ValidationSession::new`] returns `ValidationSession<Pending>`.
/// 2. [`run_early`](Self::run_early) consumes `Pending` and returns
///    `(ValidationSession<EarlyDone>, Vec<ValidationError>)`.
/// 3. Booking (and the post-booking plugin pass) runs externally on
///    the directive list.
/// 4. [`run_late`](Self::run_late) consumes `EarlyDone` and returns
///    `(ValidationSession<LateDone>, Vec<ValidationError>)`.
/// 5. [`finalize`](Self::finalize) consumes `LateDone` and returns the
///    deferred E2003 unused-pad warnings.
///
/// Standalone callers that don't run booking between phases (LSP,
/// FFI, tests) run all four calls back-to-back against the same
/// directive list. The verbosity is intentional: it surfaces the
/// phase split so callers explicitly choose whether to interleave
/// booking between Early and Late.
///
/// # Spanned vs. unspanned
///
/// Each transition has a `_spanned` variant
/// ([`run_early_spanned`](ValidationSession::<Pending>::run_early_spanned),
/// [`run_late_spanned`](ValidationSession::<EarlyDone>::run_late_spanned))
/// for `&[Spanned<Directive>]` input. The spanned variants preserve
/// source-location info on emitted errors so callers (LSP, loader,
/// FFI) can render `file:line:column` diagnostics directly.
///
/// # Migration from pre-#1236
///
/// Replace:
///
/// ```ignore
/// let mut session = ValidationSession::new(options);
/// let mut errors = session.run_phase(&directives, Phase::Early, today);
/// errors.extend(session.run_phase(&directives, Phase::Late, today));
/// errors.extend(session.finalize());
/// ```
///
/// with:
///
/// ```ignore
/// let session = ValidationSession::new(options);
/// let (session, mut errors) = session.run_early(&directives, today);
/// let (session, late_errors) = session.run_late(&directives, today);
/// errors.extend(late_errors);
/// errors.extend(session.finalize());
/// ```
///
/// The compile-time enforcement replaces the pre-#1236 runtime
/// `debug_assert!` + release-mode no-op for phase ordering.
///
/// # Example
///
/// ```
/// use rustledger_validate::{ValidationOptions, ValidationSession};
/// use rustledger_core::{Directive, naive_date};
///
/// let directives: Vec<Directive> = vec![];
/// let today = naive_date(2030, 1, 1).unwrap();
///
/// let session = ValidationSession::new(ValidationOptions::default());
/// let (session, mut errors) = session.run_early(&directives, today);
/// // ... booking runs here; plugins ran BEFORE Early ...
/// let (session, late_errors) = session.run_late(&directives, today);
/// errors.extend(late_errors);
/// errors.extend(session.finalize());
/// ```
pub struct ValidationSession<P: SessionPhase = Pending> {
    state: LedgerState,
    _phase: std::marker::PhantomData<P>,
}

impl ValidationSession<Pending> {
    /// Create a new session with the given validation options. The
    /// returned session is bound to the [`Pending`] marker; the only
    /// legal next step is [`run_early`](Self::run_early) (or its
    /// spanned variant).
    #[must_use]
    pub fn new(options: ValidationOptions) -> Self {
        Self {
            state: LedgerState::with_options(options),
            _phase: std::marker::PhantomData,
        }
    }

    /// Run [`Phase::Early`] over a slice of raw [`Directive`]s.
    ///
    /// `Early` runs account/structural checks that don't need filled-in
    /// amounts. The session's internal `LedgerState` is updated so
    /// [`run_late`](ValidationSession::<EarlyDone>::run_late) sees the
    /// accumulated state (open accounts, commodities, pending pads).
    ///
    /// Consumes the session and returns it bound to [`EarlyDone`]
    /// alongside the errors collected during the phase. The new phase
    /// marker prevents a second `run_early` call at compile time.
    #[must_use = "ValidationSession::run_early returns the next-phase session; dropping it loses the LedgerState built up during Early and any deferred state for Late/finalize"]
    pub fn run_early(
        self,
        directives: &[Directive],
        today: NaiveDate,
    ) -> (ValidationSession<EarlyDone>, Vec<ValidationError>) {
        self.run_phase_internal(directives, Phase::Early, today)
    }

    /// Variant of [`run_early`](Self::run_early) for
    /// `Spanned<Directive>` slices. Preserves source-location info on
    /// emitted errors.
    #[must_use = "ValidationSession::run_early_spanned returns the next-phase session; dropping it loses the LedgerState built up during Early and any deferred state for Late/finalize"]
    pub fn run_early_spanned(
        self,
        directives: &[Spanned<Directive>],
        today: NaiveDate,
    ) -> (ValidationSession<EarlyDone>, Vec<ValidationError>) {
        self.run_phase_internal(directives, Phase::Early, today)
    }

    /// Internal: run a validation phase and advance to [`EarlyDone`].
    ///
    /// Threads the underlying `LedgerState` from `Pending` into
    /// `EarlyDone` through the shared `validate_phase_inner` engine.
    /// The `phase` parameter is always [`Phase::Early`] here; it's
    /// passed through so `validate_phase_inner` can dispatch per-phase
    /// validator selection inside.
    fn run_phase_internal<D: ValidatableDirective>(
        mut self,
        directives: &[D],
        phase: Phase,
        today: NaiveDate,
    ) -> (ValidationSession<EarlyDone>, Vec<ValidationError>) {
        let errors = validate_phase_inner(directives, &mut self.state, phase, today);
        (
            ValidationSession {
                state: self.state,
                _phase: std::marker::PhantomData,
            },
            errors,
        )
    }
}

impl ValidationSession<EarlyDone> {
    /// Run [`Phase::Late`] over a slice of raw [`Directive`]s.
    ///
    /// `Late` runs balance/inventory/currency checks that need
    /// filled-in amounts. Must be called AFTER booking has run on the
    /// directive list (and after the post-booking plugin pass, if any).
    ///
    /// Consumes the session and returns it bound to [`LateDone`]
    /// alongside the errors collected during the phase. The new phase
    /// marker prevents a second `run_late` call at compile time.
    #[must_use = "ValidationSession::run_late returns the next-phase session; dropping it discards the deferred E2003 unused-pad warnings that `finalize` would surface"]
    pub fn run_late(
        self,
        directives: &[Directive],
        today: NaiveDate,
    ) -> (ValidationSession<LateDone>, Vec<ValidationError>) {
        self.run_phase_internal(directives, Phase::Late, today)
    }

    /// Variant of [`run_late`](Self::run_late) for
    /// `Spanned<Directive>` slices. Preserves source-location info on
    /// emitted errors.
    #[must_use = "ValidationSession::run_late_spanned returns the next-phase session; dropping it discards the deferred E2003 unused-pad warnings that `finalize` would surface"]
    pub fn run_late_spanned(
        self,
        directives: &[Spanned<Directive>],
        today: NaiveDate,
    ) -> (ValidationSession<LateDone>, Vec<ValidationError>) {
        self.run_phase_internal(directives, Phase::Late, today)
    }

    /// Internal: run a validation phase and advance to [`LateDone`].
    /// See [`ValidationSession::<Pending>::run_phase_internal`] for the
    /// rationale on the inner-engine dispatch shape.
    fn run_phase_internal<D: ValidatableDirective>(
        mut self,
        directives: &[D],
        phase: Phase,
        today: NaiveDate,
    ) -> (ValidationSession<LateDone>, Vec<ValidationError>) {
        let errors = validate_phase_inner(directives, &mut self.state, phase, today);
        (
            ValidationSession {
                state: self.state,
                _phase: std::marker::PhantomData,
            },
            errors,
        )
    }
}

impl ValidationSession<LateDone> {
    /// Flush deferred end-of-validation checks. Currently emits unused
    /// pad warnings (E2003). Consumes the session because deferred
    /// state is per-session.
    #[must_use]
    pub fn finalize(self) -> Vec<ValidationError> {
        check_unused_pads(&self.state)
    }
}

/// Validate the rledger-specific `precision` metadata key on a commodity directive.
///
/// Per #991, `precision: N` on a `commodity` directive sets a fixed display
/// precision for that currency. The loader silently ignores invalid values;
/// this validator is the channel that surfaces the problem to the user.
fn validate_commodity_precision_meta(comm: &Commodity, errors: &mut Vec<ValidationError>) {
    let Some(value) = comm.meta.get("precision") else {
        return;
    };
    if let Err(reason) = rustledger_core::parse_precision_meta(value) {
        errors.push(ValidationError::new(
            ErrorCode::InvalidPrecisionMetadata,
            format!(
                "invalid `precision` metadata on commodity {}: {reason}; this declaration is ignored — display precision falls back to `option \"display_precision\"` if set, otherwise to inference",
                comm.currency
            ),
            comm.date,
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{
        Amount, Balance, Close, Document, MetaValue, NaiveDate, Open, Pad, Posting, Transaction,
    };

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    /// Default "today" for tests that don't otherwise care. Set in the
    /// past relative to most fixtures so the future-date warning
    /// doesn't fire unexpectedly.
    fn test_today() -> NaiveDate {
        date(2030, 1, 1)
    }

    /// Test-only convenience: run both phases through a fresh
    /// `ValidationSession` and return the combined error list.
    /// Mirrors the deleted public `validate()` shortcut. Kept inside
    /// `mod tests` so it stays out of the crate's public API.
    fn validate(directives: &[Directive]) -> Vec<ValidationError> {
        validate_with_options(directives, ValidationOptions::default())
    }

    /// Test-only convenience: same as [`validate`] but with caller-
    /// supplied [`ValidationOptions`].
    fn validate_with_options(
        directives: &[Directive],
        options: ValidationOptions,
    ) -> Vec<ValidationError> {
        validate_with_today(directives, options, test_today())
    }

    /// Test-only convenience: same as [`validate_with_options`] but with
    /// caller-supplied "today" date (covers tests that exercise
    /// future-date / date-ordering behavior).
    fn validate_with_today(
        directives: &[Directive],
        options: ValidationOptions,
        today: NaiveDate,
    ) -> Vec<ValidationError> {
        let session = ValidationSession::new(options);
        let (session, mut errors) = session.run_early(directives, today);
        let (session, late_errors) = session.run_late(directives, today);
        errors.extend(late_errors);
        errors.extend(session.finalize());
        errors
    }

    #[test]
    fn test_validate_account_lifecycle() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Test")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-100), "USD"),
                    )),
            ),
        ];

        let errors = validate(&directives);

        // Should have error: Income:Salary not opened
        assert!(errors
            .iter()
            .any(|e| e.code == ErrorCode::AccountNotOpen && e.message.contains("Income:Salary")));
    }

    #[test]
    fn test_validate_account_used_before_open() {
        let directives = vec![
            Directive::Transaction(
                Transaction::new(date(2024, 1, 1), "Test")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-100), "USD"),
                    )),
            ),
            Directive::Open(Open::new(date(2024, 1, 15), "Assets:Bank")),
        ];

        let errors = validate(&directives);

        assert!(errors.iter().any(|e| e.code == ErrorCode::AccountNotOpen));
    }

    #[test]
    fn test_validate_account_used_after_close() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Close(Close::new(date(2024, 6, 1), "Assets:Bank")),
            Directive::Transaction(
                Transaction::new(date(2024, 7, 1), "Test")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(50), "USD"),
                    )),
            ),
        ];

        let errors = validate(&directives);

        assert!(errors.iter().any(|e| e.code == ErrorCode::AccountClosed));
    }

    #[test]
    fn test_validate_balance_assertion() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-1000.00), "USD"),
                    )),
            ),
            Directive::Balance(Balance::new(
                date(2024, 1, 16),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let errors = validate(&directives);
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn test_validate_balance_assertion_failed() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-1000.00), "USD"),
                    )),
            ),
            Directive::Balance(Balance::new(
                date(2024, 1, 16),
                "Assets:Bank",
                Amount::new(dec!(500.00), "USD"), // Wrong!
            )),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::BalanceAssertionFailed)
        );
    }

    /// Test that balance assertions use inferred tolerance (matching Python beancount).
    ///
    /// Tolerance is derived from the balance assertion amount's precision, then multiplied by 2.
    /// See: <https://github.com/beancount/beancount/blob/master/beancount/ops/balance.py>
    /// Balance assertion with 2 decimal places: tolerance = 0.5 * 2 * 10^(-2) = 0.01.
    #[test]
    fn test_validate_balance_assertion_within_tolerance() {
        // Actual balance is 70.538, assertion is 70.53 (2 decimal places)
        // Tolerance is derived from balance assertion: 0.5 * 2 * 10^(-2) = 0.01
        // Difference is 0.008, which is less than tolerance (0.01)
        // This should PASS (matching Python beancount behavior from issue #251)
        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Bank").with_currencies(vec!["ABC".into()]),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Misc")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(70.538), "ABC"), // 3 decimal places in transaction
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Misc",
                        Amount::new(dec!(-70.538), "ABC"),
                    )),
            ),
            Directive::Balance(Balance::new(
                date(2024, 1, 16),
                "Assets:Bank",
                Amount::new(dec!(70.53), "ABC"), // 2 decimal places → tolerance = 0.01, diff = 0.008 < 0.01
            )),
        ];

        let errors = validate(&directives);
        assert!(
            errors.is_empty(),
            "Balance within tolerance should pass: {errors:?}"
        );
    }

    /// Test that balance assertions fail when exceeding tolerance.
    #[test]
    fn test_validate_balance_assertion_exceeds_tolerance() {
        // Actual balance is 70.538, assertion is 70.53 with explicit precision
        // Balance assertion has 2 decimal places: tolerance = 0.5 * 2 * 10^(-2) = 0.01
        // Difference is 0.012, which exceeds tolerance
        // This should FAIL
        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Bank").with_currencies(vec!["ABC".into()]),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Misc")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(70.542), "ABC"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Misc",
                        Amount::new(dec!(-70.542), "ABC"),
                    )),
            ),
            Directive::Balance(Balance::new(
                date(2024, 1, 16),
                "Assets:Bank",
                Amount::new(dec!(70.53), "ABC"), // 2 decimal places → tolerance = 0.01, diff = 0.012 > 0.01
            )),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::BalanceAssertionFailed),
            "Balance exceeding tolerance should fail"
        );
    }

    #[test]
    fn test_validate_unbalanced_transaction() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Unbalanced")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(40.00), "USD"),
                    )), // Missing $10
            ),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::TransactionUnbalanced)
        );
    }

    #[test]
    fn test_validate_currency_not_allowed() {
        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Bank").with_currencies(vec!["USD".into()]),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Test")
                    .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(100.00), "EUR"))) // EUR not allowed!
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-100.00), "EUR"),
                    )),
            ),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::CurrencyNotAllowed)
        );
    }

    #[test]
    fn test_validate_future_date_warning() {
        // Anchor "today" so this test isn't time-dependent. The
        // directive is 30 days after the anchor — unambiguously in
        // the future from `today`'s perspective.
        let today = date(2024, 1, 1);
        let future_date = today.checked_add(jiff::ToSpan::days(30)).unwrap();

        let directives = vec![Directive::Open(Open {
            date: future_date,
            account: "Assets:Bank".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        })];

        // Without warn_future_dates option, no warnings
        let errors = validate_with_today(&directives, ValidationOptions::default(), today);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::FutureDate),
            "Should not warn about future dates by default"
        );

        // With warn_future_dates option, should warn
        let options = ValidationOptions::default().with_warn_future_dates(true);
        let errors = validate_with_today(&directives, options, today);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::FutureDate),
            "Should warn about future dates when enabled"
        );
    }

    /// `validate_with_today` is the LSP-friendly entry point that
    /// accepts the "today" date as a parameter instead of calling
    /// `jiff::Zoned::now()` internally. Verify it threads the parameter
    /// through correctly: with `today` set BEFORE the directive's date,
    /// the directive is in the future relative to `today`; with `today`
    /// set AFTER, the directive is in the past.
    #[test]
    fn test_validate_with_today_threads_today_parameter() {
        let directives = vec![Directive::Open(Open {
            date: date(2024, 6, 15),
            account: "Assets:Bank".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        })];
        let options = ValidationOptions::default().with_warn_future_dates(true);

        // today = 2024-01-01 → directive at 2024-06-15 is in the future
        let errors = validate_with_today(&directives, options.clone(), date(2024, 1, 1));
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::FutureDate),
            "with today=2024-01-01 the 2024-06-15 directive must trigger a FutureDate warning"
        );

        // today = 2025-01-01 → directive at 2024-06-15 is in the past
        let errors = validate_with_today(&directives, options, date(2025, 1, 1));
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::FutureDate),
            "with today=2025-01-01 the 2024-06-15 directive must not trigger a FutureDate warning"
        );
    }

    #[test]
    fn test_validate_document_not_found() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Document(Document {
                date: date(2024, 1, 15),
                account: "Assets:Bank".into(),
                path: "/nonexistent/path/to/document.pdf".to_string(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }),
        ];

        // With default options (check_documents: true), should error
        let errors = validate(&directives);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Should check documents by default"
        );

        // With check_documents disabled, should not error
        let options = ValidationOptions::default().with_check_documents(false);
        let errors = validate_with_options(&directives, options);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Should not report missing document when disabled"
        );
    }

    #[test]
    fn test_validate_document_account_not_open() {
        let directives = vec![Directive::Document(Document {
            date: date(2024, 1, 15),
            account: "Assets:Unknown".into(),
            path: "receipt.pdf".to_string(),
            tags: vec![],
            links: vec![],
            meta: Default::default(),
        })];

        let errors = validate(&directives);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::AccountNotOpen),
            "Should error for document on unopened account"
        );
    }

    #[test]
    fn test_validate_document_relative_path_in_document_dirs() {
        // Use a unique filename so the CWD fallback (triggered when
        // document_dirs is empty) doesn't pick up a same-named file that
        // happens to exist in the test runner's working directory.
        let filename = "rustledger_test_889_relative_receipt.pdf";
        let dir = tempfile::tempdir().unwrap();
        let doc_subdir = dir.path().join("documents");
        std::fs::create_dir_all(&doc_subdir).unwrap();
        std::fs::write(doc_subdir.join(filename), "test").unwrap();

        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Document(Document {
                date: date(2024, 1, 15),
                account: "Assets:Bank".into(),
                path: filename.to_string(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }),
        ];

        // Without document_dirs, should fail
        let errors = validate(&directives);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Should error when document_dirs not set"
        );

        // With document_dirs pointing to the directory, should pass
        let options = ValidationOptions::default().with_document_dirs(vec![doc_subdir]);
        let errors = validate_with_options(&directives, options);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Should find document in document_dirs: {errors:?}"
        );
    }

    #[test]
    fn test_validate_document_relative_path_not_found_in_dirs() {
        // Use a unique filename — see comment in the sibling test above.
        let filename = "rustledger_test_889_nonexistent.pdf";
        let dir = tempfile::tempdir().unwrap();
        let doc_subdir = dir.path().join("documents");
        std::fs::create_dir_all(&doc_subdir).unwrap();

        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Document(Document {
                date: date(2024, 1, 15),
                account: "Assets:Bank".into(),
                path: filename.to_string(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }),
        ];

        let options = ValidationOptions::default().with_document_dirs(vec![doc_subdir]);
        let errors = validate_with_options(&directives, options);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Should error when file not found in any document_dir"
        );
    }

    #[test]
    fn test_validate_document_absolute_path_ignores_document_dirs() {
        let filename = "rustledger_test_889_absolute_receipt.pdf";
        let dir = tempfile::tempdir().unwrap();
        let doc_subdir = dir.path().join("documents");
        std::fs::create_dir_all(&doc_subdir).unwrap();
        std::fs::write(doc_subdir.join(filename), "test").unwrap();

        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Document(Document {
                date: date(2024, 1, 15),
                account: "Assets:Bank".into(),
                path: doc_subdir.join(filename).display().to_string(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }),
        ];

        // Absolute path should work regardless of document_dirs
        let options = ValidationOptions::default()
            .with_document_dirs(vec![std::path::PathBuf::from("/nonexistent/path")]);
        let errors = validate_with_options(&directives, options);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Absolute path should work even with wrong document_dirs: {errors:?}"
        );
    }

    /// Regression test for the parallel `Path::exists()` pre-pass.
    /// Constructs enough Document directives (mix of found + missing)
    /// to cross `PARALLEL_DOC_EXISTS_THRESHOLD` and confirms that:
    ///
    /// 1. The found documents validate without `DocumentNotFound`.
    /// 2. The missing documents still report `DocumentNotFound`.
    /// 3. The error-context "searched: ..." message survives the
    ///    cache-routed code path (was constructed inline before).
    #[test]
    fn test_validate_document_parallel_batch_check() {
        let dir = tempfile::tempdir().unwrap();
        let doc_subdir = dir.path().join("docs");
        std::fs::create_dir_all(&doc_subdir).unwrap();

        // PARALLEL_DOC_EXISTS_THRESHOLD = 64. Generate 100 documents:
        // even-numbered exist, odd-numbered don't.
        let mut directives: Vec<Directive> =
            vec![Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank"))];
        for i in 0..100 {
            let filename = format!("receipt_{i}.pdf");
            if i % 2 == 0 {
                std::fs::write(doc_subdir.join(&filename), "x").unwrap();
            }
            directives.push(Directive::Document(Document {
                date: date(2024, 1, 15),
                account: "Assets:Bank".into(),
                path: filename,
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }));
        }

        let options = ValidationOptions::default().with_document_dirs(vec![doc_subdir]);
        let errors = validate_with_options(&directives, options);

        let not_found_count = errors
            .iter()
            .filter(|e| e.code == ErrorCode::DocumentNotFound)
            .count();
        assert_eq!(
            not_found_count, 50,
            "exactly 50 of 100 documents should error as not-found"
        );

        // Spot-check that the error context message still mentions the
        // searched document_dirs path (it's built from
        // state.options.document_dirs, independently of the cache).
        let example = errors
            .iter()
            .find(|e| e.code == ErrorCode::DocumentNotFound)
            .expect("should have at least one not-found error");
        assert!(
            example
                .context
                .as_deref()
                .is_some_and(|c| c.contains("searched")),
            "error context should mention the searched dirs, got: {:?}",
            example.context
        );
    }

    #[test]
    fn test_error_code_is_warning() {
        assert!(!ErrorCode::AccountNotOpen.is_warning());
        assert!(!ErrorCode::DocumentNotFound.is_warning());
        assert!(ErrorCode::FutureDate.is_warning());
    }

    #[test]
    fn test_validate_pad_basic() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let errors = validate(&directives);
        // Should have no errors - pad should satisfy the balance
        assert!(errors.is_empty(), "Pad should satisfy balance: {errors:?}");
    }

    #[test]
    fn test_validate_pad_with_existing_balance() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            // Add some initial transactions
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Initial deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(500.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-500.00), "USD"),
                    )),
            ),
            // Pad to reach the target balance
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"), // Need to add 500 more
            )),
        ];

        let errors = validate(&directives);
        // Should have no errors - pad should add the missing 500
        assert!(
            errors.is_empty(),
            "Pad should add missing amount: {errors:?}"
        );
    }

    #[test]
    fn test_validate_pad_account_not_open() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            // Assets:Bank not opened
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::AccountNotOpen && e.message.contains("Assets:Bank")),
            "Should error for pad on unopened account"
        );
    }

    #[test]
    fn test_validate_pad_source_not_open() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            // Equity:Opening not opened
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
        ];

        let errors = validate(&directives);
        assert!(
            errors.iter().any(
                |e| e.code == ErrorCode::AccountNotOpen && e.message.contains("Equity:Opening")
            ),
            "Should error for pad with unopened source account"
        );
    }

    #[test]
    fn test_validate_pad_negative_adjustment() {
        // Test that pad can reduce a balance too
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            // Add more than needed
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Big deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(2000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-2000.00), "USD"),
                    )),
            ),
            // Pad to reach a lower target
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"), // Need to remove 1000
            )),
        ];

        let errors = validate(&directives);
        assert!(
            errors.is_empty(),
            "Pad should handle negative adjustment: {errors:?}"
        );
    }

    #[test]
    fn test_validate_insufficient_units() {
        use rustledger_core::CostSpec;

        let cost_spec = CostSpec::empty()
            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(150) })
            .with_currency("USD");

        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Stock").with_booking("STRICT".to_string()),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            // Buy 10 shares
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone()),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(-1500), "USD"),
                    )),
            ),
            // Try to sell 15 shares (more than we have)
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell too many")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-15), "AAPL"))
                            .with_cost(cost_spec),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(2250), "USD"),
                    )),
            ),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::InsufficientUnits),
            "Should error for insufficient units: {errors:?}"
        );
    }

    #[test]
    fn test_validate_no_matching_lot() {
        use rustledger_core::CostSpec;

        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Stock").with_booking("STRICT".to_string()),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            // Buy at $150
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                            CostSpec::empty()
                                .with_number(rustledger_core::CostNumber::PerUnit {
                                    value: dec!(150),
                                })
                                .with_currency("USD"),
                        ),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(-1500), "USD"),
                    )),
            ),
            // Try to sell at $160 (no lot at this price)
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell at wrong price")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-5), "AAPL")).with_cost(
                            CostSpec::empty()
                                .with_number(rustledger_core::CostNumber::PerUnit {
                                    value: dec!(160),
                                })
                                .with_currency("USD"),
                        ),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(800), "USD"),
                    )),
            ),
        ];

        let errors = validate(&directives);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::NoMatchingLot),
            "Should error for no matching lot: {errors:?}"
        );
    }

    #[test]
    fn test_validate_multiple_lot_match_uses_fifo() {
        // In Python beancount, when multiple lots match the same cost spec,
        // STRICT mode falls back to FIFO order rather than erroring.
        use rustledger_core::CostSpec;

        let cost_spec = CostSpec::empty()
            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(150) })
            .with_currency("USD");

        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Stock").with_booking("STRICT".to_string()),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            // Buy at $150 on Jan 15
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy lot 1")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone().with_date(date(2024, 1, 15))),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(-1500), "USD"),
                    )),
            ),
            // Buy again at $150 on Feb 15 (creates second lot at same price)
            Directive::Transaction(
                Transaction::new(date(2024, 2, 15), "Buy lot 2")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone().with_date(date(2024, 2, 15))),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(-1500), "USD"),
                    )),
            ),
            // Sell with cost spec that matches both lots - STRICT falls back to FIFO
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell using FIFO fallback")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-5), "AAPL"))
                            .with_cost(cost_spec),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(750), "USD"),
                    )),
            ),
        ];

        let errors = validate(&directives);
        // Filter out only booking errors - balance may or may not match
        let booking_errors: Vec<_> = errors
            .iter()
            .filter(|e| {
                matches!(
                    e.code,
                    ErrorCode::InsufficientUnits
                        | ErrorCode::NoMatchingLot
                        | ErrorCode::AmbiguousLotMatch
                )
            })
            .collect();
        assert!(
            booking_errors.is_empty(),
            "Should not have booking errors when multiple lots match (FIFO fallback): {booking_errors:?}"
        );
    }

    #[test]
    fn test_validate_successful_booking() {
        use rustledger_core::CostSpec;

        let cost_spec = CostSpec::empty()
            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(150) })
            .with_currency("USD");

        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Stock").with_booking("FIFO".to_string()),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            // Buy 10 shares
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone()),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(-1500), "USD"),
                    )),
            ),
            // Sell 5 shares (should succeed with FIFO)
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-5), "AAPL"))
                            .with_cost(cost_spec),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(750), "USD"),
                    )),
            ),
        ];

        let errors = validate(&directives);
        // Filter out any balance errors (we're testing booking only)
        let booking_errors: Vec<_> = errors
            .iter()
            .filter(|e| {
                matches!(
                    e.code,
                    ErrorCode::InsufficientUnits
                        | ErrorCode::NoMatchingLot
                        | ErrorCode::AmbiguousLotMatch
                )
            })
            .collect();
        assert!(
            booking_errors.is_empty(),
            "Should have no booking errors: {booking_errors:?}"
        );
    }

    #[test]
    fn test_validate_account_already_open() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 6, 1), "Assets:Bank")), // Duplicate!
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::AccountAlreadyOpen),
            "Should error for duplicate open: {errors:?}"
        );
    }

    #[test]
    fn test_validate_account_close_not_empty() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(100.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-100.00), "USD"),
                    )),
            ),
            Directive::Close(Close::new(date(2024, 12, 31), "Assets:Bank")), // Still has 100 USD
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::AccountCloseNotEmpty),
            "Should warn for closing account with balance: {errors:?}"
        );
    }

    #[test]
    fn test_validate_no_postings_allowed() {
        // Python beancount allows transactions with no postings (metadata-only).
        // We match this behavior.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(Transaction::new(date(2024, 1, 15), "Empty")),
        ];

        let errors = validate(&directives);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::NoPostings),
            "Should NOT error for transaction with no postings: {errors:?}"
        );
    }

    #[test]
    fn test_validate_single_posting() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Single").with_synthesized_posting(
                    Posting::new("Assets:Bank", Amount::new(dec!(100.00), "USD")),
                ),
            ),
        ];

        let errors = validate(&directives);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::SinglePosting),
            "Should warn for transaction with single posting: {errors:?}"
        );
        // Check it's a warning not error
        assert!(ErrorCode::SinglePosting.is_warning());
    }

    #[test]
    fn test_validate_single_posting_zero_cost_no_warning() {
        // A transaction with a single posting that has {0 USD} cost should not
        // warn about single posting — the counterpart was removed during
        // zero-cost interpolation.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stock")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Grant").with_synthesized_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(100), "AAPL")).with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(0) })
                            .with_currency("USD"),
                    ),
                ),
            ),
        ];

        let errors = validate(&directives);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::SinglePosting),
            "Should NOT warn for zero-cost single posting: {errors:?}"
        );
    }

    #[test]
    fn test_validate_single_posting_nonzero_cost_still_warns() {
        // A single posting with a NON-zero cost should still warn
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stock")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy").with_synthesized_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(100), "AAPL")).with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(150) })
                            .with_currency("USD"),
                    ),
                ),
            ),
        ];

        let errors = validate(&directives);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::SinglePosting),
            "Should warn for single posting with non-zero cost: {errors:?}"
        );
    }

    #[test]
    fn test_validate_pad_without_balance() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            // No balance assertion follows!
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::PadWithoutBalance),
            "Should error for pad without subsequent balance: {errors:?}"
        );
    }

    #[test]
    fn test_validate_multiple_pads_for_balance() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")), // Second pad!
            Directive::Balance(Balance::new(
                date(2024, 1, 3),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::MultiplePadForBalance),
            "Should error for multiple pads before balance: {errors:?}"
        );
    }

    #[test]
    fn test_e2004_fires_after_prior_balance_consumed_a_pad() {
        // Pinning the post-#1116-self-review semantics: a successfully
        // applied pad gets drained from `pending_pads`, so a later
        // sequence of two unused pads correctly triggers E2004 even
        // when an earlier pad already served a previous balance.
        // Pre-#1116 the `!any(used)` clause suppressed this case.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            // First Pad → Balance pair: pad gets used, then drained.
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(100.00), "USD"),
            )),
            // Two more unused pads, then a balance — this is the
            // ambiguous case E2004 is meant to flag.
            Directive::Pad(Pad::new(date(2024, 2, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 2, 2), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 2, 3),
                "Assets:Bank",
                Amount::new(dec!(200.00), "USD"),
            )),
        ];

        let errors = validate(&directives);
        let multi_pad_count = errors
            .iter()
            .filter(|e| e.code == ErrorCode::MultiplePadForBalance)
            .count();
        assert_eq!(
            multi_pad_count, 1,
            "E2004 must fire exactly once on the second balance; got {errors:?}"
        );
    }

    #[test]
    fn test_pad_serves_multi_currency_balances_on_same_day() {
        // A single Pad must remain available to subsequent Balance
        // assertions in DIFFERENT currencies on the same target
        // account. Pre-#1116 the `any(used)` clause kept the pad
        // visible after the first currency consumed it. The retain
        // change in 05fcba8b broke this by dropping the pad as soon
        // as the first currency was padded.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            // Two balances on the same day, different currencies.
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(100.00), "USD"),
            )),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(50.00), "EUR"),
            )),
        ];

        let errors = validate(&directives);
        assert!(
            !errors
                .iter()
                .any(|e| e.code == ErrorCode::BalanceAssertionFailed),
            "pad should serve both USD and EUR; got {errors:?}"
        );
        assert!(
            !errors
                .iter()
                .any(|e| e.code == ErrorCode::PadWithoutBalance),
            "pad serves at least one balance; should not be E2003; got {errors:?}"
        );
    }

    #[test]
    fn test_same_day_pad_does_not_apply_to_same_day_balance() {
        // Python beancount semantics: a Pad on date D only takes
        // effect for the NEXT Balance dated strictly after D. So a
        // same-day Pad+Balance leaves the Balance unpadded (regular
        // assertion runs) AND the Pad orphaned (E2003).
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(100.00), "USD"),
            )),
        ];

        let errors = validate(&directives);
        // The pad is ignored, so the balance assertion runs against
        // the unpadded inventory (0 USD) and fails against the
        // asserted 100 USD.
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::BalanceAssertionFailed),
            "same-day pad should NOT apply; balance fails on bare inventory; got {errors:?}"
        );
        // The pad never serves a balance, so E2003 fires.
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::PadWithoutBalance),
            "same-day pad never consumed; expected E2003; got {errors:?}"
        );
    }

    #[test]
    fn test_future_pad_does_not_apply_to_earlier_balance() {
        // The date-filter in `validate_balance_late` must prevent a
        // later-dated Pad from being silently consumed by an earlier
        // Balance — a regression that would surface as the wrong
        // source account being debited. Regression test for commit
        // 83369fd8.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(0.00), "USD"),
            )),
            Directive::Pad(Pad::new(date(2024, 6, 1), "Assets:Bank", "Equity:Opening")),
        ];

        let errors = validate(&directives);
        // The future pad must NOT consume the earlier balance; balance
        // asserts 0 USD against an empty inventory, which matches.
        assert!(
            !errors
                .iter()
                .any(|e| e.code == ErrorCode::BalanceAssertionFailed),
            "future pad should not influence earlier balance; got {errors:?}"
        );
        // The pad never gets used, so E2003 fires.
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::PadWithoutBalance),
            "future-dated pad without subsequent balance should fire E2003; got {errors:?}"
        );
    }

    #[test]
    fn test_error_severity() {
        // Errors
        assert_eq!(ErrorCode::AccountNotOpen.severity(), Severity::Error);
        assert_eq!(ErrorCode::TransactionUnbalanced.severity(), Severity::Error);
        assert_eq!(ErrorCode::NoMatchingLot.severity(), Severity::Error);

        // Warnings
        assert_eq!(ErrorCode::FutureDate.severity(), Severity::Warning);
        assert_eq!(ErrorCode::SinglePosting.severity(), Severity::Warning);
        assert_eq!(
            ErrorCode::AccountCloseNotEmpty.severity(),
            Severity::Warning
        );

        // Info
        assert_eq!(ErrorCode::DateOutOfOrder.severity(), Severity::Info);
    }

    #[test]
    fn test_validate_invalid_account_name() {
        // Test invalid root type
        let directives = vec![Directive::Open(Open::new(date(2024, 1, 1), "Invalid:Bank"))];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::InvalidAccountName),
            "Should error for invalid account root: {errors:?}"
        );
    }

    #[test]
    fn test_validate_account_lowercase_component() {
        // Test lowercase component (must start with uppercase or digit)
        let directives = vec![Directive::Open(Open::new(date(2024, 1, 1), "Assets:bank"))];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::InvalidAccountName),
            "Should error for lowercase component: {errors:?}"
        );
    }

    #[test]
    fn test_validate_valid_account_names() {
        // Valid account names should not error
        let valid_names = [
            "Assets:Bank",
            "Assets:Bank:Checking",
            "Liabilities:CreditCard",
            "Equity:Opening-Balances",
            "Income:Salary2024",
            "Expenses:Food:Restaurant",
            "Assets:401k",     // Component starting with digit
            "Assets:沪深300",  // CJK characters
            "Assets:Café",     // Non-ASCII letter (é)
            "Assets:日本銀行", // Full non-ASCII component
            "Assets:Капитал",  // Cyrillic sub-account
        ];

        for name in valid_names {
            let directives = vec![Directive::Open(Open::new(date(2024, 1, 1), name))];

            let errors = validate(&directives);
            let name_errors: Vec<_> = errors
                .iter()
                .filter(|e| e.code == ErrorCode::InvalidAccountName)
                .collect();
            assert!(
                name_errors.is_empty(),
                "Should accept valid account name '{name}': {name_errors:?}"
            );
        }
    }

    // =========================================================================
    // Error code coverage tests (spring 2026 audit)
    // =========================================================================

    #[test]
    fn test_e2002_balance_exceeds_explicit_tolerance() {
        // E2002: When a balance directive specifies an explicit tolerance and the
        // actual balance exceeds it, we should get BalanceToleranceExceeded.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-1000.00), "USD"),
                    )),
            ),
            // Balance assertion with explicit tolerance of 0.01,
            // but actual is 1000.00 vs expected 999.00 (difference = 1.00)
            Directive::Balance(
                Balance::new(
                    date(2024, 1, 16),
                    "Assets:Bank",
                    Amount::new(dec!(999.00), "USD"),
                )
                .with_tolerance(dec!(0.01)),
            ),
        ];

        let errors = validate(&directives);

        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::BalanceToleranceExceeded),
            "Expected E2002 BalanceToleranceExceeded, got: {errors:?}"
        );
    }

    #[test]
    fn test_e2002_balance_within_explicit_tolerance_passes() {
        // When within explicit tolerance, no error should be raised
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-1000.00), "USD"),
                    )),
            ),
            // Balance assertion with tolerance of 5.00, difference is only 1.00
            Directive::Balance(
                Balance::new(
                    date(2024, 1, 16),
                    "Assets:Bank",
                    Amount::new(dec!(999.00), "USD"),
                )
                .with_tolerance(dec!(5.00)),
            ),
        ];

        let errors = validate(&directives);

        assert!(
            !errors
                .iter()
                .any(|e| e.code == ErrorCode::BalanceToleranceExceeded
                    || e.code == ErrorCode::BalanceAssertionFailed),
            "Expected no balance errors, got: {errors:?}"
        );
    }

    #[test]
    fn test_e5001_undeclared_currency() {
        // E5001: When require_commodities=true, using a currency without a
        // commodity directive should raise UndeclaredCurrency.
        use rustledger_core::Commodity;

        let directives = vec![
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "USD")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Lunch")
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(20.00), "EUR"), // EUR not declared
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-20.00), "EUR"),
                    )),
            ),
        ];

        let options = ValidationOptions::default().with_require_commodities(true);
        let errors = validate_with_options(&directives, options);

        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::UndeclaredCurrency),
            "Expected E5001 UndeclaredCurrency for EUR, got: {errors:?}"
        );
    }

    #[test]
    fn test_e5001_declared_currency_passes() {
        // When the currency is declared, no E5001 error
        use rustledger_core::Commodity;

        let directives = vec![
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "USD")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "EUR")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Lunch")
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(20.00), "EUR"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-20.00), "EUR"),
                    )),
            ),
        ];

        let options = ValidationOptions::default().with_require_commodities(true);
        let errors = validate_with_options(&directives, options);

        assert!(
            !errors
                .iter()
                .any(|e| e.code == ErrorCode::UndeclaredCurrency),
            "Expected no E5001 errors, got: {errors:?}"
        );
    }

    #[test]
    fn test_e5001_not_raised_without_require_commodities() {
        // Without require_commodities=true, undeclared currencies are fine
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Lunch")
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(20.00), "XYZ"), // Totally made up
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-20.00), "XYZ"),
                    )),
            ),
        ];

        let errors = validate(&directives);

        assert!(
            !errors
                .iter()
                .any(|e| e.code == ErrorCode::UndeclaredCurrency),
            "Should not raise E5001 without require_commodities, got: {errors:?}"
        );
    }

    #[test]
    fn test_e3002_multiple_missing_amounts() {
        // E3002: Multiple postings with missing amounts is ambiguous
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Drinks")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Lunch")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50.00), "USD"),
                    ))
                    // Two postings with no amount — ambiguous interpolation
                    .with_synthesized_posting(Posting {
                        account: "Expenses:Food".into(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: vec![],
                        trailing_comments: vec![],
                    })
                    .with_synthesized_posting(Posting {
                        account: "Expenses:Drinks".into(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: vec![],
                        trailing_comments: vec![],
                    }),
            ),
        ];

        let errors = validate(&directives);

        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::MultipleInterpolation),
            "Expected E3002 MultipleInterpolation, got: {errors:?}"
        );
    }

    #[test]
    fn test_e3002_single_missing_amount_ok() {
        // A single missing amount is fine (can be interpolated)
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Lunch")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting {
                        account: "Expenses:Food".into(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: vec![],
                        trailing_comments: vec![],
                    }),
            ),
        ];

        let errors = validate(&directives);

        assert!(
            !errors
                .iter()
                .any(|e| e.code == ErrorCode::MultipleInterpolation),
            "Should not raise E3002 with single missing amount, got: {errors:?}"
        );
    }

    #[test]
    fn test_e7001_unknown_option() {
        // E7001: import_option_warnings converts loader warnings to validation errors
        let state = LedgerState::new();
        let mut errors = Vec::new();

        state.import_option_warnings(&[("E7001", "Invalid option \"bogus_option\"")], &mut errors);

        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].code, ErrorCode::UnknownOption);
        assert!(errors[0].message.contains("bogus_option"));
    }

    #[test]
    fn test_e7002_invalid_option_value() {
        let state = LedgerState::new();
        let mut errors = Vec::new();

        state.import_option_warnings(
            &[("E7002", "Invalid leaf account name: 'not-valid'")],
            &mut errors,
        );

        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].code, ErrorCode::InvalidOptionValue);
    }

    #[test]
    fn test_e7003_duplicate_option() {
        let state = LedgerState::new();
        let mut errors = Vec::new();

        state.import_option_warnings(
            &[("E7003", "Option \"title\" can only be specified once")],
            &mut errors,
        );

        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].code, ErrorCode::DuplicateOption);
    }

    // ----- E5003: invalid `precision` metadata on commodity (issue #991) ----

    fn commodity_with_precision(value: MetaValue) -> Directive {
        let mut meta = rustledger_core::Metadata::default();
        meta.insert("precision".into(), value);
        Directive::Commodity(
            rustledger_core::Commodity::new(date(2024, 1, 1), "USD").with_meta(meta),
        )
    }

    #[test]
    fn precision_meta_valid_integer_emits_no_warning() {
        let directives = vec![commodity_with_precision(MetaValue::Number(dec!(2)))];
        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .all(|e| e.code != ErrorCode::InvalidPrecisionMetadata),
            "valid precision must not produce a warning, got: {errors:?}"
        );
    }

    #[test]
    fn precision_meta_zero_is_valid() {
        let directives = vec![commodity_with_precision(MetaValue::Number(dec!(0)))];
        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .all(|e| e.code != ErrorCode::InvalidPrecisionMetadata)
        );
    }

    #[test]
    fn precision_meta_negative_emits_e5003() {
        let directives = vec![commodity_with_precision(MetaValue::Number(dec!(-1)))];
        let errors = validate(&directives);
        let warnings: Vec<_> = errors
            .iter()
            .filter(|e| e.code == ErrorCode::InvalidPrecisionMetadata)
            .collect();
        assert_eq!(warnings.len(), 1, "expected one E5003");
        assert_eq!(warnings[0].code.severity(), Severity::Warning);
        assert!(warnings[0].message.contains("non-negative"));
    }

    #[test]
    fn precision_meta_non_integer_emits_e5003() {
        let directives = vec![commodity_with_precision(MetaValue::Number(dec!(2.5)))];
        let errors = validate(&directives);
        let warnings: Vec<_> = errors
            .iter()
            .filter(|e| e.code == ErrorCode::InvalidPrecisionMetadata)
            .collect();
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].message.contains("integer"));
    }

    #[test]
    fn precision_meta_string_value_emits_e5003() {
        let directives = vec![commodity_with_precision(MetaValue::String("abc".into()))];
        let errors = validate(&directives);
        let warnings: Vec<_> = errors
            .iter()
            .filter(|e| e.code == ErrorCode::InvalidPrecisionMetadata)
            .collect();
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].message.contains("string"));
    }

    #[test]
    fn precision_meta_out_of_u32_range_emits_e5003() {
        // 2^33 — too big for u32.
        let directives = vec![commodity_with_precision(MetaValue::Number(dec!(
            8589934592
        )))];
        let errors = validate(&directives);
        let warnings: Vec<_> = errors
            .iter()
            .filter(|e| e.code == ErrorCode::InvalidPrecisionMetadata)
            .collect();
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].message.contains("exceeds"));
    }

    #[test]
    fn precision_meta_valid_then_invalid_same_currency_warns_only_once() {
        // Two commodity directives for USD: first valid (2), second invalid
        // (-1). The validator must surface the bad one as E5003 even though
        // the loader pins the earlier valid override. This pairs with the
        // loader-side test `precision_metadata_valid_then_invalid_keeps_first`.
        let directives = vec![
            commodity_with_precision(MetaValue::Number(dec!(2))),
            commodity_with_precision(MetaValue::Number(dec!(-1))),
        ];
        let warnings: Vec<_> = validate(&directives)
            .into_iter()
            .filter(|e| e.code == ErrorCode::InvalidPrecisionMetadata)
            .collect();
        assert_eq!(
            warnings.len(),
            1,
            "exactly one E5003 expected (only the invalid declaration)"
        );
        assert!(warnings[0].message.contains("non-negative"));
    }

    #[test]
    fn precision_meta_e5003_is_warning_severity() {
        // Pin the severity classification — InvalidPrecisionMetadata must be
        // a warning (loading does not fail). Used by CLI / LSP renderers to
        // pick the right color and exit code.
        assert_eq!(
            ErrorCode::InvalidPrecisionMetadata.severity(),
            Severity::Warning
        );
        assert_eq!(ErrorCode::InvalidPrecisionMetadata.code(), "E5003");
    }

    // ─── Phase-split (refs #1115) ────────────────────────────────────────

    /// `validate_early` must catch E1001 on a posting to an account that
    /// was never opened — even when the posting is elided (no units), so
    /// the loader's pre-booking validation can see it before booking
    /// drops zero-value interpolations. This is the load-bearing test
    /// for the rustledger#877 strictness deviation from Python beancount.
    #[test]
    fn test_validate_early_emits_e1001_on_elided_posting() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Zero to unopened")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(0.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::auto("Expenses:NeverOpened")),
            ),
        ];

        let session = ValidationSession::new(ValidationOptions::default());
        let (_session, errors) = session.run_early(&directives, date(2026, 1, 1));

        assert!(
            errors.iter().any(|e| e.code == ErrorCode::AccountNotOpen
                && e.to_string().contains("Expenses:NeverOpened")),
            "early phase must emit E1001 on elided posting to unopened account; got: {errors:?}"
        );
    }

    /// An *explicit* posting to an unopened account is reported in the LATE
    /// phase (deferred from early so account-rewriting plugins run first) —
    /// exactly once across phases, never duplicated.
    #[test]
    fn test_validate_late_does_not_duplicate_e1001() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "To unopened")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Expenses:NeverOpened",
                        Amount::new(dec!(-100), "USD"),
                    )),
            ),
        ];

        let session = ValidationSession::new(ValidationOptions::default());
        let (session, early) = session.run_early(&directives, date(2026, 1, 1));
        let (_session, late) = session.run_late(&directives, date(2026, 1, 1));

        let early_e1001 = early
            .iter()
            .filter(|e| e.code == ErrorCode::AccountNotOpen)
            .count();
        let late_e1001 = late
            .iter()
            .filter(|e| e.code == ErrorCode::AccountNotOpen)
            .count();

        assert_eq!(
            early_e1001, 0,
            "explicit posting: early phase defers E1001 to late; got: {early:?}"
        );
        assert_eq!(
            late_e1001, 1,
            "explicit posting: late phase emits E1001 exactly once; got: {late:?}"
        );
    }

    /// The legacy convenience entry `validate()` chains `Early` then
    /// `Late` internally. Its error list must match what you'd get from
    /// explicitly running both phases against the same input — so
    /// existing callers (LSP, FFI, direct test code) don't observe a
    /// behavior change after the phase split.
    #[test]
    fn test_validate_chained_matches_explicit_phases() {
        // A mix that exercises both phases: an Open, a Transaction with
        // an unopened account, a same-day Balance that needs late-phase
        // inventory state.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Mixed")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(50), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-50), "USD"),
                    )),
            ),
            Directive::Balance(Balance::new(
                date(2024, 1, 16),
                "Assets:Bank",
                Amount::new(dec!(50), "USD"),
            )),
        ];

        // Legacy single-call.
        let chained = validate(&directives);

        // Explicit phase split.
        let session = ValidationSession::new(ValidationOptions::default());
        let (session, mut explicit) = session.run_early(&directives, date(2026, 1, 1));
        let (session, late_errs) = session.run_late(&directives, date(2026, 1, 1));
        explicit.extend(late_errs);
        explicit.extend(session.finalize());

        // Same set of (code, date, message) tuples in the same order.
        // String comparison sidesteps the ValidationError struct's
        // non-pub fields and matches what users actually see.
        let chained_strs: Vec<String> = chained.iter().map(ToString::to_string).collect();
        let explicit_strs: Vec<String> = explicit.iter().map(ToString::to_string).collect();
        assert_eq!(
            chained_strs, explicit_strs,
            "legacy `validate()` and explicit `Early` + `Late` must produce identical error lists"
        );
    }

    #[test]
    fn test_phase_order_early_then_late_then_finalize() {
        // Pin the error emission ordering across phases:
        //   1. Early-phase errors  (E1001 AccountNotOpen)
        //   2. Late-phase errors   (E2002 BalanceAssertionFailed)
        //   3. Finalize errors     (E2003 PadWithoutBalance)
        // Stable ordering matters for LSP diagnostics and CLI output;
        // accidental reordering of the pipeline would surface here.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Other")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            // Early: posting to unopened Income:Salary → E1001.
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "early")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-100), "USD"),
                    )),
            ),
            // Finalize: pad on Assets:Other has no following Balance → E2003.
            Directive::Pad(Pad::new(
                date(2024, 1, 10),
                "Assets:Other",
                "Equity:Opening",
            )),
            // Late: wrong amount → E2002. (Posted balance is 100 USD.)
            Directive::Balance(Balance::new(
                date(2024, 2, 1),
                "Assets:Bank",
                Amount::new(dec!(999), "USD"),
            )),
        ];

        let errors = validate(&directives);
        let codes: Vec<ErrorCode> = errors.iter().map(|e| e.code).collect();

        let early_pos = codes
            .iter()
            .position(|c| *c == ErrorCode::AccountNotOpen)
            .unwrap_or_else(|| panic!("expected E1001 in {codes:?}"));
        let late_pos = codes
            .iter()
            .position(|c| *c == ErrorCode::BalanceAssertionFailed)
            .unwrap_or_else(|| panic!("expected E2002 in {codes:?}"));
        let finalize_pos = codes
            .iter()
            .position(|c| *c == ErrorCode::PadWithoutBalance)
            .unwrap_or_else(|| panic!("expected E2003 in {codes:?}"));

        assert!(
            early_pos < late_pos,
            "early-phase errors must precede late-phase; got {codes:?}"
        );
        assert!(
            late_pos < finalize_pos,
            "late-phase errors must precede finalize; got {codes:?}"
        );
    }

    #[test]
    fn test_duplicate_same_day_close_emits_close_not_empty_once() {
        // Regression for the Copilot inline review on PR #1116: two
        // Close directives for the same account on the same date used
        // to bypass the `validate_close_late` guard, double-emitting
        // `AccountCloseNotEmpty`. The early phase rejects the duplicate
        // with `AccountClosed`; the late phase should run the
        // non-empty-balance check exactly once.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            // Leave a non-zero balance on Assets:Bank so the late-phase
            // non-empty check actually fires.
            Directive::Transaction(
                Transaction::new(date(2024, 1, 10), "leave residue")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(50), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-50), "USD"),
                    )),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Close(Close::new(date(2024, 6, 1), "Assets:Bank")),
            Directive::Close(Close::new(date(2024, 6, 1), "Assets:Bank")),
        ];

        let errors = validate(&directives);
        let close_not_empty_count = errors
            .iter()
            .filter(|e| e.code == ErrorCode::AccountCloseNotEmpty)
            .count();
        assert_eq!(
            close_not_empty_count, 1,
            "AccountCloseNotEmpty must fire exactly once for duplicate same-day closes; got {errors:?}"
        );
        // And the duplicate still gets its early-phase `AccountClosed` flag.
        let account_closed_count = errors
            .iter()
            .filter(|e| e.code == ErrorCode::AccountClosed)
            .count();
        assert_eq!(
            account_closed_count, 1,
            "duplicate close should still report AccountClosed once; got {errors:?}"
        );
    }

    // Pre-#1236 these were two `#[should_panic]` tests that asserted
    // the `debug_assert!` calls in `ValidationSession::check_phase_ordering`
    // fired on out-of-order or duplicate phase calls. The typestate
    // refactor moved that enforcement to the type system: calling
    // `run_late` before `run_early`, or either phase twice, is now a
    // compile error rather than a runtime panic.
    //
    // We deliberately do not keep the runtime panic-tests as a parallel
    // safety net: there is no longer a runtime code path that could
    // panic, so a runtime test would simply be unreachable.

    /// Compile-time pin for the typestate ordering: `run_late` is not
    /// callable on a `ValidationSession<Pending>` (the only `new()`
    /// output). This test is type-level only and runs at compile time.
    ///
    /// Coverage is limited to the happy-path direction: the helper
    /// functions below assert that the by-value transitions resolve to
    /// the documented next-phase types. Compiler rejection of the
    /// inverse misuse (`run_late` on `Pending`, double-`run_early`,
    /// `finalize` on `EarlyDone`, etc.) is exercised today by ordinary
    /// development — the missing methods produce E0599 the moment a
    /// caller tries them. Pinning these as `trybuild`-style `compile_fail`
    /// tests is a candidate follow-up; the dependency adds rustc-version-
    /// sensitive `.stderr` snapshots that aren't justified by the
    /// already-structural type-system enforcement.
    #[test]
    fn typestate_pins_phase_ordering_at_compile_time() {
        // A `Pending` session has `run_early` but not `run_late`. The
        // following commented-out lines would fail to compile if
        // uncommented; they're documentation, not executable code.
        //
        //     let session = ValidationSession::new(ValidationOptions::default());
        //     let (_, _) = session.run_late(&[], date(2024, 1, 1));
        //     // error[E0599]: no method named `run_late` found for struct
        //     //               `ValidationSession<Pending>` in the current scope
        //
        // The helper functions below pin the happy-path transitions
        // via signatures the type-checker validates at compile time.
        fn _expect_pending_returns_early(
            s: ValidationSession<Pending>,
        ) -> ValidationSession<EarlyDone> {
            let (s, _errors) = s.run_early(&[] as &[Directive], date(2024, 1, 1));
            s
        }
        fn _expect_early_returns_late(
            s: ValidationSession<EarlyDone>,
        ) -> ValidationSession<LateDone> {
            let (s, _errors) = s.run_late(&[] as &[Directive], date(2024, 1, 1));
            s
        }
        fn _expect_late_finalizes(s: ValidationSession<LateDone>) -> Vec<ValidationError> {
            s.finalize()
        }
    }
}
