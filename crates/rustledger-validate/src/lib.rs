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

pub use error::{ErrorCode, Severity, ValidationError};

use validators::{
    validate_balance, validate_close, validate_document, validate_note, validate_open,
    validate_pad, validate_transaction,
};

use rayon::prelude::*;
use rustledger_core::NaiveDate;

/// Threshold for using parallel sort. For small collections, sequential sort
/// is faster due to reduced threading overhead.
const PARALLEL_SORT_THRESHOLD: usize = 5000;
use rust_decimal::Decimal;
use rustc_hash::{FxHashMap, FxHashSet};
use rustledger_core::{BookingMethod, Directive, InternedStr, Inventory};
use rustledger_parser::{SYNTHESIZED_FILE_ID, Spanned};

/// Account state for tracking lifecycle.
#[derive(Debug, Clone)]
struct AccountState {
    /// Date opened.
    opened: NaiveDate,
    /// Date closed (if closed).
    closed: Option<NaiveDate>,
    /// Allowed currencies (empty = any).
    currencies: FxHashSet<InternedStr>,
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
}

impl Default for ValidationOptions {
    fn default() -> Self {
        Self {
            require_commodities: false,
            check_documents: true, // Python beancount validates document files by default
            warn_future_dates: false,
            document_base: None,
            document_dirs: Vec::new(),
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
}

/// Pending pad directive info.
#[derive(Debug, Clone)]
struct PendingPad {
    /// Source account for padding.
    source_account: InternedStr,
    /// Date of the pad directive.
    date: NaiveDate,
    /// Whether this pad has been used (has at least one balance assertion).
    used: bool,
}

/// Ledger state for validation.
#[derive(Debug, Default)]
pub struct LedgerState {
    /// Account states.
    accounts: FxHashMap<InternedStr, AccountState>,
    /// Account inventories.
    inventories: FxHashMap<InternedStr, Inventory>,
    /// Declared commodities.
    commodities: FxHashSet<InternedStr>,
    /// Pending pad directives (account -> list of pads).
    pending_pads: FxHashMap<InternedStr, Vec<PendingPad>>,
    /// Validation options.
    options: ValidationOptions,
    /// Track previous directive date for out-of-order detection.
    last_date: Option<NaiveDate>,
    /// Accumulated tolerances per currency from transaction amounts.
    /// Balance assertions use these with 2x multiplier (Python beancount behavior).
    tolerances: FxHashMap<InternedStr, Decimal>,
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
        self.accounts.keys().map(InternedStr::as_str)
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

/// Validate a stream of directives.
///
/// Returns a list of validation errors found.
pub fn validate(directives: &[Directive]) -> Vec<ValidationError> {
    validate_with_options(directives, ValidationOptions::default())
}

/// Validate a stream of directives with custom options.
///
/// Returns a list of validation errors and warnings found.
pub fn validate_with_options(
    directives: &[Directive],
    options: ValidationOptions,
) -> Vec<ValidationError> {
    let mut state = LedgerState::with_options(options);
    let mut errors = Vec::new();

    let today = jiff::Zoned::now().date();

    // Sort directives by date, then by type priority
    // (e.g., balance assertions before transactions on the same day)
    // Use parallel sort only for large collections (threading overhead otherwise)
    let mut sorted: Vec<&Directive> = Vec::with_capacity(directives.len());
    sorted.extend(directives.iter());
    let sort_fn = |a: &&Directive, b: &&Directive| {
        a.date()
            .cmp(&b.date())
            .then_with(|| a.priority().cmp(&b.priority()))
            .then_with(|| a.has_cost_reduction().cmp(&b.has_cost_reduction()))
    };
    if sorted.len() >= PARALLEL_SORT_THRESHOLD {
        sorted.par_sort_by(sort_fn);
    } else {
        sorted.sort_by(sort_fn);
    }

    for directive in sorted {
        let date = directive.date();

        // Check for date ordering (info only - we sort anyway)
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

        // Check for future dates if enabled
        if state.options.warn_future_dates && date > today {
            errors.push(ValidationError::new(
                ErrorCode::FutureDate,
                format!("Entry dated in the future: {date}"),
                date,
            ));
        }

        match directive {
            Directive::Open(open) => {
                validate_open(&mut state, open, &mut errors);
            }
            Directive::Close(close) => {
                validate_close(&mut state, close, &mut errors);
            }
            Directive::Transaction(txn) => {
                validate_transaction(&mut state, txn, &mut errors);
            }
            Directive::Balance(bal) => {
                validate_balance(&mut state, bal, &mut errors);
            }
            Directive::Commodity(comm) => {
                state.commodities.insert(comm.currency.clone());
            }
            Directive::Pad(pad) => {
                validate_pad(&mut state, pad, &mut errors);
            }
            Directive::Document(doc) => {
                validate_document(&state, doc, &mut errors);
            }
            Directive::Note(note) => {
                validate_note(&state, note, &mut errors);
            }
            _ => {}
        }
    }

    // Check for unused pads (E2003)
    for (target_account, pads) in &state.pending_pads {
        for pad in pads {
            if !pad.used {
                errors.push(
                    ValidationError::new(
                        ErrorCode::PadWithoutBalance,
                        "Unused Pad entry".to_string(),
                        pad.date,
                    )
                    .with_context(format!(
                        "   {} pad {} {}",
                        pad.date, target_account, pad.source_account
                    )),
                );
            }
        }
    }

    errors
}

/// Validate a stream of spanned directives with custom options.
///
/// This variant accepts `Spanned<Directive>` to preserve source location information,
/// which is propagated to any validation errors. This enables IDE-friendly error
/// messages with `file:line` information.
///
/// Returns a list of validation errors and warnings found, each with source location
/// when available.
pub fn validate_spanned_with_options(
    directives: &[Spanned<Directive>],
    options: ValidationOptions,
) -> Vec<ValidationError> {
    let mut state = LedgerState::with_options(options);
    let mut errors = Vec::new();

    let today = jiff::Zoned::now().date();

    // Sort directives by date, then by type priority
    // Use parallel sort only for large collections (threading overhead otherwise)
    let mut sorted: Vec<&Spanned<Directive>> = Vec::with_capacity(directives.len());
    sorted.extend(directives.iter());
    let sort_fn = |a: &&Spanned<Directive>, b: &&Spanned<Directive>| {
        a.value
            .date()
            .cmp(&b.value.date())
            .then_with(|| a.value.priority().cmp(&b.value.priority()))
            .then_with(|| {
                a.value
                    .has_cost_reduction()
                    .cmp(&b.value.has_cost_reduction())
            })
    };
    if sorted.len() >= PARALLEL_SORT_THRESHOLD {
        sorted.par_sort_by(sort_fn);
    } else {
        sorted.sort_by(sort_fn);
    }

    for spanned in sorted {
        let directive = &spanned.value;
        let date = directive.date();

        // Snapshot before ANY errors are pushed for this directive so the
        // downstream patching loop can enrich every error tied to this
        // directive — including the ordering / future-date checks below,
        // not just the ones produced by the per-kind validators (issue #896).
        let error_count_before = errors.len();

        // Check for date ordering (info only - we sort anyway)
        if let Some(last) = state.last_date
            && date < last
        {
            errors.push(ValidationError::with_location(
                ErrorCode::DateOutOfOrder,
                format!("Directive date {date} is before previous directive {last}"),
                date,
                spanned,
            ));
        }
        state.last_date = Some(date);

        // Check for future dates if enabled
        if state.options.warn_future_dates && date > today {
            errors.push(ValidationError::with_location(
                ErrorCode::FutureDate,
                format!("Entry dated in the future: {date}"),
                date,
                spanned,
            ));
        }

        match directive {
            Directive::Open(open) => {
                validate_open(&mut state, open, &mut errors);
            }
            Directive::Close(close) => {
                validate_close(&mut state, close, &mut errors);
            }
            Directive::Transaction(txn) => {
                validate_transaction(&mut state, txn, &mut errors);
            }
            Directive::Balance(bal) => {
                validate_balance(&mut state, bal, &mut errors);
            }
            Directive::Commodity(comm) => {
                state.commodities.insert(comm.currency.clone());
            }
            Directive::Pad(pad) => {
                validate_pad(&mut state, pad, &mut errors);
            }
            Directive::Document(doc) => {
                validate_document(&state, doc, &mut errors);
            }
            Directive::Note(note) => {
                validate_note(&state, note, &mut errors);
            }
            _ => {}
        }

        // Patch any new errors with location info from the current directive,
        // and tag plugin-synthesized directives with an advisory note so users
        // can trace errors that don't correspond to anything in their source
        // files back to a plugin (see issue #896).
        for error in errors.iter_mut().skip(error_count_before) {
            if error.span.is_none() {
                error.span = Some(spanned.span);
                error.file_id = Some(spanned.file_id);
            }
            if error.note.is_none() && spanned.file_id == SYNTHESIZED_FILE_ID {
                error.note = Some(
                    "directive was synthesized by a plugin (no source location); \
                     check your `plugin \"…\"` declarations for the responsible plugin"
                        .to_string(),
                );
            }
        }
    }

    // Check for unused pads (E2003)
    // Note: These errors won't have location info since we don't store spans in PendingPad
    for (target_account, pads) in &state.pending_pads {
        for pad in pads {
            if !pad.used {
                errors.push(
                    ValidationError::new(
                        ErrorCode::PadWithoutBalance,
                        "Unused Pad entry".to_string(),
                        pad.date,
                    )
                    .with_context(format!(
                        "   {} pad {} {}",
                        pad.date, target_account, pad.source_account
                    )),
                );
            }
        }
    }

    errors
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{
        Amount, Balance, Close, Document, NaiveDate, Open, Pad, Posting, Transaction,
    };

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_validate_account_lifecycle() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Test")
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD")))
                    .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD"))),
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(70.538), "ABC"), // 3 decimal places in transaction
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(70.542), "ABC"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100.00), "EUR"))) // EUR not allowed!
                    .with_posting(Posting::new(
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
        // Create a date in the future
        let future_date = jiff::Zoned::now()
            .date()
            .checked_add(jiff::ToSpan::days(30))
            .unwrap();

        let directives = vec![Directive::Open(Open {
            date: future_date,
            account: "Assets:Bank".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        })];

        // Without warn_future_dates option, no warnings
        let errors = validate(&directives);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::FutureDate),
            "Should not warn about future dates by default"
        );

        // With warn_future_dates option, should warn
        let options = ValidationOptions::default().with_warn_future_dates(true);
        let errors = validate_with_options(&directives, options);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::FutureDate),
            "Should warn about future dates when enabled"
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(500.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(2000.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
            .with_number_per(dec!(150))
            .with_currency("USD");

        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Stock").with_booking("STRICT".to_string()),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            // Buy 10 shares
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone()),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
            ),
            // Try to sell 15 shares (more than we have)
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell too many")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-15), "AAPL"))
                            .with_cost(cost_spec),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(2250), "USD"))),
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
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(150))
                                .with_currency("USD"),
                        ),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
            ),
            // Try to sell at $160 (no lot at this price)
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell at wrong price")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-5), "AAPL")).with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(160))
                                .with_currency("USD"),
                        ),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(800), "USD"))),
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
            .with_number_per(dec!(150))
            .with_currency("USD");

        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Stock").with_booking("STRICT".to_string()),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            // Buy at $150 on Jan 15
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy lot 1")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone().with_date(date(2024, 1, 15))),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
            ),
            // Buy again at $150 on Feb 15 (creates second lot at same price)
            Directive::Transaction(
                Transaction::new(date(2024, 2, 15), "Buy lot 2")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone().with_date(date(2024, 2, 15))),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
            ),
            // Sell with cost spec that matches both lots - STRICT falls back to FIFO
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell using FIFO fallback")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-5), "AAPL"))
                            .with_cost(cost_spec),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(750), "USD"))),
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
            .with_number_per(dec!(150))
            .with_currency("USD");

        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Stock").with_booking("FIFO".to_string()),
            ),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            // Buy 10 shares
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Buy")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                            .with_cost(cost_spec.clone()),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
            ),
            // Sell 5 shares (should succeed with FIFO)
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-5), "AAPL"))
                            .with_cost(cost_spec),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(750), "USD"))),
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(100.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
            Directive::Transaction(Transaction::new(date(2024, 1, 15), "Single").with_posting(
                Posting::new("Assets:Bank", Amount::new(dec!(100.00), "USD")),
            )),
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
                Transaction::new(date(2024, 1, 15), "Grant").with_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(100), "AAPL")).with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number_per(dec!(0))
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
                Transaction::new(date(2024, 1, 15), "Buy").with_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(100), "AAPL")).with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number_per(dec!(150))
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(20.00), "EUR"), // EUR not declared
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(20.00), "EUR"),
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(20.00), "XYZ"), // Totally made up
                    ))
                    .with_posting(Posting::new(
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50.00), "USD"),
                    ))
                    // Two postings with no amount — ambiguous interpolation
                    .with_posting(Posting {
                        account: "Expenses:Food".into(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: vec![],
                        trailing_comments: vec![],
                    })
                    .with_posting(Posting {
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
                    .with_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50.00), "USD"),
                    ))
                    .with_posting(Posting {
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
}
