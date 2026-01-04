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
//! | E2003 | Pad without subsequent balance |
//! | E2004 | Multiple pads for same balance |
//! | E3001 | Transaction does not balance |
//! | E3002 | Multiple missing amounts in transaction |
//! | E3003 | Transaction has no postings |
//! | E3004 | Transaction has single posting (warning) |
//! | E4001 | No matching lot for reduction |
//! | E4002 | Insufficient units in lot |
//! | E4003 | Ambiguous lot match |
//! | E4004 | Reduction would create negative inventory |
//! | E5001 | Currency not declared |
//! | E5002 | Currency not allowed in account |
//! | E6001 | Duplicate metadata key |
//! | E6002 | Invalid metadata value |
//! | E7001 | Unknown option |
//! | E7002 | Invalid option value |
//! | E7003 | Duplicate option |
//! | E8001 | Document file not found |
//! | E10001 | Date out of order (info) |
//! | E10002 | Entry dated in the future (warning) |

#![forbid(unsafe_code)]
#![warn(missing_docs)]

use chrono::{Local, NaiveDate};
use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Balance, BookingMethod, Close, Directive, Document, Inventory, Open, Pad, Position,
    Transaction,
};
use std::collections::{HashMap, HashSet};
use std::path::Path;
use thiserror::Error;

/// Validation error codes.
///
/// Error codes follow the spec in `spec/validation.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    // === Account Errors (E1xxx) ===
    /// E1001: Account used before it was opened.
    AccountNotOpen,
    /// E1002: Account already open (duplicate open directive).
    AccountAlreadyOpen,
    /// E1003: Account used after it was closed.
    AccountClosed,
    /// E1004: Account close with non-zero balance.
    AccountCloseNotEmpty,
    /// E1005: Invalid account name.
    InvalidAccountName,

    // === Balance Errors (E2xxx) ===
    /// E2001: Balance assertion failed.
    BalanceAssertionFailed,
    /// E2003: Pad without subsequent balance assertion.
    PadWithoutBalance,
    /// E2004: Multiple pads for same balance assertion.
    MultiplePadForBalance,

    // === Transaction Errors (E3xxx) ===
    /// E3001: Transaction does not balance.
    TransactionUnbalanced,
    /// E3002: Multiple postings missing amounts for same currency.
    MultipleInterpolation,
    /// E3003: Transaction has no postings.
    NoPostings,
    /// E3004: Transaction has single posting (warning).
    SinglePosting,

    // === Booking Errors (E4xxx) ===
    /// E4001: No matching lot for reduction.
    NoMatchingLot,
    /// E4002: Insufficient units in lot for reduction.
    InsufficientUnits,
    /// E4003: Ambiguous lot match in STRICT mode.
    AmbiguousLotMatch,
    /// E4004: Reduction would create negative inventory.
    NegativeInventory,

    // === Currency Errors (E5xxx) ===
    /// E5001: Currency not declared (when strict mode enabled).
    UndeclaredCurrency,
    /// E5002: Currency not allowed in account.
    CurrencyNotAllowed,

    // === Metadata Errors (E6xxx) ===
    /// E6001: Duplicate metadata key.
    DuplicateMetadataKey,
    /// E6002: Invalid metadata value type.
    InvalidMetadataValue,

    // === Option Errors (E7xxx) ===
    /// E7001: Unknown option name.
    UnknownOption,
    /// E7002: Invalid option value.
    InvalidOptionValue,
    /// E7003: Duplicate non-repeatable option.
    DuplicateOption,

    // === Document Errors (E8xxx) ===
    /// E8001: Document file not found.
    DocumentNotFound,

    // === Date Errors (E10xxx) ===
    /// E10001: Date out of order (info only).
    DateOutOfOrder,
    /// E10002: Entry dated in the future (warning).
    FutureDate,
}

impl ErrorCode {
    /// Get the error code string (e.g., "E1001").
    #[must_use]
    pub const fn code(&self) -> &'static str {
        match self {
            // Account errors
            Self::AccountNotOpen => "E1001",
            Self::AccountAlreadyOpen => "E1002",
            Self::AccountClosed => "E1003",
            Self::AccountCloseNotEmpty => "E1004",
            Self::InvalidAccountName => "E1005",
            // Balance errors
            Self::BalanceAssertionFailed => "E2001",
            Self::PadWithoutBalance => "E2003",
            Self::MultiplePadForBalance => "E2004",
            // Transaction errors
            Self::TransactionUnbalanced => "E3001",
            Self::MultipleInterpolation => "E3002",
            Self::NoPostings => "E3003",
            Self::SinglePosting => "E3004",
            // Booking errors
            Self::NoMatchingLot => "E4001",
            Self::InsufficientUnits => "E4002",
            Self::AmbiguousLotMatch => "E4003",
            Self::NegativeInventory => "E4004",
            // Currency errors
            Self::UndeclaredCurrency => "E5001",
            Self::CurrencyNotAllowed => "E5002",
            // Metadata errors
            Self::DuplicateMetadataKey => "E6001",
            Self::InvalidMetadataValue => "E6002",
            // Option errors
            Self::UnknownOption => "E7001",
            Self::InvalidOptionValue => "E7002",
            Self::DuplicateOption => "E7003",
            // Document errors
            Self::DocumentNotFound => "E8001",
            // Date errors
            Self::DateOutOfOrder => "E10001",
            Self::FutureDate => "E10002",
        }
    }

    /// Check if this is a warning (not an error).
    #[must_use]
    pub const fn is_warning(&self) -> bool {
        matches!(
            self,
            Self::FutureDate
                | Self::SinglePosting
                | Self::AccountCloseNotEmpty
                | Self::DateOutOfOrder
        )
    }

    /// Check if this is just informational.
    #[must_use]
    pub const fn is_info(&self) -> bool {
        matches!(self, Self::DateOutOfOrder)
    }

    /// Get the severity level.
    #[must_use]
    pub const fn severity(&self) -> Severity {
        if self.is_info() {
            Severity::Info
        } else if self.is_warning() {
            Severity::Warning
        } else {
            Severity::Error
        }
    }
}

/// Severity level for validation messages.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Severity {
    /// Ledger is invalid.
    Error,
    /// Suspicious but valid.
    Warning,
    /// Informational only.
    Info,
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.code())
    }
}

/// A validation error.
#[derive(Debug, Clone, Error)]
#[error("[{code}] {message}")]
pub struct ValidationError {
    /// Error code.
    pub code: ErrorCode,
    /// Error message.
    pub message: String,
    /// Date of the directive that caused the error.
    pub date: NaiveDate,
    /// Additional context.
    pub context: Option<String>,
}

impl ValidationError {
    /// Create a new validation error.
    #[must_use]
    pub fn new(code: ErrorCode, message: impl Into<String>, date: NaiveDate) -> Self {
        Self {
            code,
            message: message.into(),
            date,
            context: None,
        }
    }

    /// Add context to this error.
    #[must_use]
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }
}

/// Account state for tracking lifecycle.
#[derive(Debug, Clone)]
struct AccountState {
    /// Date opened.
    opened: NaiveDate,
    /// Date closed (if closed).
    closed: Option<NaiveDate>,
    /// Allowed currencies (empty = any).
    currencies: HashSet<String>,
    /// Booking method (stored for future use in booking validation).
    #[allow(dead_code)]
    booking: BookingMethod,
}

/// Validation options.
#[derive(Debug, Clone, Default)]
pub struct ValidationOptions {
    /// Whether to require commodity declarations.
    pub require_commodities: bool,
    /// Whether to check if document files exist.
    pub check_documents: bool,
    /// Whether to warn about future-dated entries.
    pub warn_future_dates: bool,
    /// Base directory for resolving relative document paths.
    pub document_base: Option<std::path::PathBuf>,
}

/// Pending pad directive info.
#[derive(Debug, Clone)]
struct PendingPad {
    /// Source account for padding.
    source_account: String,
    /// Date of the pad directive.
    date: NaiveDate,
}

/// Ledger state for validation.
#[derive(Debug, Default)]
pub struct LedgerState {
    /// Account states.
    accounts: HashMap<String, AccountState>,
    /// Account inventories.
    inventories: HashMap<String, Inventory>,
    /// Declared commodities.
    commodities: HashSet<String>,
    /// Pending pad directives (account -> list of pads).
    pending_pads: HashMap<String, Vec<PendingPad>>,
    /// Validation options.
    options: ValidationOptions,
    /// Track previous directive date for out-of-order detection.
    last_date: Option<NaiveDate>,
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
    pub fn set_require_commodities(&mut self, require: bool) {
        self.options.require_commodities = require;
    }

    /// Set whether to check document files.
    pub fn set_check_documents(&mut self, check: bool) {
        self.options.check_documents = check;
    }

    /// Set whether to warn about future dates.
    pub fn set_warn_future_dates(&mut self, warn: bool) {
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
        self.accounts.keys().map(String::as_str)
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

    let today = Local::now().date_naive();

    // Sort directives by date
    let mut sorted: Vec<&Directive> = directives.iter().collect();
    sorted.sort_by_key(|d| d.date());

    for directive in sorted {
        let date = directive.date();

        // Check for date ordering (info only - we sort anyway)
        if let Some(last) = state.last_date {
            if date < last {
                errors.push(ValidationError::new(
                    ErrorCode::DateOutOfOrder,
                    format!("Directive date {date} is before previous directive {last}"),
                    date,
                ));
            }
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
            _ => {}
        }
    }

    // Check for unused pads (E2003)
    for (account, pads) in &state.pending_pads {
        for pad in pads {
            errors.push(
                ValidationError::new(
                    ErrorCode::PadWithoutBalance,
                    format!("Pad directive for {account} has no subsequent balance assertion"),
                    pad.date,
                )
                .with_context(format!("source account: {}", pad.source_account)),
            );
        }
    }

    errors
}

/// Valid account root types in beancount.
const VALID_ACCOUNT_ROOTS: &[&str] = &["Assets", "Liabilities", "Equity", "Income", "Expenses"];

/// Validate an account name according to beancount rules.
/// Returns None if valid, or Some(reason) if invalid.
fn validate_account_name(account: &str) -> Option<String> {
    if account.is_empty() {
        return Some("account name is empty".to_string());
    }

    let parts: Vec<&str> = account.split(':').collect();
    if parts.is_empty() {
        return Some("account name has no components".to_string());
    }

    // Check root account type
    let root = parts[0];
    if !VALID_ACCOUNT_ROOTS.contains(&root) {
        return Some(format!(
            "account must start with one of: {}",
            VALID_ACCOUNT_ROOTS.join(", ")
        ));
    }

    // Check each component
    for (i, part) in parts.iter().enumerate() {
        if part.is_empty() {
            return Some(format!("component {} is empty", i + 1));
        }

        // First character must be uppercase letter or digit
        let first_char = part.chars().next().unwrap();
        if !first_char.is_ascii_uppercase() && !first_char.is_ascii_digit() {
            return Some(format!(
                "component '{part}' must start with uppercase letter or digit"
            ));
        }

        // Remaining characters: letters, numbers, dashes
        for c in part.chars().skip(1) {
            if !c.is_ascii_alphanumeric() && c != '-' {
                return Some(format!(
                    "component '{part}' contains invalid character '{c}'"
                ));
            }
        }
    }

    None // Valid
}

fn validate_open(state: &mut LedgerState, open: &Open, errors: &mut Vec<ValidationError>) {
    // Validate account name format
    if let Some(reason) = validate_account_name(&open.account) {
        errors.push(
            ValidationError::new(
                ErrorCode::InvalidAccountName,
                format!("Invalid account name \"{}\": {}", open.account, reason),
                open.date,
            )
            .with_context(open.account.clone()),
        );
        // Continue anyway to allow further validation
    }

    // Check if already open
    if let Some(existing) = state.accounts.get(&open.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountAlreadyOpen,
            format!(
                "Account {} is already open (opened on {})",
                open.account, existing.opened
            ),
            open.date,
        ));
        return;
    }

    let booking = open
        .booking
        .as_ref()
        .and_then(|b| b.parse::<BookingMethod>().ok())
        .unwrap_or_default();

    state.accounts.insert(
        open.account.clone(),
        AccountState {
            opened: open.date,
            closed: None,
            currencies: open.currencies.iter().cloned().collect(),
            booking,
        },
    );

    state
        .inventories
        .insert(open.account.clone(), Inventory::new());
}

fn validate_close(state: &mut LedgerState, close: &Close, errors: &mut Vec<ValidationError>) {
    match state.accounts.get_mut(&close.account) {
        Some(account_state) => {
            if account_state.closed.is_some() {
                errors.push(ValidationError::new(
                    ErrorCode::AccountClosed,
                    format!("Account {} already closed", close.account),
                    close.date,
                ));
            } else {
                // Check if account has non-zero balance (warning)
                if let Some(inv) = state.inventories.get(&close.account) {
                    if !inv.is_empty() {
                        let positions: Vec<String> = inv
                            .positions()
                            .iter()
                            .map(|p| format!("{} {}", p.units.number, p.units.currency))
                            .collect();
                        errors.push(
                            ValidationError::new(
                                ErrorCode::AccountCloseNotEmpty,
                                format!(
                                    "Cannot close account {} with non-zero balance",
                                    close.account
                                ),
                                close.date,
                            )
                            .with_context(format!("balance: {}", positions.join(", "))),
                        );
                    }
                }
                account_state.closed = Some(close.date);
            }
        }
        None => {
            errors.push(ValidationError::new(
                ErrorCode::AccountNotOpen,
                format!("Account {} was never opened", close.account),
                close.date,
            ));
        }
    }
}

fn validate_transaction(
    state: &mut LedgerState,
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) {
    // Check transaction structure
    if txn.postings.is_empty() {
        errors.push(ValidationError::new(
            ErrorCode::NoPostings,
            "Transaction must have at least one posting".to_string(),
            txn.date,
        ));
        return; // No point checking further
    }

    if txn.postings.len() == 1 {
        errors.push(ValidationError::new(
            ErrorCode::SinglePosting,
            "Transaction has only one posting".to_string(),
            txn.date,
        ));
        // Continue validation - this is just a warning
    }

    // Check each posting
    for posting in &txn.postings {
        // Check account lifecycle
        match state.accounts.get(&posting.account) {
            Some(account_state) => {
                if txn.date < account_state.opened {
                    errors.push(ValidationError::new(
                        ErrorCode::AccountNotOpen,
                        format!(
                            "Account {} used on {} but not opened until {}",
                            posting.account, txn.date, account_state.opened
                        ),
                        txn.date,
                    ));
                }

                if let Some(closed) = account_state.closed {
                    if txn.date >= closed {
                        errors.push(ValidationError::new(
                            ErrorCode::AccountClosed,
                            format!(
                                "Account {} used on {} but was closed on {}",
                                posting.account, txn.date, closed
                            ),
                            txn.date,
                        ));
                    }
                }

                // Check currency constraints (only for complete amounts)
                if let Some(units) = posting.amount() {
                    if !account_state.currencies.is_empty()
                        && !account_state.currencies.contains(&units.currency)
                    {
                        errors.push(ValidationError::new(
                            ErrorCode::CurrencyNotAllowed,
                            format!(
                                "Currency {} not allowed in account {}",
                                units.currency, posting.account
                            ),
                            txn.date,
                        ));
                    }

                    // Check commodity declaration
                    if state.options.require_commodities
                        && !state.commodities.contains(&units.currency)
                    {
                        errors.push(ValidationError::new(
                            ErrorCode::UndeclaredCurrency,
                            format!("Currency {} not declared", units.currency),
                            txn.date,
                        ));
                    }
                }
            }
            None => {
                errors.push(ValidationError::new(
                    ErrorCode::AccountNotOpen,
                    format!("Account {} was never opened", posting.account),
                    txn.date,
                ));
            }
        }
    }

    // Check transaction balance
    let residuals = rustledger_booking::calculate_residual(txn);
    for (currency, residual) in residuals {
        // Use a default tolerance of 0.005 for now
        if residual.abs() > Decimal::new(5, 3) {
            errors.push(ValidationError::new(
                ErrorCode::TransactionUnbalanced,
                format!("Transaction does not balance: residual {residual} {currency}"),
                txn.date,
            ));
        }
    }

    // Update inventories with booking validation (only for complete amounts)
    for posting in &txn.postings {
        if let Some(units) = posting.amount() {
            if let Some(inv) = state.inventories.get_mut(&posting.account) {
                // Get booking method for this account
                let booking_method = state
                    .accounts
                    .get(&posting.account)
                    .map(|a| a.booking)
                    .unwrap_or_default();

                // Check if this is a reduction (negative units with cost)
                let is_reduction = units.number.is_sign_negative() && posting.cost.is_some();

                if is_reduction {
                    // For reductions, use booking to match against existing lots
                    // The reduce method expects negative amounts (opposite sign from positions)
                    let reduction_units = units.clone();

                    // Try to reduce from inventory
                    match inv.reduce(&reduction_units, posting.cost.as_ref(), booking_method) {
                        Ok(_) => {}
                        Err(rustledger_core::BookingError::InsufficientUnits {
                            requested,
                            available,
                            ..
                        }) => {
                            errors.push(
                                ValidationError::new(
                                    ErrorCode::InsufficientUnits,
                                    format!(
                                        "Insufficient units in {}: requested {}, available {}",
                                        posting.account, requested, available
                                    ),
                                    txn.date,
                                )
                                .with_context(format!("currency: {}", units.currency)),
                            );
                        }
                        Err(rustledger_core::BookingError::NoMatchingLot { currency, .. }) => {
                            errors.push(
                                ValidationError::new(
                                    ErrorCode::NoMatchingLot,
                                    format!(
                                        "No matching lot for {} in {}",
                                        currency, posting.account
                                    ),
                                    txn.date,
                                )
                                .with_context(format!("cost spec: {:?}", posting.cost)),
                            );
                        }
                        Err(rustledger_core::BookingError::AmbiguousMatch {
                            currency,
                            num_matches,
                        }) => {
                            errors.push(
                                ValidationError::new(
                                    ErrorCode::AmbiguousLotMatch,
                                    format!(
                                        "Ambiguous lot match for {}: {} lots match in {}",
                                        currency, num_matches, posting.account
                                    ),
                                    txn.date,
                                )
                                .with_context(
                                    "Specify cost, date, or label to disambiguate".to_string(),
                                ),
                            );
                        }
                        Err(rustledger_core::BookingError::CurrencyMismatch { .. }) => {
                            // This shouldn't happen in normal validation
                        }
                    }
                } else {
                    // For additions, just add the position
                    let position = if let Some(cost_spec) = &posting.cost {
                        if let Some(cost) = cost_spec.resolve(units.number, txn.date) {
                            rustledger_core::Position::with_cost(units.clone(), cost)
                        } else {
                            rustledger_core::Position::simple(units.clone())
                        }
                    } else {
                        rustledger_core::Position::simple(units.clone())
                    };

                    inv.add(position);
                }
            }
        }
    }
}

fn validate_pad(state: &mut LedgerState, pad: &Pad, errors: &mut Vec<ValidationError>) {
    // Check that the target account exists
    if !state.accounts.contains_key(&pad.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Pad target account {} was never opened", pad.account),
            pad.date,
        ));
        return;
    }

    // Check that the source account exists
    if !state.accounts.contains_key(&pad.source_account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Pad source account {} was never opened", pad.source_account),
            pad.date,
        ));
        return;
    }

    // Add to pending pads list for this account
    let pending_pad = PendingPad {
        source_account: pad.source_account.clone(),
        date: pad.date,
    };
    state
        .pending_pads
        .entry(pad.account.clone())
        .or_default()
        .push(pending_pad);
}

fn validate_balance(state: &mut LedgerState, bal: &Balance, errors: &mut Vec<ValidationError>) {
    // Check account exists
    if !state.accounts.contains_key(&bal.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Account {} was never opened", bal.account),
            bal.date,
        ));
        return;
    }

    // Check if there are pending pads for this account
    if let Some(pending_pads) = state.pending_pads.remove(&bal.account) {
        // Check for multiple pads (E2004)
        if pending_pads.len() > 1 {
            errors.push(
                ValidationError::new(
                    ErrorCode::MultiplePadForBalance,
                    format!(
                        "Multiple pad directives for {} {} before balance assertion",
                        bal.account, bal.amount.currency
                    ),
                    bal.date,
                )
                .with_context(format!(
                    "pad dates: {}",
                    pending_pads
                        .iter()
                        .map(|p| p.date.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )),
            );
        }

        // Use the most recent pad
        if let Some(pending_pad) = pending_pads.last() {
            // Apply padding: calculate difference and add to both accounts
            if let Some(inv) = state.inventories.get(&bal.account) {
                let actual = inv.units(&bal.amount.currency);
                let expected = bal.amount.number;
                let difference = expected - actual;

                if difference != Decimal::ZERO {
                    // Add padding amount to target account
                    if let Some(target_inv) = state.inventories.get_mut(&bal.account) {
                        target_inv.add(Position::simple(Amount::new(
                            difference,
                            &bal.amount.currency,
                        )));
                    }

                    // Subtract padding amount from source account
                    if let Some(source_inv) = state.inventories.get_mut(&pending_pad.source_account)
                    {
                        source_inv.add(Position::simple(Amount::new(
                            -difference,
                            &bal.amount.currency,
                        )));
                    }
                }
            }
        }
        // After padding, the balance should match (no error needed)
        return;
    }

    // Get inventory and check balance (no padding case)
    if let Some(inv) = state.inventories.get(&bal.account) {
        let actual = inv.units(&bal.amount.currency);
        let expected = bal.amount.number;
        let tolerance = bal.tolerance.unwrap_or(bal.amount.inferred_tolerance());

        if (actual - expected).abs() > tolerance {
            errors.push(
                ValidationError::new(
                    ErrorCode::BalanceAssertionFailed,
                    format!(
                        "Balance assertion failed for {}: expected {} {}, got {} {}",
                        bal.account, expected, bal.amount.currency, actual, bal.amount.currency
                    ),
                    bal.date,
                )
                .with_context(format!("difference: {}", actual - expected)),
            );
        }
    }
}

fn validate_document(state: &LedgerState, doc: &Document, errors: &mut Vec<ValidationError>) {
    // Check account exists
    if !state.accounts.contains_key(&doc.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Account {} was never opened", doc.account),
            doc.date,
        ));
    }

    // Check if document file exists (if enabled)
    if state.options.check_documents {
        let doc_path = Path::new(&doc.path);

        let full_path = if doc_path.is_absolute() {
            doc_path.to_path_buf()
        } else if let Some(base) = &state.options.document_base {
            base.join(doc_path)
        } else {
            doc_path.to_path_buf()
        };

        if !full_path.exists() {
            errors.push(
                ValidationError::new(
                    ErrorCode::DocumentNotFound,
                    format!("Document file not found: {}", doc.path),
                    doc.date,
                )
                .with_context(format!("resolved path: {}", full_path.display())),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, NaiveDate, Posting};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
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
        assert!(errors
            .iter()
            .any(|e| e.code == ErrorCode::BalanceAssertionFailed));
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
        assert!(errors
            .iter()
            .any(|e| e.code == ErrorCode::TransactionUnbalanced));
    }

    #[test]
    fn test_validate_currency_not_allowed() {
        let directives = vec![
            Directive::Open(
                Open::new(date(2024, 1, 1), "Assets:Bank").with_currencies(vec!["USD".to_string()]),
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
        assert!(errors
            .iter()
            .any(|e| e.code == ErrorCode::CurrencyNotAllowed));
    }

    #[test]
    fn test_validate_future_date_warning() {
        // Create a date in the future
        let future_date = Local::now().date_naive() + chrono::Duration::days(30);

        let directives = vec![Directive::Open(Open {
            date: future_date,
            account: "Assets:Bank".to_string(),
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
        let options = ValidationOptions {
            warn_future_dates: true,
            ..Default::default()
        };
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
                account: "Assets:Bank".to_string(),
                path: "/nonexistent/path/to/document.pdf".to_string(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }),
        ];

        // Without check_documents option, no error
        let errors = validate(&directives);
        assert!(
            !errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Should not check documents by default"
        );

        // With check_documents option, should error
        let options = ValidationOptions {
            check_documents: true,
            ..Default::default()
        };
        let errors = validate_with_options(&directives, options);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::DocumentNotFound),
            "Should report missing document when enabled"
        );
    }

    #[test]
    fn test_validate_document_account_not_open() {
        let directives = vec![Directive::Document(Document {
            date: date(2024, 1, 15),
            account: "Assets:Unknown".to_string(),
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
    fn test_validate_ambiguous_lot_match() {
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
            // Try to sell with ambiguous cost (matches both lots - price only, no date)
            Directive::Transaction(
                Transaction::new(date(2024, 6, 1), "Sell ambiguous")
                    .with_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-5), "AAPL"))
                            .with_cost(cost_spec),
                    )
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(750), "USD"))),
            ),
        ];

        let errors = validate(&directives);
        assert!(
            errors
                .iter()
                .any(|e| e.code == ErrorCode::AmbiguousLotMatch),
            "Should error for ambiguous lot match: {errors:?}"
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
    fn test_validate_no_postings() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(Transaction::new(date(2024, 1, 15), "Empty")),
        ];

        let errors = validate(&directives);
        assert!(
            errors.iter().any(|e| e.code == ErrorCode::NoPostings),
            "Should error for transaction with no postings: {errors:?}"
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
            "Assets:401k", // Component starting with digit
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
}
