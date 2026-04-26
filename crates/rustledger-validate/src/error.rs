//! Validation error types.

use rustledger_core::NaiveDate;
use rustledger_parser::{Span, Spanned};
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
    /// E2002: Balance exceeds explicit tolerance.
    BalanceToleranceExceeded,
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
    /// E4005: Cost amount is negative (cost must be non-negative).
    NegativeCost,

    // === Currency Errors (E5xxx) ===
    /// E5001: Currency not declared (when strict mode enabled).
    UndeclaredCurrency,
    /// E5002: Currency not allowed in account.
    CurrencyNotAllowed,

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
            Self::BalanceToleranceExceeded => "E2002",
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
            Self::NegativeCost => "E4005",
            // Currency errors
            Self::UndeclaredCurrency => "E5001",
            Self::CurrencyNotAllowed => "E5002",
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

    /// Whether this error represents a parse-phase concern rather than a
    /// semantic/validate-phase concern.
    ///
    /// Some checks — notably account-name structure (E1005) — are lexical in
    /// nature and are conceptually part of parsing, even though rustledger
    /// currently runs them during validation because the set of valid account
    /// roots is not known until options have been resolved. Python beancount's
    /// parser rejects these inputs at parse time, so we tag them as parse-phase
    /// for consumers that distinguish the two (e.g. the conformance harness).
    #[must_use]
    pub const fn is_parse_phase(&self) -> bool {
        matches!(self, Self::InvalidAccountName)
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
///
/// The `Display` impl emits just the message text (no `[E1234]` prefix).
/// CLI and IDE renderers are expected to prepend the error code themselves,
/// which avoids the double-tagging seen in older output like
/// `error[E3001]: [E3001] ...` (see issue #901).
#[derive(Debug, Clone, Error)]
#[error("{message}")]
#[non_exhaustive]
pub struct ValidationError {
    /// Error code.
    pub code: ErrorCode,
    /// Error message.
    pub message: String,
    /// Date of the directive that caused the error.
    pub date: NaiveDate,
    /// Additional context.
    pub context: Option<String>,
    /// Advisory note attached to the error — typically used to help users
    /// diagnose the underlying cause (e.g. "this directive was synthesized
    /// by a plugin"). Unlike [`Self::context`], which describes data tied
    /// to the error, the note describes something about its *origin*.
    pub note: Option<String>,
    /// Source span (byte offsets within the file).
    pub span: Option<Span>,
    /// Source file ID (index into `SourceMap`).
    /// Uses `u16` to minimize struct size (max 65,535 files).
    pub file_id: Option<u16>,
}

impl ValidationError {
    /// Create a new validation error without source location.
    #[must_use]
    pub fn new(code: ErrorCode, message: impl Into<String>, date: NaiveDate) -> Self {
        Self {
            code,
            message: message.into(),
            date,
            context: None,
            note: None,
            span: None,
            file_id: None,
        }
    }

    /// Create a new validation error with source location from a spanned directive.
    #[must_use]
    pub fn with_location<T>(
        code: ErrorCode,
        message: impl Into<String>,
        date: NaiveDate,
        spanned: &Spanned<T>,
    ) -> Self {
        Self {
            code,
            message: message.into(),
            date,
            context: None,
            note: None,
            span: Some(spanned.span),
            file_id: Some(spanned.file_id),
        }
    }

    /// Add context to this error.
    #[must_use]
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Attach an advisory note to this error (builder pattern).
    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    /// Set the source location for this error (builder pattern).
    ///
    /// Use this to add location info to an existing error. For creating
    /// new errors with location, prefer [`Self::with_location`] instead.
    #[must_use]
    pub const fn at_location<T>(mut self, spanned: &Spanned<T>) -> Self {
        self.span = Some(spanned.span);
        self.file_id = Some(spanned.file_id);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_account_name_is_parse_phase() {
        // E1005 is a lexical/structural account-name check and must be
        // reported as a parse-phase diagnostic, matching Python beancount.
        assert!(ErrorCode::InvalidAccountName.is_parse_phase());
    }

    #[test]
    fn other_account_errors_are_validate_phase() {
        // Lifecycle errors remain semantic (validate-phase) concerns.
        assert!(!ErrorCode::AccountNotOpen.is_parse_phase());
        assert!(!ErrorCode::AccountAlreadyOpen.is_parse_phase());
        assert!(!ErrorCode::AccountClosed.is_parse_phase());
    }

    #[test]
    fn non_account_errors_are_validate_phase() {
        assert!(!ErrorCode::TransactionUnbalanced.is_parse_phase());
        assert!(!ErrorCode::BalanceAssertionFailed.is_parse_phase());
        assert!(!ErrorCode::UnknownOption.is_parse_phase());
    }
}
