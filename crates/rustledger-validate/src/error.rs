//! Validation error types.

use rustledger_core::NaiveDate;
use rustledger_parser::{Span, Spanned};
use thiserror::Error;

/// Validation error codes.
///
/// Error codes follow the spec in `spec/core/validation.md`. Every variant's
/// [`ErrorCode::code`] is asserted to appear in that spec by
/// `error_codes_documented_in_spec` (a drift guard).
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
    ///
    /// Reserved for spec parity but **never emitted**: rledger skips validation
    /// of a posting-less transaction rather than flagging it (matching Python
    /// beancount, which treats it as a structurally-valid no-op). See the early
    /// return in `validate_transaction_structure` and the
    /// `test_validate_no_postings_allowed` test.
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
    /// E4004: Arithmetic exceeded the representable decimal range.
    ArithmeticOverflow,
    /// E4005: Cost amount is negative (cost must be non-negative).
    NegativeCost,

    // === Currency Errors (E5xxx) ===
    /// E5001: Currency not declared (when strict mode enabled).
    UndeclaredCurrency,
    /// E5002: Currency not allowed in account.
    CurrencyNotAllowed,
    /// E5003: Invalid `precision` metadata on commodity directive (warning).
    InvalidPrecisionMetadata,

    // === Budget Errors (E11xxx) ===
    /// E11001: Malformed `custom "budget"` directive (warning).
    MalformedBudget,

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
    /// E10002: Entry dated in the future (warning).
    FutureDate,
}

impl ErrorCode {
    /// The code for an inventory-level booking failure.
    ///
    /// CANONICAL: the LSP surfaces booking errors it caught itself, and the
    /// Late validator surfaces the ones it provokes by replaying reductions —
    /// two call sites, one classification. They had byte-identical `match`
    /// arms; a reclassification applied to one and not the other would give
    /// the same ledger different codes in the editor and on the command line
    /// (CLAUDE.md, Canonical-Function Discipline).
    #[must_use]
    pub const fn for_booking_error(err: &rustledger_core::BookingError) -> Self {
        use rustledger_core::BookingError as B;
        match err {
            B::Overflow(_) => Self::ArithmeticOverflow,
            B::InsufficientUnits { .. } => Self::InsufficientUnits,
            B::AmbiguousMatch { .. } => Self::AmbiguousLotMatch,
            // A merge checksum failure means the pool booking recorded is not
            // the pool application produced, which is a lot-matching failure
            // from the ledger author's point of view.
            B::NoMatchingLot { .. } | B::CurrencyMismatch { .. } | B::MergeMismatch { .. } => {
                Self::NoMatchingLot
            }
        }
    }
}

impl ErrorCode {
    /// Every error-code variant. Used by the spec-drift guard test (and any
    /// catalog enumeration). MUST list every variant — keep it in sync with the
    /// enum; the exhaustive [`code`](Self::code) match is the compiler-enforced
    /// source of truth for the code strings themselves.
    pub const ALL: &'static [Self] = &[
        Self::AccountNotOpen,
        Self::AccountAlreadyOpen,
        Self::AccountClosed,
        Self::AccountCloseNotEmpty,
        Self::InvalidAccountName,
        Self::BalanceAssertionFailed,
        Self::BalanceToleranceExceeded,
        Self::PadWithoutBalance,
        Self::MultiplePadForBalance,
        Self::TransactionUnbalanced,
        Self::MultipleInterpolation,
        Self::NoPostings,
        Self::SinglePosting,
        Self::NoMatchingLot,
        Self::InsufficientUnits,
        Self::AmbiguousLotMatch,
        Self::ArithmeticOverflow,
        Self::NegativeCost,
        Self::UndeclaredCurrency,
        Self::CurrencyNotAllowed,
        Self::InvalidPrecisionMetadata,
        Self::MalformedBudget,
        Self::UnknownOption,
        Self::InvalidOptionValue,
        Self::DuplicateOption,
        Self::DocumentNotFound,
        Self::FutureDate,
    ];

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
            Self::ArithmeticOverflow => "E4004",
            Self::NegativeCost => "E4005",
            // Currency errors
            Self::UndeclaredCurrency => "E5001",
            Self::CurrencyNotAllowed => "E5002",
            Self::InvalidPrecisionMetadata => "E5003",
            // Budget errors. E6xxx is RESERVED for metadata errors by
            // docs/reference/errors.md and left alone, even though nothing uses
            // it yet — the one metadata error that exists (E5003) was filed
            // under currency. Taking a reserved range quietly is how two
            // categories end up sharing one prefix.
            Self::MalformedBudget => "E11001",
            // Option errors
            Self::UnknownOption => "E7001",
            Self::InvalidOptionValue => "E7002",
            Self::DuplicateOption => "E7003",
            // Document errors
            Self::DocumentNotFound => "E8001",
            // Date errors
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
                | Self::InvalidPrecisionMetadata
                | Self::MalformedBudget
        )
    }

    /// Whether this diagnostic is advisory-only and must NOT be surfaced by
    /// `check` (which mirrors `bean-check`). Python beancount does not flag
    /// closing an account with a residual balance, so `check` stays silent; the
    /// advisory is surfaced instead by `rledger lint closed-nonempty`.
    #[must_use]
    pub const fn is_advisory_only(&self) -> bool {
        matches!(self, Self::AccountCloseNotEmpty)
    }

    /// Parse a user-supplied code string (`"E2001"`, `"e2001"`, or bare
    /// `"2001"`) into its variant. Backs `rledger explain`.
    #[must_use]
    pub fn from_code(code: &str) -> Option<Self> {
        let digits = code
            .trim()
            .strip_prefix(['E', 'e'])
            .unwrap_or_else(|| code.trim());
        let normalized = format!("E{digits}");
        Self::ALL.iter().find(|c| c.code() == normalized).copied()
    }

    /// A short human title for the code (one line). Backs `rledger explain`.
    #[must_use]
    pub const fn title(&self) -> &'static str {
        match self {
            Self::AccountNotOpen => "Account used before it was opened",
            Self::AccountAlreadyOpen => "Duplicate open directive for an account",
            Self::AccountClosed => "Account used after it was closed",
            Self::AccountCloseNotEmpty => "Account closed with a non-zero balance",
            Self::InvalidAccountName => "Invalid account name",
            Self::BalanceAssertionFailed => "Balance assertion failed",
            Self::BalanceToleranceExceeded => "Balance exceeds explicit tolerance",
            Self::PadWithoutBalance => "Pad without a subsequent balance assertion",
            Self::MultiplePadForBalance => "Multiple pads for the same balance assertion",
            Self::TransactionUnbalanced => "Transaction does not balance",
            Self::MultipleInterpolation => "Multiple postings missing amounts for one currency",
            Self::NoPostings => "Transaction has no postings",
            Self::SinglePosting => "Transaction has a single posting",
            Self::NoMatchingLot => "No matching lot for reduction",
            Self::InsufficientUnits => "Not enough units in matching lots",
            Self::AmbiguousLotMatch => "Ambiguous lot match under STRICT booking",
            Self::ArithmeticOverflow => "Amount exceeds the representable range",
            Self::NegativeCost => "Negative cost",
            Self::UndeclaredCurrency => "Currency used without a commodity declaration",
            Self::CurrencyNotAllowed => "Currency not allowed in this account",
            Self::InvalidPrecisionMetadata => "Invalid precision metadata on commodity",
            Self::MalformedBudget => "Malformed budget directive",
            Self::UnknownOption => "Unknown option name",
            Self::InvalidOptionValue => "Invalid option value",
            Self::DuplicateOption => "Non-repeatable option given more than once",
            Self::DocumentNotFound => "Document file not found",
            Self::FutureDate => "Directive dated in the future",
        }
    }

    /// A detailed explanation of the code — what it means, its common cause,
    /// and how to fix it. Backs `rledger explain`, mirroring
    /// `rustc --explain`.
    ///
    /// Kept as code constants (not `include_str!` from `spec/core/`) so the
    /// binary is self-contained: published crates don't package `spec/`, and
    /// the Nix flake's source filter strips it. The exhaustive match means
    /// adding a variant forces adding its explanation, and the
    /// `error_codes_documented_in_spec` test guards that every code is also
    /// documented in the spec.
    #[must_use]
    pub const fn explanation(&self) -> &'static str {
        match self {
            Self::AccountNotOpen => {
                "A posting or directive references an account with no prior `open` \
                 directive.\n\nEvery account must be opened on or before the date it is \
                 first used:\n\n    2024-01-01 open Assets:Bank:Checking USD\n\nFix: add \
                 an `open` directive dated on or before the first use, or correct a \
                 misspelled account name."
            }
            Self::AccountAlreadyOpen => {
                "An `open` directive targets an account that is already open.\n\nThis \
                 is usually a duplicated line — often the same `open` appearing in both \
                 a main file and an `include`d file.\n\nFix: remove the duplicate \
                 `open` (keep the earliest one)."
            }
            Self::AccountClosed => {
                "A posting or directive references an account after its `close` \
                 directive.\n\nFix: move the transaction before the close date, remove \
                 the `close`, or use a different account."
            }
            Self::AccountCloseNotEmpty => {
                "A `close` directive targets an account that still holds a non-zero \
                 balance.\n\nAdvisory only: `check` stays silent to match `bean-check`; \
                 surface it on demand with `rledger lint closed-nonempty`.\n\nFix: zero \
                 the account (transfer the residual) before closing it."
            }
            Self::InvalidAccountName => {
                "An account name does not match the required pattern.\n\nAccount names \
                 are colon-separated capitalized components rooted at one of the five \
                 account types (Assets, Liabilities, Equity, Income, Expenses — \
                 renameable via `option \"name_assets\"` etc.), e.g. \
                 `Assets:Bank:Checking`.\n\nFix: rename the account to match the \
                 pattern."
            }
            Self::BalanceAssertionFailed => {
                "A `balance` assertion does not match the computed balance of the \
                 account (including its sub-accounts) at that date.\n\nThe comparison \
                 uses a tolerance inferred from the asserted amount's precision.\n\n\
                 Fix: correct the asserted amount, add the missing transactions, or \
                 insert a `pad` directive to absorb the difference. The reported \
                 difference is the exact discrepancy."
            }
            Self::BalanceToleranceExceeded => {
                "A `balance` assertion with an explicit tolerance, e.g. \
                 `balance Assets:Cash 100.00 ~ 0.05 USD`, differs from the computed \
                 balance by more than that tolerance.\n\nFix: correct the amount, \
                 widen the explicit tolerance, or add the missing transactions."
            }
            Self::PadWithoutBalance => {
                "A `pad` directive is never consumed by a later `balance` assertion \
                 for that account and currency.\n\nA pad means \"insert whatever \
                 amount makes the NEXT balance assertion true\" — without that \
                 balance it does nothing.\n\nFix: add the `balance` assertion after \
                 the pad, or delete the pad."
            }
            Self::MultiplePadForBalance => {
                "More than one `pad` directive is pending for the same account and \
                 currency before a single `balance` assertion — it is ambiguous which \
                 pad should absorb the difference.\n\nFix: keep one pad per \
                 account/currency between consecutive balance assertions."
            }
            Self::TransactionUnbalanced => {
                "The weights of a transaction's postings do not sum to zero per \
                 currency (beyond the inferred tolerance).\n\nA posting's weight is \
                 its amount, converted through its cost (`{...}`) or price \
                 (`@`/`@@`) when present.\n\nFix: correct the amounts, or leave \
                 exactly one posting's amount blank and rustledger will interpolate \
                 it. The reported residual is the exact imbalance."
            }
            Self::MultipleInterpolation => {
                "More than one posting in the same currency has no amount — only one \
                 blank posting per currency can be interpolated from the others.\n\n\
                 Fix: fill in amounts so at most one posting per currency is elided."
            }
            Self::NoPostings => {
                "Reserved for a transaction with zero postings.\n\nNever emitted in \
                 practice: rustledger (like Python beancount) treats a posting-less \
                 transaction as a structurally-valid no-op."
            }
            Self::SinglePosting => {
                "A transaction has exactly one posting, which cannot balance on its \
                 own (warning).\n\nFix: add the offsetting posting(s), or elide the \
                 second amount to interpolate it."
            }
            Self::NoMatchingLot => {
                "A cost reduction (e.g. a sale, `Assets:Stock -5 X {...}`) specifies \
                 a cost, date, or label that matches no lot held in the account's \
                 inventory.\n\nFix: check the cost spec against the actual holdings; \
                 `rledger query` with `cost_label`/`cost_date` columns shows the \
                 lots."
            }
            Self::InsufficientUnits => {
                "A reduction requests more units than the matching lots hold (e.g. \
                 selling 10 when 5 are held).\n\nA failed reduction leaves the \
                 inventory untouched.\n\nFix: reduce the sold quantity, or check for \
                 a missing purchase transaction."
            }
            Self::AmbiguousLotMatch => {
                "Under STRICT booking (the default), a reduction's cost spec matches \
                 more than one lot, and rustledger refuses to guess.\n\nFix: \
                 disambiguate with the lot's cost `{10.00 USD}`, date `{2024-01-02}`, \
                 or label `{\"lot-a\"}` — or open the account with a non-strict \
                 method: `2024-01-01 open Assets:Stock \"FIFO\"`."
            }
            Self::ArithmeticOverflow => {
                "An amount, or a running total, is larger than rledger's decimal type \
                 can represent (about ±7.9×10²⁸ — a 96-bit type with ~28 significant \
                 digits).\n\nrledger reports this instead of rounding or clamping: a \
                 clamped figure would be printed as if it were exact, and two clamped \
                 figures of opposite sign cancel to zero, which would make an \
                 unbalanced transaction look balanced.\n\nFix: split the transaction, \
                 or use larger units (thousands, millions) for the commodity."
            }
            Self::NegativeCost => {
                "A posting's cost amount is negative — a cost basis must be \
                 non-negative.\n\nFix: check the sign of the cost (the units carry \
                 the sign of a sale, not the cost)."
            }
            Self::UndeclaredCurrency => {
                "A currency is used but never declared with a `commodity` directive, \
                 and commodity declarations are required (strict commodity mode).\n\n\
                 Fix: add `YYYY-MM-DD commodity CUR`, or disable the strict \
                 requirement."
            }
            Self::CurrencyNotAllowed => {
                "A posting or `balance` assertion uses a currency outside the list \
                 the account was opened with (`open Assets:Cash USD` constrains the \
                 account to USD).\n\nFix: use an allowed currency, or extend the \
                 currency list on the `open` directive. An `open` with no currencies \
                 allows all."
            }
            Self::InvalidPrecisionMetadata => {
                "A `commodity` directive carries a `precision:` metadata value that \
                 does not parse as a non-negative integer (warning). The declaration \
                 is ignored; display precision falls back to \
                 `option \"display_precision\"`, then to inference.\n\nFix: use e.g. \
                 `precision: 2`."
            }
            Self::UnknownOption => {
                "An `option` directive names an option rustledger does not recognize \
                 (warning; the option is ignored).\n\nFix: check the option name \
                 against the options documentation — it may be misspelled or \
                 unsupported."
            }
            Self::InvalidOptionValue => {
                "An `option` directive has a value that does not parse for that \
                 option's type (e.g. a non-numeric \
                 `inferred_tolerance_multiplier`).\n\nFix: correct the value per the \
                 options documentation."
            }
            Self::DuplicateOption => {
                "A non-repeatable option is specified more than once (warning; the \
                 last value wins).\n\nFix: keep a single occurrence."
            }
            Self::DocumentNotFound => {
                "A `document` directive references a file that does not exist. \
                 Relative paths resolve against the directory of the source file \
                 containing the directive (matching `include`).\n\nFix: correct the \
                 path, or remove the directive."
            }
            Self::MalformedBudget => {
                "A `custom \"budget\"` directive that is recognizably a budget \
                 carries content rledger cannot use (warning).\n\nBudgets follow \
                 Fava's convention: `<date> custom \"budget\" <Account> \
                 \"<interval>\" <amount> <CCY>`, where interval is daily, weekly, \
                 monthly, quarterly or yearly. A trailing quoted note is fine; a \
                 trailing second figure is reported, though the budget still \
                 applies at the first.\n\nFix: correct the directive. This is not \
                 raised for a `custom \"budget\"` belonging to other tooling: a \
                 payload with neither a real interval keyword nor an \
                 account-and-amount pair is left alone everywhere, since \
                 `custom` is beancount's open extension point."
            }
            Self::FutureDate => {
                "A directive is dated in the future relative to today (warning).\n\n\
                 Fix: correct the date — or ignore the warning if the future dating \
                 is intentional (e.g. scheduled entries)."
            }
        }
    }

    /// Get the severity level.
    #[must_use]
    pub const fn severity(&self) -> Severity {
        // No code maps to `Severity::Info`. E10001 was the only one, and it was
        // unreachable — see #1970. The level is kept on `Severity` because it
        // is public and consumers match it exhaustively.
        if self.is_warning() {
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

/// Whether a rendered diagnostic code string (e.g. `"E1004"`) is advisory-only.
///
/// The string-keyed counterpart to [`ErrorCode::is_advisory_only`], for
/// consumers (the CLI `check`/`lint` split) that only carry the code string.
/// Keeping it here means the set of advisory-only codes lives in one place.
#[must_use]
pub fn is_advisory_only_code(code: &str) -> bool {
    code == ErrorCode::AccountCloseNotEmpty.code()
}

/// Severity level for validation messages.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Severity {
    /// Ledger is invalid.
    Error,
    /// Suspicious but valid.
    Warning,
    /// Informational only.
    ///
    /// No [`ErrorCode`] currently maps here. E10001 did, and it could never be
    /// emitted (#1970); the level is retained because `Severity` is public and
    /// the LSP maps it to `DiagnosticSeverity::INFORMATION`.
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
    fn error_codes_documented_in_spec() {
        // Drift guard: every `ErrorCode` must be documented in the validation
        // spec. (The spec may also carry codes emitted by other crates — e.g.
        // loader include errors E9001/E9002 — so this is a subset check, not
        // strict equality.) Codes are backtick-wrapped in the spec (`**Code:**
        // `E1001``), so the backtick delimiters keep a shorter code from
        // matching inside a longer one.
        // The spec lives at the workspace root (`spec/core/validation.md`),
        // OUTSIDE this crate, so it is not packaged to crates.io. Read it at
        // runtime relative to `CARGO_MANIFEST_DIR` and skip when it is absent —
        // e.g. `cargo test` on the published crate, which the Nix release channel
        // runs — rather than `include_str!`-ing it at compile time, which would
        // fail to build the published crate's tests (broke the Nix release
        // channel on 0.17.x).
        let spec_path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../spec/core/validation.md");
        let Ok(spec) = std::fs::read_to_string(spec_path) else {
            eprintln!(
                "skipping error_codes_documented_in_spec: {spec_path} not present (published-crate build)"
            );
            return;
        };
        let missing: Vec<&str> = ErrorCode::ALL
            .iter()
            .map(ErrorCode::code)
            .filter(|code| !spec.contains(&format!("`{code}`")))
            .collect();
        assert!(
            missing.is_empty(),
            "error codes missing from spec/core/validation.md: {missing:?}"
        );
    }

    #[test]
    fn all_lists_distinct_codes() {
        // Cheap completeness/dup guard for `ALL`: every code string is unique.
        let mut codes: Vec<&str> = ErrorCode::ALL.iter().map(ErrorCode::code).collect();
        let n = codes.len();
        codes.sort_unstable();
        codes.dedup();
        assert_eq!(codes.len(), n, "duplicate code in ErrorCode::ALL");
    }

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
