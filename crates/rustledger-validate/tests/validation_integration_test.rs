//! Integration tests for the validation crate.
//!
//! Tests cover all validation rules: account lifecycle, balance assertions,
//! transaction balancing, currency constraints, and booking validation.

use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Balance, Close, Directive, NaiveDate, Open, Pad, Posting, PriceAnnotation, Transaction,
};
use rustledger_parser::{Span, Spanned};
use rustledger_validate::{ErrorCode, ValidationOptions, validate, validate_spanned_with_options};

// ============================================================================
// Helper Functions
// ============================================================================

#[allow(clippy::missing_const_for_fn)]
fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, day).unwrap()
}

fn validate_directives(directives: &[Directive]) -> Vec<ErrorCode> {
    let errors = validate(directives);
    errors.iter().map(|e| e.code).collect()
}

/// Helper to wrap a directive with span and `file_id` info for testing.
#[allow(clippy::missing_const_for_fn)]
fn spanned_directive(
    directive: Directive,
    start: usize,
    end: usize,
    file_id: u16,
) -> Spanned<Directive> {
    Spanned {
        value: directive,
        span: Span::new(start, end),
        file_id,
    }
}

// ============================================================================
// Account Lifecycle Tests (E1xxx)
// ============================================================================

#[test]
fn test_e1001_account_not_open() {
    let directives = vec![
        // No open directive, but transaction uses account
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Test")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-100), "USD"))),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::AccountNotOpen),
        "expected E1001 AccountNotOpen error"
    );
}

#[test]
fn test_e1002_account_already_open() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 2), "Assets:Bank")), // Duplicate
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::AccountAlreadyOpen),
        "expected E1002 AccountAlreadyOpen error"
    );
}

#[test]
fn test_e1003_account_closed() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
        Directive::Close(Close::new(date(2024, 6, 1), "Assets:Bank")),
        // Transaction after close
        Directive::Transaction(
            Transaction::new(date(2024, 7, 1), "After close")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(dec!(-100), "USD"),
                )),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::AccountClosed),
        "expected E1003 AccountClosed error"
    );
}

#[test]
fn test_valid_account_lifecycle() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Purchase")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
        Directive::Close(Close::new(date(2024, 12, 31), "Expenses:Food")),
    ];

    let errors = validate_directives(&directives);
    // No E1xxx errors
    let account_errors: Vec<_> = errors
        .iter()
        .filter(|e| {
            matches!(
                e,
                ErrorCode::AccountNotOpen
                    | ErrorCode::AccountAlreadyOpen
                    | ErrorCode::AccountClosed
            )
        })
        .collect();
    assert!(
        account_errors.is_empty(),
        "expected no account lifecycle errors, got {account_errors:?}"
    );
}

// ============================================================================
// Balance Assertion Tests (E2xxx)
// ============================================================================

#[test]
fn test_e2001_balance_assertion_failed() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
        // Balance assertion with wrong amount
        Directive::Balance(Balance::new(
            date(2024, 1, 31),
            "Assets:Bank",
            Amount::new(dec!(1000), "USD"), // Wrong - should be -50
        )),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::BalanceAssertionFailed),
        "expected E2001 BalanceAssertionFailed error"
    );
}

#[test]
fn test_valid_balance_assertion() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
        // Correct balance assertion
        Directive::Balance(Balance::new(
            date(2024, 1, 31),
            "Assets:Bank",
            Amount::new(dec!(-50), "USD"),
        )),
    ];

    let errors = validate_directives(&directives);
    assert!(
        !errors.contains(&ErrorCode::BalanceAssertionFailed),
        "expected no BalanceAssertionFailed error"
    );
}

// ============================================================================
// Transaction Balancing Tests (E3xxx)
// ============================================================================

#[test]
fn test_e3001_transaction_unbalanced() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        // Transaction doesn't balance
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Unbalanced")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))), // Missing 50
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::TransactionUnbalanced),
        "expected E3001 TransactionUnbalanced error"
    );
}

#[test]
fn test_e3003_no_postings_allowed() {
    // Python beancount allows transactions with no postings (metadata-only).
    // We match this behavior and do NOT report an error.
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        // Transaction with no postings
        Directive::Transaction(Transaction::new(date(2024, 1, 15), "Empty transaction")),
    ];

    let errors = validate_directives(&directives);
    assert!(
        !errors.contains(&ErrorCode::NoPostings),
        "should NOT report E3003 NoPostings error (Python allows empty transactions)"
    );
}

#[test]
fn test_e3004_single_posting() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        // Transaction with single posting (warning)
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Single posting")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::SinglePosting),
        "expected E3004 SinglePosting warning"
    );
}

#[test]
fn test_valid_balanced_transaction() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Balanced")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "USD"))),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        !errors.contains(&ErrorCode::TransactionUnbalanced),
        "expected no TransactionUnbalanced error"
    );
}

// ============================================================================
// Pad Directive Tests
// ============================================================================

#[test]
fn test_valid_pad_with_balance() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // Pad to fill initial balance
        Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
        // Balance assertion after pad
        Directive::Balance(Balance::new(
            date(2024, 1, 2),
            "Assets:Bank",
            Amount::new(dec!(1000), "USD"),
        )),
    ];

    let errors = validate_directives(&directives);
    // Pad should work correctly
    assert!(
        !errors.contains(&ErrorCode::BalanceAssertionFailed),
        "expected pad to satisfy balance assertion"
    );
}

// ============================================================================
// Multi-Currency Tests
// ============================================================================

#[test]
fn test_valid_multi_currency_with_price() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:USD")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:EUR")),
        // Exchange with price annotation
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Currency exchange")
                .with_posting(
                    Posting::new("Assets:USD", Amount::new(dec!(100), "USD"))
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(0.85), "EUR"))),
                )
                .with_posting(Posting::new("Assets:EUR", Amount::new(dec!(-85), "EUR"))),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        !errors.contains(&ErrorCode::TransactionUnbalanced),
        "expected multi-currency transaction with price to balance"
    );
}

// ============================================================================
// Real-World Scenario Tests
// ============================================================================

#[test]
fn test_complete_ledger_validation() {
    let directives = vec![
        // Open accounts
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Checking")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Savings")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Transport")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // Initial pad
        Directive::Pad(Pad::new(
            date(2024, 1, 1),
            "Assets:Bank:Checking",
            "Equity:Opening",
        )),
        Directive::Balance(Balance::new(
            date(2024, 1, 2),
            "Assets:Bank:Checking",
            Amount::new(dec!(5000), "USD"),
        )),
        // Salary
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Monthly salary")
                .with_payee("Employer")
                .with_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(dec!(-3000), "USD"),
                ))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(3000), "USD"),
                )),
        ),
        // Expenses
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(150), "USD")))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-150), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 22), "Gas")
                .with_posting(Posting::new(
                    "Expenses:Transport",
                    Amount::new(dec!(45), "USD"),
                ))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-45), "USD"),
                )),
        ),
        // Transfer
        Directive::Transaction(
            Transaction::new(date(2024, 1, 25), "Transfer to savings")
                .with_posting(Posting::new(
                    "Assets:Bank:Savings",
                    Amount::new(dec!(1000), "USD"),
                ))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-1000), "USD"),
                )),
        ),
        // Final balance check
        Directive::Balance(Balance::new(
            date(2024, 1, 31),
            "Assets:Bank:Checking",
            Amount::new(dec!(6805), "USD"), // 5000 + 3000 - 150 - 45 - 1000
        )),
    ];

    let errors = validate_directives(&directives);

    // Should have no critical errors
    let critical_errors: Vec<_> = errors
        .iter()
        .filter(|e| {
            matches!(
                e,
                ErrorCode::AccountNotOpen
                    | ErrorCode::TransactionUnbalanced
                    | ErrorCode::BalanceAssertionFailed
            )
        })
        .collect();

    assert!(
        critical_errors.is_empty(),
        "expected no critical validation errors, got {critical_errors:?}"
    );
}

#[test]
fn test_basic_validation() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Test")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "USD"))),
        ),
    ];

    // Validate
    let errors = validate(&directives);

    // Should pass basic validation
    assert!(
        !errors
            .iter()
            .any(|e| e.code == ErrorCode::TransactionUnbalanced)
    );
}

// ============================================================================
// Spanned Validation Tests (validate_spanned_with_options)
// ============================================================================

#[test]
fn test_spanned_validation_preserves_location_for_account_not_open() {
    let directives = vec![
        // Transaction uses an unopened account
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Test")
                    .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-100), "USD"))),
            ),
            100,
            200, // span: bytes 100-200
            1,   // file_id: 1
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let account_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::AccountNotOpen)
        .expect("expected E1001 AccountNotOpen error");

    // Verify that location info was propagated
    assert_eq!(account_error.span, Some(Span::new(100, 200)));
    assert_eq!(account_error.file_id, Some(1));
}

#[test]
fn test_spanned_validation_preserves_location_for_unbalanced_transaction() {
    let directives = vec![
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            0,
            50,
            0,
        ),
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            50,
            100,
            0,
        ),
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Unbalanced")
                    .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))), // Missing 50
            ),
            100,
            250, // span: bytes 100-250
            2,   // file_id: 2 (different file)
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let unbalanced_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::TransactionUnbalanced)
        .expect("expected E3001 TransactionUnbalanced error");

    // Verify location from the transaction directive
    assert_eq!(unbalanced_error.span, Some(Span::new(100, 250)));
    assert_eq!(unbalanced_error.file_id, Some(2));
}

#[test]
fn test_spanned_validation_preserves_location_for_balance_error() {
    let directives = vec![
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            0,
            50,
            0,
        ),
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            50,
            100,
            0,
        ),
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Purchase")
                    .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
            ),
            100,
            200,
            0,
        ),
        // Balance assertion with wrong amount
        spanned_directive(
            Directive::Balance(Balance::new(
                date(2024, 1, 31),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"), // Wrong
            )),
            200,
            280, // span: bytes 200-280
            3,   // file_id: 3
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let balance_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::BalanceAssertionFailed)
        .expect("expected E2001 BalanceAssertionFailed error");

    assert_eq!(balance_error.span, Some(Span::new(200, 280)));
    assert_eq!(balance_error.file_id, Some(3));
}

#[test]
fn test_spanned_validation_preserves_location_for_duplicate_open() {
    let directives = vec![
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            0,
            50,
            0,
        ),
        // Duplicate open
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 2), "Assets:Bank")),
            50,
            100, // span: bytes 50-100
            1,   // file_id: 1
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let dup_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::AccountAlreadyOpen)
        .expect("expected E1002 AccountAlreadyOpen error");

    assert_eq!(dup_error.span, Some(Span::new(50, 100)));
    assert_eq!(dup_error.file_id, Some(1));
}

#[test]
fn test_spanned_validation_preserves_location_for_account_closed() {
    let directives = vec![
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            0,
            50,
            0,
        ),
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            50,
            100,
            0,
        ),
        spanned_directive(
            Directive::Close(Close::new(date(2024, 6, 1), "Assets:Bank")),
            100,
            150,
            0,
        ),
        // Transaction after close
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 7, 1), "After close")
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")))
                    .with_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-100), "USD"),
                    )),
            ),
            150,
            300, // span: bytes 150-300
            4,   // file_id: 4
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let closed_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::AccountClosed)
        .expect("expected E1003 AccountClosed error");

    assert_eq!(closed_error.span, Some(Span::new(150, 300)));
    assert_eq!(closed_error.file_id, Some(4));
}

#[test]
fn test_spanned_validation_single_posting_warning_has_location() {
    let directives = vec![
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            0,
            50,
            0,
        ),
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Single posting")
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
            ),
            50,
            150, // span: bytes 50-150
            5,   // file_id: 5
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let single_post_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::SinglePosting)
        .expect("expected E3004 SinglePosting warning");

    assert_eq!(single_post_error.span, Some(Span::new(50, 150)));
    assert_eq!(single_post_error.file_id, Some(5));
}

#[test]
fn test_spanned_validation_multiple_errors_have_correct_locations() {
    // Test that multiple errors in the same file get their respective locations
    let directives = vec![
        // First error: unopened account
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "First error")
                    .with_posting(Posting::new("Expenses:A", Amount::new(dec!(100), "USD")))
                    .with_posting(Posting::new("Assets:A", Amount::new(dec!(-100), "USD"))),
            ),
            0,
            100, // First location
            0,
        ),
        // Second error: different unopened accounts
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "Second error")
                    .with_posting(Posting::new("Expenses:B", Amount::new(dec!(50), "USD")))
                    .with_posting(Posting::new("Assets:B", Amount::new(dec!(-50), "USD"))),
            ),
            100,
            200, // Second location
            0,
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    // Should have multiple AccountNotOpen errors with different locations
    let account_errors: Vec<_> = errors
        .iter()
        .filter(|e| e.code == ErrorCode::AccountNotOpen)
        .collect();

    assert!(
        account_errors.len() >= 2,
        "expected at least 2 AccountNotOpen errors"
    );

    // Verify at least some have different spans
    let spans: std::collections::HashSet<_> =
        account_errors.iter().filter_map(|e| e.span).collect();
    assert!(spans.len() >= 2, "expected errors to have different spans");
}

#[test]
fn test_spanned_validation_valid_ledger_no_errors() {
    let directives = vec![
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            0,
            50,
            0,
        ),
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            50,
            100,
            0,
        ),
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Valid")
                    .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "USD"))),
            ),
            100,
            250,
            0,
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    // Filter out any info-level "date out of order" messages
    let critical_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.code, ErrorCode::DateOutOfOrder | ErrorCode::FutureDate))
        .collect();

    assert!(
        critical_errors.is_empty(),
        "expected no validation errors, got {critical_errors:?}"
    );
}

#[test]
fn test_spanned_validation_out_of_order_dates_have_location() {
    // Test that date ordering warnings include location info
    let directives = vec![
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            0,
            50,
            0,
        ),
        // Later date first
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 10), "Expenses:Food")),
            50,
            100,
            0,
        ),
        // Earlier date second (out of order)
        spanned_directive(
            Directive::Open(Open::new(date(2024, 1, 5), "Expenses:Transport")),
            100,
            150, // span: bytes 100-150
            6,   // file_id: 6
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let date_error = errors.iter().find(|e| e.code == ErrorCode::DateOutOfOrder);

    // DateOutOfOrder is detected when directives are sorted - the error should have location
    if let Some(error) = date_error {
        assert!(
            error.span.is_some(),
            "DateOutOfOrder error should have span"
        );
        assert!(
            error.file_id.is_some(),
            "DateOutOfOrder error should have file_id"
        );
    }
}
