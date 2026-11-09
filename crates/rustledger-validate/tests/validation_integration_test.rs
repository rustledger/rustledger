//! Integration tests for the validation crate.
//!
//! Tests cover all validation rules: account lifecycle, balance assertions,
//! transaction balancing, currency constraints, and booking validation.

use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Balance, Close, Directive, NaiveDate, Open, Pad, Posting, PriceAnnotation, Transaction,
};
use rustledger_parser::{Span, Spanned};
use rustledger_validate::{ErrorCode, ValidationOptions};

mod common;
use common::{validate, validate_spanned_with_options};

// ============================================================================
// Helper Functions
// ============================================================================

#[allow(clippy::missing_const_for_fn)]
fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
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
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(100), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(-100), "USD"),
                )),
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
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(50), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank",
                    Amount::new(dec!(-50), "USD"),
                )),
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
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(50), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank",
                    Amount::new(dec!(-50), "USD"),
                )),
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
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(50), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank",
                    Amount::new(dec!(-50), "USD"),
                )),
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
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(100), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank",
                    Amount::new(dec!(-50), "USD"),
                )), // Missing 50
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
            Transaction::new(date(2024, 1, 15), "Single posting").with_synthesized_posting(
                Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")),
            ),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::SinglePosting),
        "expected E3004 SinglePosting warning"
    );
}

#[test]
fn test_e4005_negative_cost_per_unit() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stock")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Checking")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy with negative cost")
                .with_synthesized_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(-150) })
                            .with_currency("USD"),
                    ),
                )
                .with_synthesized_posting(Posting::auto("Assets:Checking")),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::NegativeCost),
        "expected E4005 NegativeCost error for negative per-unit cost"
    );
}

#[test]
fn test_e4005_negative_total_cost() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stock")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Checking")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy with negative total cost")
                .with_synthesized_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::Total { value: dec!(-1500) })
                            .with_currency("USD"),
                    ),
                )
                .with_synthesized_posting(Posting::auto("Assets:Checking")),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::NegativeCost),
        "expected E4005 NegativeCost error for negative total cost"
    );
}

#[test]
fn test_e4005_positive_cost_ok() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stock")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Checking")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy with positive cost")
                .with_synthesized_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(150) })
                            .with_currency("USD"),
                    ),
                )
                .with_synthesized_posting(Posting::new(
                    "Assets:Checking",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ];

    let errors = validate_directives(&directives);
    assert!(
        !errors.contains(&ErrorCode::NegativeCost),
        "expected no NegativeCost error for positive cost"
    );
}

#[test]
fn test_valid_balanced_transaction() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Balanced")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(100), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank",
                    Amount::new(dec!(-100), "USD"),
                )),
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
                .with_synthesized_posting(
                    Posting::new("Assets:USD", Amount::new(dec!(100), "USD"))
                        .with_price(PriceAnnotation::unit(Amount::new(dec!(0.85), "EUR"))),
                )
                .with_synthesized_posting(Posting::new(
                    "Assets:EUR",
                    Amount::new(dec!(-85), "EUR"),
                )),
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
                .with_synthesized_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(dec!(-3000), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(3000), "USD"),
                )),
        ),
        // Expenses
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "Groceries")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(150), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-150), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 22), "Gas")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Transport",
                    Amount::new(dec!(45), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-45), "USD"),
                )),
        ),
        // Transfer
        Directive::Transaction(
            Transaction::new(date(2024, 1, 25), "Transfer to savings")
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Savings",
                    Amount::new(dec!(1000), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
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
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(100), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank",
                    Amount::new(dec!(-100), "USD"),
                )),
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
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(-100), "USD"),
                    )),
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
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50), "USD"),
                    )), // Missing 50
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
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(50), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-50), "USD"),
                    )),
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
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
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
                Transaction::new(date(2024, 1, 15), "Single posting").with_synthesized_posting(
                    Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")),
                ),
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
                    .with_synthesized_posting(Posting::new(
                        "Expenses:A",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:A",
                        Amount::new(dec!(-100), "USD"),
                    )),
            ),
            0,
            100, // First location
            0,
        ),
        // Second error: different unopened accounts
        spanned_directive(
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "Second error")
                    .with_synthesized_posting(Posting::new(
                        "Expenses:B",
                        Amount::new(dec!(50), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:B",
                        Amount::new(dec!(-50), "USD"),
                    )),
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
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-100), "USD"),
                    )),
            ),
            100,
            250,
            0,
        ),
    ];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    // FutureDate is advisory and unrelated to what this test pins. E10001
    // used to be filtered here too; it no longer exists (#1970).
    let critical_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.code, ErrorCode::FutureDate))
        .collect();

    assert!(
        critical_errors.is_empty(),
        "expected no validation errors, got {critical_errors:?}"
    );
}

// ============================================================================
// Plugin-synthesized directive attribution (issue #896)
// ============================================================================

#[test]
fn test_plugin_synthesized_directive_gets_attribution_note() {
    // A validator error raised on a directive whose file_id is the synthesized
    // sentinel must carry an advisory note telling the user a plugin generated
    // the directive. Without this, errors from plugin-generated Opens look
    // like they came from nowhere.
    let directives = vec![spanned_directive(
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Currency:FSS_AUSFIX")),
        0,
        0,
        rustledger_parser::SYNTHESIZED_FILE_ID,
    )];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let account_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::InvalidAccountName)
        .expect("expected E1005 for the '_'-containing account name");

    let note = account_error
        .note
        .as_deref()
        .expect("plugin-synthesized directive must have an attribution note");
    assert!(
        note.contains("synthesized by a plugin"),
        "note should clearly identify the directive as plugin-generated, got: {note}",
    );
    assert!(
        note.contains("plugin"),
        "note should point users at their `plugin` declarations, got: {note}",
    );
}

#[test]
fn test_source_directive_does_not_get_attribution_note() {
    // Complement to the test above: errors on directives with a real file_id
    // (i.e. directly parsed from source) must NOT get the plugin attribution
    // note, or we would confuse users whose accounts ARE in their files.
    let directives = vec![spanned_directive(
        Directive::Open(Open::new(date(2024, 1, 1), "Invalid:Root")),
        10,
        40,
        0, // real source file_id
    )];

    let errors = validate_spanned_with_options(&directives, ValidationOptions::default());

    let account_error = errors
        .iter()
        .find(|e| e.code == ErrorCode::InvalidAccountName)
        .expect("expected E1005 for bad root account type");

    assert!(
        account_error.note.is_none(),
        "source-parsed directive must not be tagged as plugin-synthesized, got note: {:?}",
        account_error.note,
    );
}

// ============================================================================
// Account-valued metadata (#2813)
// ============================================================================

/// The `E1005` errors for `source`, validated under `roots`.
fn meta_account_errors(source: &str, roots: &[&str]) -> Vec<String> {
    let parsed = rustledger_parser::parse(source);
    assert!(parsed.errors.is_empty(), "{source:?}: {:?}", parsed.errors);
    let directives: Vec<Directive> = parsed.directives.into_iter().map(|d| d.value).collect();
    let options = ValidationOptions::default()
        .with_account_types(roots.iter().map(ToString::to_string).collect());
    common::validate_with_options(&directives, options)
        .into_iter()
        .filter(|e| e.code == ErrorCode::InvalidAccountName)
        .map(|e| e.message)
        .collect()
}

/// An account-valued metadata entry is checked against the roots, as
/// beancount checks every account token (`kk: Foo:Bar` is `Invalid account
/// name` there), on a directive and on a posting, and under the ledger's
/// configured roots (`option "name_assets"`), not a fixed list.
#[test]
fn test_validate_reports_an_account_metadata_value_with_an_invalid_root() {
    const ROOTS: [&str; 5] = ["Assets", "Liabilities", "Equity", "Income", "Expenses"];
    let open = "2024-01-01 open Assets:A\n  kk: Foo:Bar\n";
    let errors = meta_account_errors(open, &ROOTS);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("\"Foo:Bar\""), "{errors:?}");

    let posting = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n\
                   2024-01-02 *\n  Assets:A  1 USD\n    kk: Foo:Bar\n  Assets:B\n";
    assert_eq!(meta_account_errors(posting, &ROOTS).len(), 1);

    // A valid root, under the default roots and under renamed ones.
    let valid = "2024-01-01 open Assets:A\n  kk: Equity:B\n";
    assert_eq!(meta_account_errors(valid, &ROOTS), Vec::<String>::new());
    let renamed = ["Actifs", "Liabilities", "Equity", "Income", "Expenses"];
    let actifs = "2024-01-01 open Actifs:A\n  kk: Actifs:B\n  jj: Assets:B\n";
    let errors = meta_account_errors(actifs, &renamed);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("\"Assets:B\""), "{errors:?}");
}

/// Invalid account metadata values are reported in the order written, as
/// bean-check 3.2.3 reports them (`zz`, `aa`, `mm` here, lines 2 to 4), not
/// sorted by key. Sorting was only needed while `Metadata` was a hash map
/// (#2835).
#[test]
fn test_validate_reports_invalid_account_metadata_in_written_order() {
    const ROOTS: [&str; 5] = ["Assets", "Liabilities", "Equity", "Income", "Expenses"];
    let open = "2024-01-01 open Assets:A\n  zz: Foo:Bar\n  aa: Baz:Qux\n  mm: Qux:Zed\n";
    let errors = meta_account_errors(open, &ROOTS);
    assert_eq!(errors.len(), 3, "{errors:?}");
    for (error, name) in errors.iter().zip(["Foo:Bar", "Baz:Qux", "Qux:Zed"]) {
        assert!(error.contains(&format!("\"{name}\"")), "{errors:?}");
    }
}

// ============================================================================
// Account names in custom values and pads (#2809)
// ============================================================================

/// The `E1005` messages for `source` under the default roots.
fn invalid_account_names(source: &str) -> Vec<String> {
    meta_account_errors(
        source,
        &["Assets", "Liabilities", "Equity", "Income", "Expenses"],
    )
}

/// An account among a `custom` directive's values is checked against the
/// roots, as beancount checks every account token (bean-check 3.2.3:
/// `Invalid account name` for each), in the order written, and under the
/// ledger's configured roots.
#[test]
fn test_validate_reports_an_invalid_account_in_a_custom_directive() {
    for (source, names) in [
        (
            "2024-01-01 custom \"budget\" AAssets:A \"x\" 10 USD TRUE\n",
            vec!["AAssets:A"],
        ),
        (
            "2024-01-01 custom \"budget\" A-ssets:A \"x\" 10 USD TRUE\n",
            vec!["A-ssets:A"],
        ),
        (
            "2024-01-01 custom \"budget\" Assets0:A \"x\" 10 USD TRUE\n",
            vec!["Assets0:A"],
        ),
        (
            "2024-01-01 custom \"x\" Assets:A Foo:Bar Bar:Baz\n",
            vec!["Foo:Bar", "Bar:Baz"],
        ),
        // A value first, then its metadata, as beancount orders them.
        (
            "2024-01-01 custom \"x\" Foo:Bar\n  kk: Bar:Baz\n",
            vec!["Foo:Bar", "Bar:Baz"],
        ),
        ("2024-01-01 custom \"x\" Assets:A\n", vec![]),
        // A string is not an account.
        ("2024-01-01 custom \"x\" \"Foo:Bar\"\n", vec![]),
    ] {
        let errors = invalid_account_names(source);
        assert_eq!(errors.len(), names.len(), "{source:?}: {errors:?}");
        for (error, name) in errors.iter().zip(&names) {
            assert!(
                error.contains(&format!("\"{name}\"")),
                "{source:?}: {errors:?}"
            );
        }
    }
    let renamed = ["Actifs", "Liabilities", "Equity", "Income", "Expenses"];
    let errors = meta_account_errors("2024-01-01 custom \"x\" Actifs:A Assets:B\n", &renamed);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("\"Assets:B\""), "{errors:?}");
}

/// A pad checks both of its accounts before an unopened one stops it, as
/// beancount reports each: an unopened target hid an invalid source name.
#[test]
fn test_validate_pad_reports_an_invalid_source_after_an_unopened_target() {
    let errors = invalid_account_names("2024-01-01 pad Assets:A AEquity:B\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("\"AEquity:B\""), "{errors:?}");
}

/// The stray-character matrix (`rustledger-parser/tests/stray_char_matrix.rs`)
/// excludes the rows beancount rejects with `Invalid account name` (`x`),
/// because rledger reports those when it validates the file rather than when
/// it parses it. This holds that up: every excluded row outside `option`
/// (whose excluded rows are invalid option names, reported by the loader) is a
/// parse error or an `E1005` here. The `custom` rows and the pad rows with an
/// invalid source after an unopened target were the exceptions (#2809).
#[test]
fn test_validate_reports_every_account_name_row_the_stray_char_matrix_excludes() {
    // Must match `CHARS` and `cases()` in `stray_char_matrix.rs` and
    // `scripts/stray-char-matrix.py`; the length check below catches a drift.
    const CHARS: &str = "!@?*~^$&|{}(),#%\"/_-'.A0";
    fn cases(base: &str) -> Vec<String> {
        let mut out = Vec::new();
        for i in 0..base.len() {
            let before = &base[..i];
            let line = &before[before.rfind('\n').map_or(0, |p| p + 1)..];
            if !line.is_empty() && line.chars().all(|c| c == ' ') {
                continue;
            }
            for ch in CHARS.chars() {
                out.push(format!("{before}{ch}{}", &base[i..]));
                if i > 0 && base.as_bytes()[i - 1] == b' ' {
                    out.push(format!("{before}{ch} {}", &base[i..]));
                }
            }
        }
        out
    }
    let data = include_str!("../../rustledger-parser/tests/data/stray_char_matrix.tsv");
    let mut checked = 0;
    let mut unreported = Vec::new();
    for line in data.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        let base: String = serde_json::from_str(fields[2]).expect("the snippet is a JSON string");
        let generated = cases(&base);
        assert_eq!(
            generated.len(),
            fields[3].len(),
            "{}: case count",
            fields[1]
        );
        if fields[1] == "option" {
            continue;
        }
        for (src, verdict) in generated.iter().zip(fields[3].chars()) {
            if verdict != 'x' {
                continue;
            }
            checked += 1;
            let parsed = rustledger_parser::parse(src);
            if !parsed.errors.is_empty() {
                continue;
            }
            let directives: Vec<Directive> =
                parsed.directives.into_iter().map(|d| d.value).collect();
            let reported = validate(&directives)
                .iter()
                .any(|e| e.code == ErrorCode::InvalidAccountName);
            if !reported {
                unreported.push(format!("{}: {src:?}", fields[1]));
            }
        }
    }
    assert!(checked > 1_500, "only {checked} excluded rows checked");
    assert!(
        unreported.is_empty(),
        "{} excluded rows not reported, first 10:\n{}",
        unreported.len(),
        unreported[..unreported.len().min(10)].join("\n")
    );
}

// ============================================================================
// Pads with a closed or unopened account
// ============================================================================

/// The error codes `source` validates to, in order.
fn codes_of(source: &str) -> Vec<ErrorCode> {
    let parsed = rustledger_parser::parse(source);
    assert!(parsed.errors.is_empty(), "{source:?}: {:?}", parsed.errors);
    let directives: Vec<Directive> = parsed.directives.into_iter().map(|d| d.value).collect();
    validate(&directives).into_iter().map(|e| e.code).collect()
}

/// A pad dated after one of its accounts was closed references an inactive
/// account, as bean-check 3.2.3 reports (`Invalid reference to inactive
/// account`), and the padding still applies: no balance failure follows.
/// On the close date itself the account is still active.
#[test]
fn test_validate_pad_reports_a_closed_account() {
    let head = "2024-01-01 open Assets:A\n2024-01-01 open Equity:O\n";
    for close in ["Equity:O", "Assets:A"] {
        let source = format!(
            "{head}2024-01-05 close {close}\n2024-01-10 pad Assets:A Equity:O\n\
             2024-01-11 balance Assets:A 100 USD\n"
        );
        assert_eq!(codes_of(&source), [ErrorCode::AccountClosed], "{source:?}");
    }
    // Unused (a zero difference), as there: inactive, then unused.
    let source = format!(
        "{head}2024-01-05 close Equity:O\n2024-01-10 pad Assets:A Equity:O\n\
         2024-01-11 balance Assets:A 0 USD\n"
    );
    assert_eq!(
        codes_of(&source),
        [ErrorCode::AccountClosed, ErrorCode::PadWithoutBalance],
        "{source:?}"
    );
    let source = format!(
        "{head}2024-01-10 close Equity:O\n2024-01-10 pad Assets:A Equity:O\n2024-01-11 balance Assets:A 100 USD\n"
    );
    // bean-check is clean. The padding is dated at the pad, as beancount
    // dates it, so the source holds it when it closes later that day: only
    // the advisory `E1004`, which `check` does not report (`rledger lint
    // closed-nonempty` does), as for any posting before a close.
    assert_eq!(
        codes_of(&source),
        [ErrorCode::AccountCloseNotEmpty],
        "{source:?}"
    );
    assert!(ErrorCode::AccountCloseNotEmpty.is_advisory_only());
}

/// beancount inserts the padding whatever the accounts' state, so an
/// unopened account in a pad is reported (`E1001`) but adds no balance
/// failure (`E2001`) and no `Unused Pad entry` (`E2003`). bean-check 3.2.3
/// reports only the unknown accounts on each of these.
#[test]
fn test_validate_pad_with_an_unopened_account_still_pads() {
    // One E1001 per unopened account at the pad (the known count divergence:
    // bean-check reports each a second time against its padding transaction),
    // plus the balance's own E1001 on an unopened target.
    for (source, count) in [
        // Unopened source.
        (
            "2024-01-01 open Assets:A\n2024-01-10 pad Assets:A Equity:O\n2024-01-11 balance Assets:A 100 USD\n",
            1,
        ),
        // Source opened only after the pad.
        (
            "2024-01-01 open Assets:A\n2024-01-20 open Equity:O\n2024-01-10 pad Assets:A Equity:O\n2024-01-11 balance Assets:A 100 USD\n",
            1,
        ),
        // Unopened target.
        (
            "2024-01-01 open Equity:O\n2024-01-10 pad Assets:A Equity:O\n2024-01-11 balance Assets:A 100 USD\n",
            2,
        ),
        // Both unopened.
        (
            "2024-01-10 pad Assets:A Equity:O\n2024-01-11 balance Assets:A 100 USD\n",
            3,
        ),
    ] {
        assert_eq!(
            codes_of(source),
            vec![ErrorCode::AccountNotOpen; count],
            "{source:?}"
        );
    }
}

/// A zero balance on an unopened target uses no pad, just as a zero
/// difference on an opened one uses none, so the pad is unused; and a pad with an
/// unopened account and no balance after it is unused too. bean-check 3.2.3
/// reports `Unused Pad entry` and the unknown accounts on both.
#[test]
fn test_validate_unopened_pad_without_a_padding_balance_is_unused() {
    assert_eq!(
        codes_of(
            "2024-01-01 open Equity:O\n2024-01-10 pad Assets:A Equity:O\n\
             2024-01-11 balance Assets:A 0 USD\n"
        ),
        [
            ErrorCode::AccountNotOpen,
            ErrorCode::AccountNotOpen,
            ErrorCode::PadWithoutBalance
        ]
    );
    assert_eq!(
        codes_of("2024-01-01 open Assets:A\n2024-01-10 pad Assets:A Equity:O\n"),
        [ErrorCode::AccountNotOpen, ErrorCode::PadWithoutBalance]
    );
}

/// Two pads before one balance: the earlier is an unused pad (E2003) whether
/// or not the target is open, as beancount reports it, and nothing else.
#[test]
fn test_validate_two_pads_before_a_balance_leave_the_earlier_unused() {
    let two_pads = |open: &str| {
        format!(
            "{open}2024-01-01 open Equity:O\n2024-01-09 pad Assets:A Equity:O\n\
             2024-01-10 pad Assets:A Equity:O\n2024-01-11 balance Assets:A 100 USD\n"
        )
    };
    for (source, unopened) in [
        (two_pads("2024-01-01 open Assets:A\n"), 0),
        (two_pads(""), 3),
    ] {
        let codes = codes_of(&source);
        let mut expected = vec![ErrorCode::AccountNotOpen; unopened];
        expected.push(ErrorCode::PadWithoutBalance);
        assert_eq!(codes, expected, "{source:?}");
    }
}

// ============================================================================
// Account names beancount lexes with a non-ASCII start (#2906)
// ============================================================================

/// beancount 3.2.3 lexes any non-ASCII character as the start of an account
/// component, then rejects the name (`Invalid account name`) unless the first
/// sub-component starts with `\p{Lu}` or `\p{Nd}`. Every verdict here is
/// bean-check's on `2024-01-01 open <name>`, except the `\p{Lo}`/`\p{Lt}`
/// extension rledger keeps on purpose (#816). The source must PARSE without
/// errors in every case: the name is judged after lexing, as `E1005`.
#[test]
fn test_e1005_matches_beancount_on_non_ascii_component_starts() {
    let roots = ["Assets", "Liabilities", "Equity", "Income", "Expenses"];
    let check = |account: &str, roots: &[&str], valid: bool| {
        let source = format!("2024-01-01 open {account}\n");
        let errors = meta_account_errors(&source, roots);
        assert_eq!(errors.is_empty(), valid, "{account}: {errors:?}");
    };
    // Valid in beancount.
    for account in [
        "Assets:\u{663}",       // ٣
        "Assets:\u{663}Foo",    // ٣Foo
        "Assets:A\u{663}",      // A٣
        "Assets:\u{dc}n\u{ef}", // Ünï
        "Assets:A:\u{e9}clair", // later component, lowercase start
        "Assets:A:\u{1F600}",   // later component, emoji start
        "Assets:A\u{1F600}",    // emoji after the start
    ] {
        check(account, &roots, true);
    }
    // `Invalid account name` in beancount.
    for account in [
        "Assets:\u{e9}clair", // éclair
        "Assets:\u{1F600}",   // emoji start
        "Assets:\u{308}A",    // combining mark start
        "Assets:\u{b2}",      // ² (No)
        "\u{c9}quit\u{e9}:A", // Équité, a root not configured
    ] {
        check(account, &roots, false);
    }
    // A non-ASCII root is valid once configured, as with `option
    // "name_equity" "Équité"` in beancount.
    let renamed = [
        "Assets",
        "Liabilities",
        "\u{c9}quit\u{e9}",
        "Income",
        "Expenses",
    ];
    check("\u{c9}quit\u{e9}:A", &renamed, true);
    check("\u{c9}quit\u{e9}:\u{663}", &renamed, true);
    check("\u{c9}quit\u{e9}:\u{e9}", &renamed, false);
    // rledger's deliberate extension (#816): beancount rejects these.
    check("Assets:\u{65e5}\u{672c}", &roots, true); // 日本
}

/// A pad that already padded one currency, a later pad, and balances in
/// another currency and then the first: each balance uses its own pad, so
/// nothing is reported, as bean-check 3.2.3 reports nothing. The removed
/// `E2004` counted the first pad as a second contender for the EUR balance.
#[test]
fn test_validate_pad_for_one_currency_is_no_contender_for_another() {
    let codes = codes_of(
        "2024-01-01 open Assets:A\n2024-01-01 open Equity:O\n\
         2024-01-02 pad Assets:A Equity:O\n2024-01-03 balance Assets:A 100 USD\n\
         2024-01-04 pad Assets:A Equity:O\n2024-01-05 balance Assets:A 10 EUR\n\
         2024-01-06 balance Assets:A 50 USD\n",
    );
    assert_eq!(codes, Vec::<ErrorCode>::new());
}

/// A `pad` or `balance` dated before its account's later `open` names an
/// inactive account, as bean-check 3.2.3 reports it (`Invalid reference to
/// inactive account`), not one that was never opened (#2896).
#[test]
fn test_validate_pad_and_balance_before_a_later_open_are_inactive() {
    let source = "2024-01-01 open Equity:O\n2024-02-01 open Assets:A\n\
                  2024-01-02 pad Assets:A Equity:O\n2024-01-05 balance Assets:A 100 USD\n";
    let parsed = rustledger_parser::parse(source);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let directives: Vec<Directive> = parsed.directives.into_iter().map(|d| d.value).collect();
    let messages: Vec<String> = validate(&directives)
        .into_iter()
        .map(|e| format!("{}: {}", e.code.code(), e.message))
        .collect();
    assert_eq!(
        messages,
        [
            "E1001: Pad target account Assets:A is inactive on 2024-01-02 \
             (not opened until 2024-02-01)",
            "E1001: Account Assets:A is inactive on 2024-01-05 (not opened until 2024-02-01)",
        ],
    );
}

/// Two pads before a balance: the balance uses only the later one, and the
/// earlier one is unused and never pads a later balance, as in beancount
/// (bean-check 3.2.3: `Unused Pad entry` on the 01-09 pad, `Balance failed`
/// on 01-12). The earlier pad padded the 01-12 balance, hiding the failure
/// (#2896).
#[test]
fn test_validate_superseded_pad_is_unused_and_pads_nothing_later() {
    let codes = codes_of(
        "2024-01-01 open Assets:A\n2024-01-01 open Equity:O\n\
         2024-01-09 pad Assets:A Equity:O\n2024-01-10 pad Assets:A Equity:O\n\
         2024-01-11 balance Assets:A 100 USD\n2024-01-12 balance Assets:A 200 USD\n",
    );
    assert_eq!(
        codes,
        [
            ErrorCode::BalanceAssertionFailed,
            ErrorCode::PadWithoutBalance,
        ]
    );
}
