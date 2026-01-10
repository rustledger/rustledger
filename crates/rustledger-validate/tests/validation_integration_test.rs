//! Integration tests for the validation crate.
//!
//! Tests cover all validation rules: account lifecycle, balance assertions,
//! transaction balancing, currency constraints, and booking validation.

use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Balance, Close, Directive, NaiveDate, Open, Pad, Posting, PriceAnnotation, Transaction,
};
use rustledger_validate::{validate, ErrorCode};

// ============================================================================
// Helper Functions
// ============================================================================

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, day).unwrap()
}

fn validate_directives(directives: &[Directive]) -> Vec<ErrorCode> {
    let errors = validate(directives);
    errors.iter().map(|e| e.code).collect()
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
fn test_e3003_no_postings() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        // Transaction with no postings
        Directive::Transaction(Transaction::new(date(2024, 1, 15), "Empty transaction")),
    ];

    let errors = validate_directives(&directives);
    assert!(
        errors.contains(&ErrorCode::NoPostings),
        "expected E3003 NoPostings error"
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
    assert!(!errors
        .iter()
        .any(|e| e.code == ErrorCode::TransactionUnbalanced));
}
