//! Property-Based Tests from TLA+ Invariants for Validation
//!
//! These tests use proptest to verify that the validation implementation
//! satisfies the same invariants defined in ValidationCorrect.tla.
//!
//! Reference: spec/tla/ValidationCorrect.tla

use chrono::NaiveDate;
use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Balance, Directive, IncompleteAmount, Open, Posting, Transaction};
use rustledger_validate::{validate, ErrorCode};

// ============================================================================
// Test Strategies
// ============================================================================

fn date_strategy() -> impl Strategy<Value = NaiveDate> {
    (2020i32..2025, 1u32..13, 1u32..29).prop_map(|(y, m, d)| {
        NaiveDate::from_ymd_opt(y, m, d).unwrap_or(NaiveDate::from_ymd_opt(y, m, 1).unwrap())
    })
}

fn account_strategy() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "Assets:Bank:Checking".to_string(),
        "Assets:Bank:Savings".to_string(),
        "Expenses:Food".to_string(),
        "Income:Salary".to_string(),
        "Liabilities:CreditCard".to_string(),
    ])
}

/// Helper to create a complete amount for postings
fn complete(number: Decimal, currency: &str) -> Option<IncompleteAmount> {
    Some(IncompleteAmount::Complete(Amount::new(number, currency)))
}

// ============================================================================
// Validation Tests (from ValidationCorrect.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ ValidationCorrect ErrorMeansFirstMismatch:
    /// If a balance assertion error is reported, the expected and actual differ
    #[test]
    fn prop_balance_error_means_mismatch(
        open_date in date_strategy(),
        balance_date in date_strategy(),
        actual_balance in 0i64..1000,
        wrong_expected in 0i64..1000,
    ) {
        // Ensure balance_date is after open_date
        let balance_date = if balance_date <= open_date {
            open_date + chrono::Duration::days(1)
        } else {
            balance_date
        };

        // Ensure expected != actual for this test
        prop_assume!(actual_balance != wrong_expected);

        let account = "Assets:Bank:Checking".to_string();

        // Create directives: open account, add balance, check wrong balance
        let directives = vec![
            Directive::Open(Open {
                date: open_date,
                account: account.clone(),
                currencies: vec!["USD".to_string()],
                booking: None,
                meta: Default::default(),
            }),
            // Transaction to set actual balance
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposit".to_string(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone(),
                        units: complete(Decimal::from(actual_balance), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                    Posting {
                        account: "Equity:Opening".to_string(),
                        units: complete(Decimal::from(-actual_balance), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                ],
                meta: Default::default(),
            }),
            // Balance assertion with wrong expected
            Directive::Balance(Balance {
                date: balance_date,
                account,
                amount: Amount::new(Decimal::from(wrong_expected), "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
        ];

        let errors = validate(&directives);

        // Should have balance error
        let has_balance_error = errors.iter().any(|e| e.code == ErrorCode::BalanceAssertionFailed);

        prop_assert!(
            has_balance_error,
            "Balance assertion should fail when expected ({}) != actual ({})",
            wrong_expected, actual_balance
        );
    }

    /// TLA+ ValidationCorrect ErrorDetailsConsistent:
    /// No error when balance assertion matches actual balance
    #[test]
    fn prop_no_error_when_balance_matches(
        open_date in date_strategy(),
        balance_date in date_strategy(),
        balance_amount in 1i64..1000,
    ) {
        // Ensure balance_date is after open_date
        let balance_date = if balance_date <= open_date {
            open_date + chrono::Duration::days(1)
        } else {
            balance_date
        };

        let account = "Assets:Bank:Checking".to_string();

        // Create directives: open account, add balance, check correct balance
        let directives = vec![
            Directive::Open(Open {
                date: open_date,
                account: account.clone(),
                currencies: vec!["USD".to_string()],
                booking: None,
                meta: Default::default(),
            }),
            // Transaction to set balance
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposit".to_string(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone(),
                        units: complete(Decimal::from(balance_amount), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                    Posting {
                        account: "Equity:Opening".to_string(),
                        units: complete(Decimal::from(-balance_amount), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                ],
                meta: Default::default(),
            }),
            // Balance assertion with correct expected
            Directive::Balance(Balance {
                date: balance_date,
                account,
                amount: Amount::new(Decimal::from(balance_amount), "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
        ];

        let errors = validate(&directives);

        // Should NOT have balance assertion failed error
        let has_balance_error = errors.iter().any(|e| e.code == ErrorCode::BalanceAssertionFailed);

        prop_assert!(
            !has_balance_error,
            "No balance error when expected ({}) == actual",
            balance_amount
        );
    }

    /// TLA+ ValidationCorrect NonNegativeBalance:
    /// Balance tracking is accurate across multiple transactions
    #[test]
    fn prop_balance_tracking_accurate(
        open_date in date_strategy(),
        deposits in prop::collection::vec(1i64..100, 1..5),
    ) {
        let account = "Assets:Bank:Checking".to_string();
        let mut directives = vec![
            Directive::Open(Open {
                date: open_date,
                account: account.clone(),
                currencies: vec!["USD".to_string()],
                booking: None,
                meta: Default::default(),
            }),
        ];

        let mut total = 0i64;
        for (i, deposit) in deposits.iter().enumerate() {
            total += deposit;
            let txn_date = open_date + chrono::Duration::days(i as i64 + 1);

            directives.push(Directive::Transaction(Transaction {
                date: txn_date,
                flag: '*',
                payee: None,
                narration: format!("Deposit {}", i + 1),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone(),
                        units: complete(Decimal::from(*deposit), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                    Posting {
                        account: "Income:Salary".to_string(),
                        units: complete(Decimal::from(-*deposit), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                ],
                meta: Default::default(),
            }));
        }

        // Add balance assertion at end
        let balance_date = open_date + chrono::Duration::days(deposits.len() as i64 + 2);
        directives.push(Directive::Balance(Balance {
            date: balance_date,
            account,
            amount: Amount::new(Decimal::from(total), "USD"),
            tolerance: None,
            meta: Default::default(),
        }));

        let errors = validate(&directives);

        // Should NOT have balance assertion failed error
        let has_balance_error = errors.iter().any(|e| e.code == ErrorCode::BalanceAssertionFailed);

        prop_assert!(
            !has_balance_error,
            "Balance should be {} after {} deposits, errors: {:?}",
            total, deposits.len(), errors
        );
    }
}

// ============================================================================
// Account Lifecycle Tests (from AccountStateMachine.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Account must be opened before use
    #[test]
    fn prop_account_must_be_opened(
        date in date_strategy(),
        account in account_strategy(),
    ) {
        // Transaction without opening the account first
        let directives = vec![
            Directive::Transaction(Transaction {
                date,
                flag: '*',
                payee: None,
                narration: "Test transaction".to_string(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone(),
                        units: complete(Decimal::from(100), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                    Posting {
                        account: "Equity:Opening".to_string(),
                        units: complete(Decimal::from(-100), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                    },
                ],
                meta: Default::default(),
            }),
        ];

        let errors = validate(&directives);

        // Should have account not open error
        let has_not_open_error = errors.iter().any(|e| e.code == ErrorCode::AccountNotOpen);

        prop_assert!(
            has_not_open_error,
            "Should report error when using unopened account: {}",
            account
        );
    }

    /// Duplicate account opens are detected
    #[test]
    fn prop_no_duplicate_opens(
        date1 in date_strategy(),
        date2 in date_strategy(),
        account in account_strategy(),
    ) {
        // Open account twice
        let directives = vec![
            Directive::Open(Open {
                date: date1,
                account: account.clone(),
                currencies: vec![],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Open(Open {
                date: date2,
                account: account.clone(),
                currencies: vec![],
                booking: None,
                meta: Default::default(),
            }),
        ];

        let errors = validate(&directives);

        // Should have duplicate open error
        let has_duplicate_error = errors.iter().any(|e| e.code == ErrorCode::AccountAlreadyOpen);

        prop_assert!(
            has_duplicate_error,
            "Should detect duplicate open for account: {}",
            account
        );
    }
}
