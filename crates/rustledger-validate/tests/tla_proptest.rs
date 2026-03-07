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
use rustledger_validate::{ErrorCode, validate};

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
    ///
    /// Note: With beancount's 2x tolerance multiplier for balance assertions,
    /// integer amounts have tolerance = 0.5 * 2 = 1.0, so difference must be > 1.
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

        // Ensure difference exceeds the 2x tolerance for integer amounts.
        // For integers (scale=0), tolerance = 0.5 * 2 = 1.0, so diff must be > 1.
        let diff = (actual_balance - wrong_expected).abs();
        prop_assume!(diff > 1);

        let account = "Assets:Bank:Checking".to_string();

        // Create directives: open account, add balance, check wrong balance
        let directives = vec![
            Directive::Open(Open {
                date: open_date,
                account: account.clone().into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            // Transaction to set actual balance
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposit".into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone().into(),
                        units: complete(Decimal::from(actual_balance), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Equity:Opening".into(),
                        units: complete(Decimal::from(-actual_balance), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
            }),
            // Balance assertion with wrong expected
            Directive::Balance(Balance {
                date: balance_date,
                account: account.into(),
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
                account: account.clone().into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            // Transaction to set balance
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposit".into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone().into(),
                        units: complete(Decimal::from(balance_amount), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Equity:Opening".into(),
                        units: complete(Decimal::from(-balance_amount), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
            }),
            // Balance assertion with correct expected
            Directive::Balance(Balance {
                date: balance_date,
                account: account.into(),
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
                account: account.clone().into(),
                currencies: vec!["USD".into()],
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
                narration: format!("Deposit {}", i + 1).into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone().into(),
                        units: complete(Decimal::from(*deposit), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Income:Salary".into(),
                        units: complete(Decimal::from(-*deposit), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
            }));
        }

        // Add balance assertion at end
        let balance_date = open_date + chrono::Duration::days(deposits.len() as i64 + 2);
        directives.push(Directive::Balance(Balance {
            date: balance_date,
            account: account.into(),
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
                narration: "Test transaction".into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone().into(),
                        units: complete(Decimal::from(100), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Equity:Opening".into(),
                        units: complete(Decimal::from(-100), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
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
                account: account.clone().into(),
                currencies: vec![],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Open(Open {
                date: date2,
                account: account.clone().into(),
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

// ============================================================================
// Additional Validation Invariants (from ValidationCorrect.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ ValidationCorrect: Validation is deterministic.
    ///
    /// Running validate() twice on the same directives should produce
    /// identical error sets.
    #[test]
    fn prop_validation_deterministic(
        open_date in date_strategy(),
        balance_amount in 1i64..1000,
    ) {
        let account = "Assets:Bank:Checking".to_string();

        let directives = vec![
            Directive::Open(Open {
                date: open_date,
                account: account.clone().into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposit".into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.into(),
                        units: complete(Decimal::from(balance_amount), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Equity:Opening".into(),
                        units: complete(Decimal::from(-balance_amount), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
            }),
        ];

        let errors1 = validate(&directives);
        let errors2 = validate(&directives);

        // Same number of errors
        prop_assert_eq!(
            errors1.len(),
            errors2.len(),
            "Validation should be deterministic"
        );

        // Same error codes
        for (e1, e2) in errors1.iter().zip(errors2.iter()) {
            prop_assert_eq!(
                e1.code,
                e2.code,
                "Error codes should match"
            );
        }
    }

    /// TLA+ ValidationCorrect: Tolerance bounds are respected.
    ///
    /// Balance assertions within tolerance should pass.
    /// Balance assertions outside tolerance should fail.
    #[test]
    fn prop_tolerance_bounds_respected(
        open_date in date_strategy(),
        actual_balance in 100i64..1000,
    ) {
        let balance_date = open_date + chrono::Duration::days(1);
        let account = "Assets:Bank:Checking".to_string();

        // Use decimal amounts to get smaller tolerance
        let actual_dec = Decimal::new(actual_balance, 2); // e.g., 1.00 to 10.00
        let within_tol = actual_dec + Decimal::new(1, 3); // +0.001 (within 0.005 * 2 = 0.01)
        let outside_tol = actual_dec + Decimal::new(2, 2); // +0.02 (outside tolerance)

        // Test within tolerance
        let directives_within = vec![
            Directive::Open(Open {
                date: open_date,
                account: account.clone().into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposit".into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone().into(),
                        units: Some(IncompleteAmount::Complete(Amount::new(actual_dec, "USD"))),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Equity:Opening".into(),
                        units: Some(IncompleteAmount::Complete(Amount::new(-actual_dec, "USD"))),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
            }),
            Directive::Balance(Balance {
                date: balance_date,
                account: account.clone().into(),
                amount: Amount::new(within_tol, "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
        ];

        let errors_within = validate(&directives_within);
        let has_error_within = errors_within.iter().any(|e| e.code == ErrorCode::BalanceAssertionFailed);

        prop_assert!(
            !has_error_within,
            "Balance within tolerance should pass: actual={}, expected={}",
            actual_dec, within_tol
        );

        // Test outside tolerance
        let directives_outside = vec![
            Directive::Open(Open {
                date: open_date,
                account: account.clone().into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposit".into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account.clone().into(),
                        units: Some(IncompleteAmount::Complete(Amount::new(actual_dec, "USD"))),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Equity:Opening".into(),
                        units: Some(IncompleteAmount::Complete(Amount::new(-actual_dec, "USD"))),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
            }),
            Directive::Balance(Balance {
                date: balance_date,
                account: account.into(),
                amount: Amount::new(outside_tol, "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
        ];

        let errors_outside = validate(&directives_outside);
        let has_error_outside = errors_outside.iter().any(|e| e.code == ErrorCode::BalanceAssertionFailed);

        prop_assert!(
            has_error_outside,
            "Balance outside tolerance should fail: actual={}, expected={}",
            actual_dec, outside_tol
        );
    }

    /// TLA+ ValidationCorrect: First error detected is accurate.
    ///
    /// Multiple balance assertion failures should all be reported with
    /// accurate expected vs actual values.
    #[test]
    fn prop_multiple_balance_errors_reported(
        open_date in date_strategy(),
        actual_balance in 100i64..500,
    ) {
        let account1 = "Assets:Bank:Checking".to_string();
        let account2 = "Assets:Bank:Savings".to_string();
        let balance_date = open_date + chrono::Duration::days(1);

        // Wrong expected values (differ by more than tolerance)
        let wrong_expected1 = actual_balance + 100;
        let wrong_expected2 = actual_balance + 200;

        let directives = vec![
            Directive::Open(Open {
                date: open_date,
                account: account1.clone().into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Open(Open {
                date: open_date,
                account: account2.clone().into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Transaction(Transaction {
                date: open_date,
                flag: '*',
                payee: None,
                narration: "Initial deposits".into(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    Posting {
                        account: account1.clone().into(),
                        units: complete(Decimal::from(actual_balance), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: account2.clone().into(),
                        units: complete(Decimal::from(actual_balance), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                    Posting {
                        account: "Equity:Opening".into(),
                        units: complete(Decimal::from(-actual_balance * 2), "USD"),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    },
                ],
                meta: Default::default(),
                trailing_comments: Vec::new(),
            }),
            Directive::Balance(Balance {
                date: balance_date,
                account: account1.into(),
                amount: Amount::new(Decimal::from(wrong_expected1), "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
            Directive::Balance(Balance {
                date: balance_date,
                account: account2.into(),
                amount: Amount::new(Decimal::from(wrong_expected2), "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
        ];

        let errors = validate(&directives);

        // Should have two balance assertion errors
        let balance_error_count = errors
            .iter()
            .filter(|e| e.code == ErrorCode::BalanceAssertionFailed)
            .count();

        prop_assert_eq!(
            balance_error_count,
            2,
            "Should report two balance assertion errors, got: {:?}",
            errors
        );
    }
}
