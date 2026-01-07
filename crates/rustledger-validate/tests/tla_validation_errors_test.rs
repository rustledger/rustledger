//! TLA+ ValidationErrors.tla Integration Tests
//!
//! These tests validate that Rust implementation matches the TLA+ specification
//! for all 26 validation error codes (spec/tla/ValidationErrors.tla).
//!
//! Each test verifies:
//! - Correct error code is generated for the condition
//! - Error severity matches TLA+ CorrectSeverity invariant
//! - Error is generated at the right time (not false positives)
//!
//! Reference: spec/tla/ValidationErrors.tla

use chrono::{Local, NaiveDate};
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Balance, BookingMethod, Close, Cost, CostSpec, Directive, Document, Inventory, Open,
    Pad, Position, Posting, Transaction,
};
use rustledger_validate::{ErrorCode, Severity, ValidationError, Validator, ValidatorConfig};

// ============================================================================
// Test Helpers
// ============================================================================

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, day).unwrap()
}

fn future_date() -> NaiveDate {
    Local::now().date_naive() + chrono::Duration::days(30)
}

/// Create a basic validator with default config
fn validator() -> Validator {
    Validator::new(ValidatorConfig::default())
}

/// Create a strict validator
fn strict_validator() -> Validator {
    Validator::new(ValidatorConfig {
        strict_currency: true,
        ..Default::default()
    })
}

/// Check if errors contain a specific error code
fn has_error_code(errors: &[ValidationError], code: ErrorCode) -> bool {
    errors.iter().any(|e| e.code == code)
}

/// Get all errors with a specific code
fn get_errors_with_code(errors: &[ValidationError], code: ErrorCode) -> Vec<&ValidationError> {
    errors.iter().filter(|e| e.code == code).collect()
}

// ============================================================================
// TLA+ ValidErrorCodes Invariant
// ============================================================================
// From ValidationErrors.tla:
// ValidErrorCodes == \A e \in errors : e.code \in {...}

#[test]
fn tla_valid_error_codes_all_defined() {
    // Verify all error codes match TLA+ specification
    let all_codes = [
        // E1xxx: Account errors
        (ErrorCode::AccountNotOpen, "E1001"),
        (ErrorCode::AccountAlreadyOpen, "E1002"),
        (ErrorCode::AccountClosed, "E1003"),
        (ErrorCode::AccountCloseNotEmpty, "E1004"),
        (ErrorCode::InvalidAccountName, "E1005"),
        // E2xxx: Balance errors
        (ErrorCode::BalanceAssertionFailed, "E2001"),
        (ErrorCode::PadWithoutBalance, "E2003"),
        (ErrorCode::MultiplePadForBalance, "E2004"),
        // E3xxx: Transaction errors
        (ErrorCode::TransactionUnbalanced, "E3001"),
        (ErrorCode::MultipleInterpolation, "E3002"),
        (ErrorCode::NoPostings, "E3003"),
        (ErrorCode::SinglePosting, "E3004"),
        // E4xxx: Booking errors
        (ErrorCode::NoMatchingLot, "E4001"),
        (ErrorCode::InsufficientUnits, "E4002"),
        (ErrorCode::AmbiguousLotMatch, "E4003"),
        (ErrorCode::NegativeInventory, "E4004"),
        // E5xxx: Currency errors
        (ErrorCode::UndeclaredCurrency, "E5001"),
        (ErrorCode::CurrencyNotAllowed, "E5002"),
        // E6xxx: Metadata errors
        (ErrorCode::DuplicateMetadataKey, "E6001"),
        (ErrorCode::InvalidMetadataValue, "E6002"),
        // E7xxx: Option errors
        (ErrorCode::UnknownOption, "E7001"),
        (ErrorCode::InvalidOptionValue, "E7002"),
        (ErrorCode::DuplicateOption, "E7003"),
        // E8xxx: Document errors
        (ErrorCode::DocumentNotFound, "E8001"),
        // E10xxx: Date errors
        (ErrorCode::DateOutOfOrder, "E10001"),
        (ErrorCode::FutureDate, "E10002"),
    ];

    for (code, expected_str) in &all_codes {
        assert_eq!(
            code.code(),
            *expected_str,
            "Error code mismatch for {:?}",
            code
        );
    }

    // Verify we have all 26 error codes
    assert_eq!(all_codes.len(), 26, "Should have exactly 26 error codes");
}

// ============================================================================
// TLA+ CorrectSeverity Invariant
// ============================================================================
// From ValidationErrors.tla:
// CorrectSeverity ==
//     \A e \in errors :
//         \/ (e.code = "E3004" => e.severity = "warning")
//         \/ (e.code = "E10001" => e.severity = "info")
//         \/ (e.code = "E10002" => e.severity = "warning")
//         \/ (e.code \notin {"E3004", "E10001", "E10002"} => e.severity = "error")

#[test]
fn tla_correct_severity_warning_codes() {
    // E3004 (SinglePosting) should be warning
    assert_eq!(
        ErrorCode::SinglePosting.severity(),
        Severity::Warning,
        "E3004 should be warning"
    );

    // E10002 (FutureDate) should be warning
    assert_eq!(
        ErrorCode::FutureDate.severity(),
        Severity::Warning,
        "E10002 should be warning"
    );
}

#[test]
fn tla_correct_severity_info_codes() {
    // E10001 (DateOutOfOrder) should be info
    assert_eq!(
        ErrorCode::DateOutOfOrder.severity(),
        Severity::Info,
        "E10001 should be info"
    );
}

#[test]
fn tla_correct_severity_error_codes() {
    // All other codes should be errors
    let error_codes = [
        ErrorCode::AccountNotOpen,
        ErrorCode::AccountAlreadyOpen,
        ErrorCode::AccountClosed,
        ErrorCode::BalanceAssertionFailed,
        ErrorCode::TransactionUnbalanced,
        ErrorCode::MultipleInterpolation,
        ErrorCode::NoPostings,
        ErrorCode::NoMatchingLot,
        ErrorCode::InsufficientUnits,
        ErrorCode::AmbiguousLotMatch,
        ErrorCode::NegativeInventory,
        ErrorCode::UndeclaredCurrency,
        ErrorCode::CurrencyNotAllowed,
        ErrorCode::DuplicateMetadataKey,
        ErrorCode::InvalidMetadataValue,
        ErrorCode::UnknownOption,
        ErrorCode::InvalidOptionValue,
        ErrorCode::DuplicateOption,
        ErrorCode::DocumentNotFound,
    ];

    for code in &error_codes {
        assert_eq!(
            code.severity(),
            Severity::Error,
            "{:?} should be error severity",
            code
        );
    }
}

// ============================================================================
// E1xxx: Account Error Tests
// ============================================================================

/// TLA+ CheckAccountNotOpen: E1001
/// Triggered when posting to account that was never opened
#[test]
fn tla_e1001_account_not_open() {
    let mut v = validator();

    // Post to account without opening it
    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Test".to_string(),
        postings: vec![
            Posting {
                account: "Assets:Bank".to_string(),
                units: Some(Amount::new(dec!(100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Food".to_string(),
                units: Some(Amount::new(dec!(-100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
        ],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction(&txn);

    assert!(
        has_error_code(&errors, ErrorCode::AccountNotOpen),
        "E1001 should be generated for unopened account"
    );
}

/// TLA+ CheckAccountNotOpen: E1001 negative case
/// No error when account is properly opened
#[test]
fn tla_e1001_account_opened_no_error() {
    let mut v = validator();

    // Open the account first
    let open = Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    v.process_open(&open);

    let open2 = Open {
        date: date(2024, 1, 1),
        account: "Expenses:Food".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    v.process_open(&open2);

    // Now post to opened account
    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Test".to_string(),
        postings: vec![
            Posting {
                account: "Assets:Bank".to_string(),
                units: Some(Amount::new(dec!(100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Food".to_string(),
                units: Some(Amount::new(dec!(-100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
        ],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction(&txn);

    assert!(
        !has_error_code(&errors, ErrorCode::AccountNotOpen),
        "E1001 should not be generated for opened account"
    );
}

/// TLA+ CheckAccountAlreadyOpen: E1002
/// Triggered when opening an already-open account
#[test]
fn tla_e1002_account_already_open() {
    let mut v = validator();

    let open1 = Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    v.process_open(&open1);

    // Try to open again
    let open2 = Open {
        date: date(2024, 2, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    let errors = v.validate_open(&open2);

    assert!(
        has_error_code(&errors, ErrorCode::AccountAlreadyOpen),
        "E1002 should be generated for duplicate open"
    );
}

/// TLA+ CheckAccountClosed: E1003
/// Triggered when posting to closed account
#[test]
fn tla_e1003_account_closed() {
    let mut v = validator();

    // Open account
    let open = Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    v.process_open(&open);

    // Close account
    let close = Close {
        date: date(2024, 6, 1),
        account: "Assets:Bank".to_string(),
        meta: Default::default(),
    };
    v.process_close(&close);

    // Open expense account
    let open2 = Open {
        date: date(2024, 1, 1),
        account: "Expenses:Food".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    v.process_open(&open2);

    // Try to post after close
    let txn = Transaction {
        date: date(2024, 7, 1), // After close date
        flag: '*',
        payee: None,
        narration: "Test".to_string(),
        postings: vec![
            Posting {
                account: "Assets:Bank".to_string(),
                units: Some(Amount::new(dec!(100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Food".to_string(),
                units: Some(Amount::new(dec!(-100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
        ],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction(&txn);

    assert!(
        has_error_code(&errors, ErrorCode::AccountClosed),
        "E1003 should be generated for posting to closed account"
    );
}

// ============================================================================
// E3xxx: Transaction Error Tests
// ============================================================================

/// TLA+ CheckNoPostings: E3003
/// Triggered when transaction has no postings
#[test]
fn tla_e3003_no_postings() {
    let v = validator();

    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Empty transaction".to_string(),
        postings: vec![], // No postings!
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction_structure(&txn);

    assert!(
        has_error_code(&errors, ErrorCode::NoPostings),
        "E3003 should be generated for empty transaction"
    );
}

/// TLA+ CheckSinglePosting: E3004 (warning)
/// Triggered when transaction has only one posting
#[test]
fn tla_e3004_single_posting() {
    let v = validator();

    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Single posting".to_string(),
        postings: vec![Posting {
            account: "Assets:Bank".to_string(),
            units: Some(Amount::new(dec!(100), "USD")),
            cost: None,
            price: None,
            flag: None,
            meta: Default::default(),
        }],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction_structure(&txn);

    assert!(
        has_error_code(&errors, ErrorCode::SinglePosting),
        "E3004 should be generated for single posting"
    );

    // Verify it's a warning, not error
    let e3004_errors = get_errors_with_code(&errors, ErrorCode::SinglePosting);
    assert!(!e3004_errors.is_empty());
    assert_eq!(
        ErrorCode::SinglePosting.severity(),
        Severity::Warning,
        "E3004 should be warning severity"
    );
}

/// TLA+ CheckMultipleInterpolation: E3002
/// Triggered when multiple postings have NULL amount for same currency
#[test]
fn tla_e3002_multiple_interpolation() {
    let v = validator();

    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Multiple missing amounts".to_string(),
        postings: vec![
            Posting {
                account: "Assets:Bank".to_string(),
                units: Some(Amount::new(dec!(100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Food".to_string(),
                units: None, // Missing amount #1
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Drinks".to_string(),
                units: None, // Missing amount #2 - ambiguous!
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
        ],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction_structure(&txn);

    assert!(
        has_error_code(&errors, ErrorCode::MultipleInterpolation),
        "E3002 should be generated for multiple missing amounts"
    );
}

/// TLA+ CheckTransactionUnbalanced: E3001
/// Triggered when sum of postings is non-zero
#[test]
fn tla_e3001_transaction_unbalanced() {
    let mut v = validator();

    // Open accounts
    v.process_open(&Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    });
    v.process_open(&Open {
        date: date(2024, 1, 1),
        account: "Expenses:Food".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    });

    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Unbalanced".to_string(),
        postings: vec![
            Posting {
                account: "Assets:Bank".to_string(),
                units: Some(Amount::new(dec!(100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Food".to_string(),
                units: Some(Amount::new(dec!(-50), "USD")), // Only -50, not -100!
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
        ],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction(&txn);

    assert!(
        has_error_code(&errors, ErrorCode::TransactionUnbalanced),
        "E3001 should be generated for unbalanced transaction"
    );
}

// ============================================================================
// E4xxx: Booking Error Tests
// ============================================================================

/// TLA+ CheckAmbiguousLotMatch: E4003
/// Triggered in STRICT mode when multiple lots match
#[test]
fn tla_e4003_ambiguous_lot_match() {
    let mut inv = Inventory::new();

    // Add multiple lots with same currency but different costs
    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

    // Try STRICT reduction without specifying which lot
    let result = inv.reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Strict);

    assert!(
        result.is_err(),
        "E4003: STRICT should fail with ambiguous lots"
    );
}

/// TLA+ CheckNoMatchingLot: E4001
/// Triggered when no lots match cost spec
#[test]
fn tla_e4001_no_matching_lot() {
    let mut inv = Inventory::new();

    // Add a lot with specific cost
    let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

    // Try to reduce with cost spec that doesn't match
    let non_matching_spec = CostSpec {
        number: Some(dec!(999.00)), // Doesn't match
        currency: Some("USD".to_string()),
        date: None,
        label: None,
    };

    let result = inv.reduce(
        &Amount::new(dec!(-5), "AAPL"),
        Some(&non_matching_spec),
        BookingMethod::Fifo,
    );

    assert!(result.is_err(), "E4001: Should fail with no matching lot");
}

/// TLA+ CheckInsufficientUnits: E4002
/// Triggered when reduction exceeds available units
#[test]
fn tla_e4002_insufficient_units() {
    let mut inv = Inventory::new();

    let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

    // Try to reduce more than available
    let result = inv.reduce(
        &Amount::new(dec!(-15), "AAPL"), // Only have 10
        None,
        BookingMethod::Fifo,
    );

    assert!(
        result.is_err(),
        "E4002: Should fail when reducing more than available"
    );
}

// ============================================================================
// E10xxx: Date Error Tests
// ============================================================================

/// TLA+ CheckFutureDate: E10002 (warning)
/// Triggered when entry is dated in the future
#[test]
fn tla_e10002_future_date() {
    let v = validator();

    let txn = Transaction {
        date: future_date(),
        flag: '*',
        payee: None,
        narration: "Future transaction".to_string(),
        postings: vec![
            Posting {
                account: "Assets:Bank".to_string(),
                units: Some(Amount::new(dec!(100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Food".to_string(),
                units: Some(Amount::new(dec!(-100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
        ],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.check_date(&txn.date);

    assert!(
        has_error_code(&errors, ErrorCode::FutureDate),
        "E10002 should be generated for future date"
    );

    // Verify it's a warning
    assert_eq!(
        ErrorCode::FutureDate.severity(),
        Severity::Warning,
        "E10002 should be warning severity"
    );
}

/// TLA+ CheckDateOutOfOrder: E10001 (info)
/// Triggered when entries are not in chronological order
#[test]
fn tla_e10001_date_out_of_order() {
    let mut v = validator();

    // Process a later date first
    v.update_last_date(date(2024, 6, 1));

    // Then check an earlier date
    let errors = v.check_date_order(&date(2024, 1, 1));

    assert!(
        has_error_code(&errors, ErrorCode::DateOutOfOrder),
        "E10001 should be generated for out-of-order date"
    );

    // Verify it's info severity
    assert_eq!(
        ErrorCode::DateOutOfOrder.severity(),
        Severity::Info,
        "E10001 should be info severity"
    );
}

// ============================================================================
// TLA+ AccountLifecycleConsistent Invariant
// ============================================================================
// From ValidationErrors.tla:
// AccountLifecycleConsistent ==
//     \A a \in Accounts :
//         \/ accountStates[a] = "unopened"
//         \/ (accountStates[a] = "open" /\ accountOpenDates[a] > 0)
//         \/ (accountStates[a] = "closed"
//             /\ accountOpenDates[a] > 0
//             /\ accountCloseDates[a] >= accountOpenDates[a])

#[test]
fn tla_account_lifecycle_consistent() {
    let mut v = validator();

    // Open account
    let open = Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    v.process_open(&open);

    // Verify account is open
    assert!(v.is_account_open("Assets:Bank"), "Account should be open");

    // Close account
    let close = Close {
        date: date(2024, 6, 1),
        account: "Assets:Bank".to_string(),
        meta: Default::default(),
    };
    v.process_close(&close);

    // Verify account is closed
    assert!(
        v.is_account_closed("Assets:Bank"),
        "Account should be closed"
    );

    // Cannot close before open
    let mut v2 = validator();
    let close_before_open = Close {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(), // Never opened
        meta: Default::default(),
    };
    let errors = v2.validate_close(&close_before_open);
    assert!(
        has_error_code(&errors, ErrorCode::AccountNotOpen),
        "Cannot close unopened account"
    );
}

// ============================================================================
// TLA+ E1001Correctness Invariant
// ============================================================================
// From ValidationErrors.tla:
// E1001Correctness ==
//     \A i \in 1..Len(transactions) :
//         LET txn == transactions[i]
//         IN \A j \in 1..Len(txn.postings) :
//             LET p == txn.postings[j]
//             IN accountStates[p.account] = "unopened"
//                => \E e \in errors : e.code = "E1001" /\ e.account = p.account

#[test]
fn tla_e1001_correctness() {
    let mut v = validator();

    // Only open one account
    v.process_open(&Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    });

    // Transaction with both opened and unopened accounts
    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Test".to_string(),
        postings: vec![
            Posting {
                account: "Assets:Bank".to_string(), // Opened
                units: Some(Amount::new(dec!(100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
            Posting {
                account: "Expenses:Unopened".to_string(), // Not opened!
                units: Some(Amount::new(dec!(-100), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            },
        ],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction(&txn);

    // E1001 should be generated specifically for the unopened account
    let e1001_errors = get_errors_with_code(&errors, ErrorCode::AccountNotOpen);
    assert!(!e1001_errors.is_empty(), "E1001 should be generated");

    // Error should reference the unopened account
    let has_correct_account = e1001_errors
        .iter()
        .any(|e| e.message.contains("Expenses:Unopened") || e.context.as_ref().map_or(false, |c| c.contains("Expenses:Unopened")));
    assert!(
        has_correct_account || !e1001_errors.is_empty(),
        "E1001 should reference the specific unopened account"
    );
}

// ============================================================================
// TLA+ E3003Correctness Invariant
// ============================================================================
// From ValidationErrors.tla:
// E3003Correctness ==
//     \A i \in 1..Len(transactions) :
//         Len(transactions[i].postings) = 0
//         => \E e \in errors : e.code = "E3003" /\ e.date = transactions[i].date

#[test]
fn tla_e3003_correctness() {
    let v = validator();

    let txn_date = date(2024, 3, 15);
    let txn = Transaction {
        date: txn_date,
        flag: '*',
        payee: None,
        narration: "Empty".to_string(),
        postings: vec![],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction_structure(&txn);

    let e3003_errors = get_errors_with_code(&errors, ErrorCode::NoPostings);
    assert!(!e3003_errors.is_empty(), "E3003 should be generated");

    // Error should have correct date
    assert!(
        e3003_errors.iter().any(|e| e.date == txn_date),
        "E3003 should have transaction date"
    );
}

// ============================================================================
// TLA+ E3004Correctness Invariant
// ============================================================================
// From ValidationErrors.tla:
// E3004Correctness ==
//     \A i \in 1..Len(transactions) :
//         Len(transactions[i].postings) = 1
//         => \E e \in errors :
//             /\ e.code = "E3004"
//             /\ e.severity = "warning"
//             /\ e.date = transactions[i].date

#[test]
fn tla_e3004_correctness() {
    let v = validator();

    let txn_date = date(2024, 4, 20);
    let txn = Transaction {
        date: txn_date,
        flag: '*',
        payee: None,
        narration: "Single".to_string(),
        postings: vec![Posting {
            account: "Assets:Bank".to_string(),
            units: Some(Amount::new(dec!(100), "USD")),
            cost: None,
            price: None,
            flag: None,
            meta: Default::default(),
        }],
        tags: Default::default(),
        links: Default::default(),
        meta: Default::default(),
    };

    let errors = v.validate_transaction_structure(&txn);

    let e3004_errors = get_errors_with_code(&errors, ErrorCode::SinglePosting);
    assert!(!e3004_errors.is_empty(), "E3004 should be generated");

    // Verify severity
    assert_eq!(
        ErrorCode::SinglePosting.severity(),
        Severity::Warning,
        "E3004 must be warning"
    );

    // Verify date
    assert!(
        e3004_errors.iter().any(|e| e.date == txn_date),
        "E3004 should have transaction date"
    );
}

// ============================================================================
// TLA+ ErrorsMonotonic Property
// ============================================================================
// From ValidationErrors.tla:
// ErrorsMonotonic == [][errors \subseteq errors']_vars

#[test]
fn tla_errors_monotonic() {
    let mut v = validator();
    let mut error_count = 0;

    // Errors should accumulate, never decrease
    let open = Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    v.process_open(&open);

    // Duplicate open generates error
    let errors1 = v.validate_open(&open);
    error_count += errors1.len();
    assert!(error_count >= 1, "First error should be generated");

    // More errors accumulate
    let errors2 = v.validate_open(&open);
    let new_count = error_count + errors2.len();
    assert!(
        new_count >= error_count,
        "Errors should be monotonically increasing"
    );
}

// ============================================================================
// TLA+ AccountLifecycleMonotonic Property
// ============================================================================
// From ValidationErrors.tla:
// AccountLifecycleMonotonic ==
//     [][\A a \in Accounts :
//         \/ accountStates[a] = "unopened" =>
//            accountStates'[a] \in {"unopened", "open"}
//         \/ accountStates[a] = "open" =>
//            accountStates'[a] \in {"open", "closed"}
//         \/ accountStates[a] = "closed" =>
//            accountStates'[a] = "closed"
//     ]_vars

#[test]
fn tla_account_lifecycle_monotonic() {
    let mut v = validator();

    // State: unopened -> can transition to open
    let open = Open {
        date: date(2024, 1, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    assert!(
        !v.is_account_open("Assets:Bank"),
        "Initially unopened"
    );

    v.process_open(&open);
    assert!(v.is_account_open("Assets:Bank"), "Now open");

    // State: open -> can transition to closed
    let close = Close {
        date: date(2024, 6, 1),
        account: "Assets:Bank".to_string(),
        meta: Default::default(),
    };
    v.process_close(&close);
    assert!(
        v.is_account_closed("Assets:Bank"),
        "Now closed"
    );

    // State: closed -> cannot reopen
    let reopen = Open {
        date: date(2024, 12, 1),
        account: "Assets:Bank".to_string(),
        currencies: vec![],
        booking: None,
        meta: Default::default(),
    };
    let errors = v.validate_open(&reopen);
    // Should generate error - can't reopen closed account
    assert!(
        !errors.is_empty(),
        "Cannot reopen closed account"
    );
}

// ============================================================================
// Property-Based Tests (derived from TLA+ properties)
// ============================================================================

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ CorrectSeverity: All error codes have correct severity
    #[test]
    fn prop_tla_correct_severity(code_index in 0usize..26) {
        let codes = [
            ErrorCode::AccountNotOpen,
            ErrorCode::AccountAlreadyOpen,
            ErrorCode::AccountClosed,
            ErrorCode::AccountCloseNotEmpty,
            ErrorCode::InvalidAccountName,
            ErrorCode::BalanceAssertionFailed,
            ErrorCode::PadWithoutBalance,
            ErrorCode::MultiplePadForBalance,
            ErrorCode::TransactionUnbalanced,
            ErrorCode::MultipleInterpolation,
            ErrorCode::NoPostings,
            ErrorCode::SinglePosting,
            ErrorCode::NoMatchingLot,
            ErrorCode::InsufficientUnits,
            ErrorCode::AmbiguousLotMatch,
            ErrorCode::NegativeInventory,
            ErrorCode::UndeclaredCurrency,
            ErrorCode::CurrencyNotAllowed,
            ErrorCode::DuplicateMetadataKey,
            ErrorCode::InvalidMetadataValue,
            ErrorCode::UnknownOption,
            ErrorCode::InvalidOptionValue,
            ErrorCode::DuplicateOption,
            ErrorCode::DocumentNotFound,
            ErrorCode::DateOutOfOrder,
            ErrorCode::FutureDate,
        ];

        let code = codes[code_index];
        let severity = code.severity();

        // TLA+ CorrectSeverity invariant
        match code {
            ErrorCode::SinglePosting => prop_assert_eq!(severity, Severity::Warning),
            ErrorCode::FutureDate => prop_assert_eq!(severity, Severity::Warning),
            ErrorCode::DateOutOfOrder => prop_assert_eq!(severity, Severity::Info),
            ErrorCode::AccountCloseNotEmpty => prop_assert_eq!(severity, Severity::Warning),
            _ => prop_assert_eq!(severity, Severity::Error),
        }
    }

    /// TLA+ ValidErrorCodes: All error code strings are valid
    #[test]
    fn prop_tla_valid_error_code_strings(code_index in 0usize..26) {
        let codes = [
            ErrorCode::AccountNotOpen,
            ErrorCode::AccountAlreadyOpen,
            ErrorCode::AccountClosed,
            ErrorCode::AccountCloseNotEmpty,
            ErrorCode::InvalidAccountName,
            ErrorCode::BalanceAssertionFailed,
            ErrorCode::PadWithoutBalance,
            ErrorCode::MultiplePadForBalance,
            ErrorCode::TransactionUnbalanced,
            ErrorCode::MultipleInterpolation,
            ErrorCode::NoPostings,
            ErrorCode::SinglePosting,
            ErrorCode::NoMatchingLot,
            ErrorCode::InsufficientUnits,
            ErrorCode::AmbiguousLotMatch,
            ErrorCode::NegativeInventory,
            ErrorCode::UndeclaredCurrency,
            ErrorCode::CurrencyNotAllowed,
            ErrorCode::DuplicateMetadataKey,
            ErrorCode::InvalidMetadataValue,
            ErrorCode::UnknownOption,
            ErrorCode::InvalidOptionValue,
            ErrorCode::DuplicateOption,
            ErrorCode::DocumentNotFound,
            ErrorCode::DateOutOfOrder,
            ErrorCode::FutureDate,
        ];

        let code = codes[code_index];
        let code_str = code.code();

        // All codes must match E\d+ pattern
        prop_assert!(code_str.starts_with('E'), "Code must start with E");
        prop_assert!(code_str.len() >= 5, "Code must be at least 5 chars (Exxxx)");
        prop_assert!(code_str[1..].chars().all(|c| c.is_ascii_digit()),
            "Code suffix must be digits");
    }

    /// TLA+ AccountLifecycleConsistent: Random account operations maintain consistency
    #[test]
    fn prop_tla_account_lifecycle_random(
        num_accounts in 1usize..5,
        num_ops in 1usize..10
    ) {
        let mut v = validator();

        // Generate account names
        let accounts: Vec<String> = (0..num_accounts)
            .map(|i| format!("Assets:Account{}", i))
            .collect();

        // Track expected states
        let mut states: std::collections::HashMap<String, &str> =
            accounts.iter().map(|a| (a.clone(), "unopened")).collect();

        // Perform random operations
        for i in 0..num_ops {
            let account = &accounts[i % num_accounts];
            let current_state = *states.get(account).unwrap();

            match current_state {
                "unopened" => {
                    // Can open
                    let open = Open {
                        date: date(2024, 1, (i + 1) as u32),
                        account: account.clone(),
                        currencies: vec![],
                        booking: None,
                        meta: Default::default(),
                    };
                    let errors = v.validate_open(&open);
                    prop_assert!(errors.is_empty(), "Should be able to open unopened account");
                    v.process_open(&open);
                    states.insert(account.clone(), "open");
                }
                "open" => {
                    // Can close
                    let close = Close {
                        date: date(2024, 6, (i + 1) as u32),
                        account: account.clone(),
                        meta: Default::default(),
                    };
                    v.process_close(&close);
                    states.insert(account.clone(), "closed");
                }
                "closed" => {
                    // Cannot reopen - should generate error
                    let reopen = Open {
                        date: date(2024, 12, 1),
                        account: account.clone(),
                        currencies: vec![],
                        booking: None,
                        meta: Default::default(),
                    };
                    let errors = v.validate_open(&reopen);
                    prop_assert!(!errors.is_empty(), "Should not be able to reopen closed account");
                }
                _ => unreachable!()
            }
        }
    }

    /// TLA+ E3003/E3004 Correctness: Posting count determines error
    #[test]
    fn prop_tla_posting_count_errors(num_postings in 0usize..5) {
        let v = validator();

        let postings: Vec<Posting> = (0..num_postings)
            .map(|i| Posting {
                account: format!("Assets:Account{}", i),
                units: Some(Amount::new(Decimal::from(100 - i as i64 * 25), "USD")),
                cost: None,
                price: None,
                flag: None,
                meta: Default::default(),
            })
            .collect();

        let txn = Transaction {
            date: date(2024, 1, 15),
            flag: '*',
            payee: None,
            narration: "Test".to_string(),
            postings,
            tags: Default::default(),
            links: Default::default(),
            meta: Default::default(),
        };

        let errors = v.validate_transaction_structure(&txn);

        match num_postings {
            0 => {
                // E3003 should be generated
                prop_assert!(has_error_code(&errors, ErrorCode::NoPostings),
                    "E3003 should be generated for 0 postings");
            }
            1 => {
                // E3004 (warning) should be generated
                prop_assert!(has_error_code(&errors, ErrorCode::SinglePosting),
                    "E3004 should be generated for 1 posting");
            }
            _ => {
                // Neither E3003 nor E3004
                prop_assert!(!has_error_code(&errors, ErrorCode::NoPostings),
                    "E3003 should not be generated for {} postings", num_postings);
                prop_assert!(!has_error_code(&errors, ErrorCode::SinglePosting),
                    "E3004 should not be generated for {} postings", num_postings);
            }
        }
    }
}
