//! Integration tests for the BQL query engine.
//!
//! Tests cover parsing, execution, aggregation, filtering, and real-world query scenarios.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{parse, Executor, QueryResult, Value};

// ============================================================================
// Helper Functions
// ============================================================================

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, day).unwrap()
}

fn make_test_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Checking")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Savings")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Transport")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
        // Transaction 1: Salary
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Monthly salary")
                .with_payee("Employer")
                .with_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(dec!(-5000), "USD"),
                ))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(5000), "USD"),
                )),
        ),
        // Transaction 2: Groceries
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "Weekly groceries")
                .with_payee("Grocery Store")
                .with_tag("food")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(150), "USD")))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-150), "USD"),
                )),
        ),
        // Transaction 3: Gas
        Directive::Transaction(
            Transaction::new(date(2024, 1, 22), "Fill up")
                .with_payee("Gas Station")
                .with_posting(Posting::new(
                    "Expenses:Transport",
                    Amount::new(dec!(45), "USD"),
                ))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-45), "USD"),
                )),
        ),
        // Transaction 4: Transfer to savings
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
        // Transaction 5: More groceries
        Directive::Transaction(
            Transaction::new(date(2024, 1, 27), "More groceries")
                .with_payee("Grocery Store")
                .with_tag("food")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(80), "USD")))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-80), "USD"),
                )),
        ),
    ]
}

fn execute_query(query_str: &str, directives: &[Directive]) -> QueryResult {
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(directives);
    executor.execute(&query).expect("query should execute")
}

// ============================================================================
// Query Parsing Tests
// ============================================================================

#[test]
fn test_parse_simple_select() {
    let query = parse("SELECT account, number").expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Select(_)));
}

#[test]
fn test_parse_select_with_where() {
    let query = parse(r#"SELECT account WHERE account ~ "Expenses""#).expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Select(_)));
}

#[test]
fn test_parse_select_with_group_by() {
    let query = parse("SELECT account, SUM(number) GROUP BY account").expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Select(_)));
}

#[test]
fn test_parse_select_with_order_by() {
    let query = parse("SELECT account, number ORDER BY number DESC").expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Select(_)));
}

#[test]
fn test_parse_journal_query() {
    let query = parse(r#"JOURNAL "Assets:Bank""#).expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Journal(_)));
}

#[test]
fn test_parse_balances_query() {
    let query = parse("BALANCES").expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Balances(_)));
}

#[test]
fn test_parse_print_query() {
    let query = parse("PRINT").expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Print(_)));
}

#[test]
fn test_parse_error_invalid_query() {
    let result = parse("INVALID QUERY SYNTAX");
    assert!(result.is_err());
}

// ============================================================================
// Query Execution Tests
// ============================================================================

#[test]
fn test_execute_select_account() {
    let directives = make_test_directives();
    let result = execute_query("SELECT account", &directives);

    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 1);
    assert_eq!(result.columns[0], "account");
}

#[test]
fn test_execute_select_multiple_columns() {
    let directives = make_test_directives();
    let result = execute_query("SELECT account, position", &directives);

    assert_eq!(result.columns.len(), 2);
    assert!(result.columns.contains(&"account".to_string()));
    assert!(result.columns.contains(&"position".to_string()));
}

#[test]
fn test_execute_select_with_filter() {
    let directives = make_test_directives();
    let result = execute_query(r#"SELECT account WHERE account ~ "Expenses""#, &directives);

    // All results should be expense accounts
    for row in &result.rows {
        if let Value::String(account) = &row[0] {
            assert!(
                account.starts_with("Expenses"),
                "expected Expenses account, got {account}"
            );
        }
    }
}

#[test]
fn test_execute_select_with_date_filter() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT date, narration WHERE date >= 2024-01-20",
        &directives,
    );

    // All results should be on or after Jan 20
    for row in &result.rows {
        if let Value::Date(d) = &row[0] {
            assert!(
                *d >= date(2024, 1, 20),
                "expected date >= 2024-01-20, got {d}"
            );
        }
    }
}

// ============================================================================
// Aggregation Tests
// ============================================================================

#[test]
fn test_execute_sum_aggregation() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account, SUM(position) WHERE account ~ "Expenses:Food" GROUP BY account"#,
        &directives,
    );

    // Should have one row for Expenses:Food
    assert!(!result.is_empty());

    // Find the Expenses:Food row
    let food_row = result.rows.iter().find(|row| {
        if let Value::String(account) = &row[0] {
            account == "Expenses:Food"
        } else {
            false
        }
    });

    assert!(food_row.is_some(), "should have Expenses:Food row");
}

#[test]
fn test_execute_count_aggregation() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account, COUNT(*) WHERE account ~ "Expenses" GROUP BY account"#,
        &directives,
    );

    assert!(!result.is_empty());
}

#[test]
fn test_execute_group_by_account() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT account, SUM(position) GROUP BY account",
        &directives,
    );

    // Should have grouped results
    assert!(!result.is_empty());

    // Check that we have unique accounts
    let accounts: Vec<&String> = result
        .rows
        .iter()
        .filter_map(|row| {
            if let Value::String(s) = &row[0] {
                Some(s)
            } else {
                None
            }
        })
        .collect();

    // Each account should appear at most once
    let unique_accounts: std::collections::HashSet<_> = accounts.iter().collect();
    assert_eq!(accounts.len(), unique_accounts.len());
}

// ============================================================================
// Ordering Tests
// ============================================================================

#[test]
fn test_execute_order_by_date() {
    let directives = make_test_directives();
    let result = execute_query("SELECT date, narration ORDER BY date ASC", &directives);

    // Verify dates are in ascending order
    let dates: Vec<NaiveDate> = result
        .rows
        .iter()
        .filter_map(|row| {
            if let Value::Date(d) = &row[0] {
                Some(*d)
            } else {
                None
            }
        })
        .collect();

    for i in 1..dates.len() {
        assert!(
            dates[i] >= dates[i - 1],
            "dates should be in ascending order"
        );
    }
}

#[test]
fn test_execute_order_by_desc() {
    let directives = make_test_directives();
    let result = execute_query("SELECT date, narration ORDER BY date DESC", &directives);

    let dates: Vec<NaiveDate> = result
        .rows
        .iter()
        .filter_map(|row| {
            if let Value::Date(d) = &row[0] {
                Some(*d)
            } else {
                None
            }
        })
        .collect();

    for i in 1..dates.len() {
        assert!(
            dates[i] <= dates[i - 1],
            "dates should be in descending order"
        );
    }
}

// ============================================================================
// Function Tests
// ============================================================================

#[test]
fn test_execute_year_function() {
    let directives = make_test_directives();
    let result = execute_query("SELECT YEAR(date), narration", &directives);

    assert!(!result.is_empty());

    // All years should be 2024
    for row in &result.rows {
        if let Value::Integer(year) = &row[0] {
            assert_eq!(*year, 2024);
        }
    }
}

#[test]
fn test_execute_month_function() {
    let directives = make_test_directives();
    let result = execute_query("SELECT MONTH(date), narration", &directives);

    assert!(!result.is_empty());

    // All months should be 1 (January)
    for row in &result.rows {
        if let Value::Integer(month) = &row[0] {
            assert_eq!(*month, 1);
        }
    }
}

#[test]
fn test_execute_account_functions() {
    let directives = make_test_directives();
    let result = execute_query("SELECT account, ROOT(account), LEAF(account)", &directives);

    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 3);
}

// ============================================================================
// JOURNAL Query Tests
// ============================================================================

#[test]
fn test_execute_journal_query() {
    let directives = make_test_directives();
    let query = parse(r#"JOURNAL "Assets:Bank:Checking""#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    // Journal should show postings to Assets:Bank:Checking
    assert!(!result.is_empty());
}

// ============================================================================
// BALANCES Query Tests
// ============================================================================

#[test]
fn test_execute_balances_query() {
    let directives = make_test_directives();
    let query = parse("BALANCES").expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    // Should have balances for all accounts
    assert!(!result.is_empty());
}

#[test]
fn test_execute_balances_with_from() {
    let directives = make_test_directives();
    let query = parse(r"BALANCES FROM OPEN ON 2024-01-01").expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    // Should have balances
    assert!(!result.is_empty());
}

// ============================================================================
// Expression Tests
// ============================================================================

#[test]
fn test_execute_arithmetic_expression() {
    let directives = make_test_directives();
    let result = execute_query("SELECT NUMBER(position), NUMBER(position) * 2", &directives);

    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 2);
}

#[test]
fn test_execute_comparison_in_where() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT account, NUMBER(position) WHERE NUMBER(position) > 100",
        &directives,
    );

    // All numbers should be > 100
    for row in &result.rows {
        if let Value::Number(n) = &row[1] {
            assert!(*n > dec!(100), "expected number > 100, got {n}");
        }
    }
}

#[test]
fn test_execute_and_condition() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account, NUMBER(position) WHERE account ~ "Expenses" AND NUMBER(position) > 50"#,
        &directives,
    );

    for row in &result.rows {
        if let (Value::String(account), Value::Number(n)) = (&row[0], &row[1]) {
            assert!(account.starts_with("Expenses"));
            assert!(*n > dec!(50));
        }
    }
}

#[test]
fn test_execute_or_condition() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account WHERE account ~ "Food" OR account ~ "Transport""#,
        &directives,
    );

    for row in &result.rows {
        if let Value::String(account) = &row[0] {
            assert!(
                account.contains("Food") || account.contains("Transport"),
                "expected Food or Transport account, got {account}"
            );
        }
    }
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_execute_empty_result() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account WHERE account ~ "NonExistent""#,
        &directives,
    );

    assert!(result.is_empty());
}

#[test]
fn test_execute_with_no_directives() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT account", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_execute_distinct() {
    let directives = make_test_directives();
    let result = execute_query("SELECT DISTINCT payee", &directives);

    // Should have unique payees
    let payees: Vec<&String> = result
        .rows
        .iter()
        .filter_map(|row| {
            if let Value::String(s) = &row[0] {
                Some(s)
            } else {
                None
            }
        })
        .collect();

    let unique_payees: std::collections::HashSet<_> = payees.iter().collect();
    assert_eq!(payees.len(), unique_payees.len());
}

// ============================================================================
// Real-World Query Scenarios
// ============================================================================

#[test]
fn test_expense_summary_by_category() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account, SUM(position) WHERE account ~ "Expenses" GROUP BY account ORDER BY account"#,
        &directives,
    );

    assert!(!result.is_empty());
}

#[test]
fn test_monthly_spending() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT YEAR(date), MONTH(date), SUM(position) WHERE account ~ "Expenses" GROUP BY YEAR(date), MONTH(date)"#,
        &directives,
    );

    assert!(!result.is_empty());
}

#[test]
fn test_payee_analysis() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT payee, COUNT(*), SUM(position) GROUP BY payee",
        &directives,
    );

    assert!(!result.is_empty());
}

// ============================================================================
// New Operator Tests (BQL parity)
// ============================================================================

#[test]
fn test_not_regex_operator() {
    let directives = make_test_directives();
    // Select accounts that don't match "Expenses"
    let result = execute_query(
        r#"SELECT DISTINCT account WHERE account !~ "Expenses""#,
        &directives,
    );

    // Should return Assets and Income accounts
    for row in &result.rows {
        if let Value::String(account) = &row[0] {
            assert!(
                !account.contains("Expenses"),
                "Account {account} should not contain 'Expenses'"
            );
        }
    }
}

#[test]
fn test_modulo_operator() {
    let directives = make_test_directives();
    // Test modulo operator: year % 4 = 0 (2024 is divisible by 4)
    let result = execute_query(
        "SELECT DISTINCT YEAR(date) WHERE YEAR(date) % 4 = 0",
        &directives,
    );

    // All our test data is from 2024, which is divisible by 4
    assert!(
        !result.is_empty(),
        "Should have results for year 2024 (divisible by 4)"
    );
    for row in &result.rows {
        if let Value::Integer(year) = &row[0] {
            assert_eq!(*year % 4, 0, "Year {year} should be divisible by 4");
        }
    }
}

#[test]
fn test_is_null_operator() {
    let directives = make_test_directives();
    // Select transactions where payee is null (the transfer transaction)
    let result = execute_query("SELECT DISTINCT narration WHERE payee IS NULL", &directives);

    // The "Transfer to savings" transaction has no payee
    assert!(!result.is_empty());
    let has_transfer = result
        .rows
        .iter()
        .any(|row| matches!(&row[0], Value::String(s) if s.contains("Transfer")));
    assert!(
        has_transfer,
        "Should find the Transfer transaction with no payee"
    );
}

#[test]
fn test_is_not_null_operator() {
    let directives = make_test_directives();
    // Select transactions where payee is not null
    let result = execute_query("SELECT DISTINCT payee WHERE payee IS NOT NULL", &directives);

    // Should include Employer, Grocery Store, Gas Station
    assert!(!result.is_empty());
    for row in &result.rows {
        assert!(!matches!(&row[0], Value::Null), "Payee should not be null");
    }
}

// ============================================================================
// New Column Tests (BQL parity)
// ============================================================================

#[test]
fn test_type_column() {
    let directives = make_test_directives();
    let result = execute_query("SELECT DISTINCT type", &directives);

    assert!(!result.is_empty());
    // All rows should be "txn" for transactions
    for row in &result.rows {
        assert_eq!(row[0], Value::String("txn".to_string()));
    }
}

#[test]
fn test_description_column() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT description WHERE narration = "Monthly salary""#,
        &directives,
    );

    assert!(!result.is_empty());
    // Should be "Employer | Monthly salary"
    let has_correct_desc = result
        .rows
        .iter()
        .any(|row| matches!(&row[0], Value::String(s) if s == "Employer | Monthly salary"));
    assert!(
        has_correct_desc,
        "Description should combine payee and narration"
    );
}

#[test]
fn test_number_currency_columns() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT number, currency WHERE account ~ \"Expenses:Food\"",
        &directives,
    );

    assert!(!result.is_empty());
    for row in &result.rows {
        // Number should be a decimal
        assert!(matches!(&row[0], Value::Number(_)));
        // Currency should be USD
        assert_eq!(row[1], Value::String("USD".to_string()));
    }
}

#[test]
fn test_accounts_column() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT DISTINCT accounts WHERE narration = "Monthly salary""#,
        &directives,
    );

    assert!(!result.is_empty());
    // The salary transaction has Income:Salary and Assets:Bank:Checking
    for row in &result.rows {
        if let Value::StringSet(accounts) = &row[0] {
            assert!(accounts.len() >= 2, "Should have at least 2 accounts");
        }
    }
}

#[test]
fn test_other_accounts_column() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT account, other_accounts WHERE account ~ \"Expenses:\"",
        &directives,
    );

    assert!(!result.is_empty());
    for row in &result.rows {
        if let (Value::String(account), Value::StringSet(others)) = (&row[0], &row[1]) {
            // Other accounts should not contain the current account
            assert!(
                !others.contains(account),
                "other_accounts should not contain current account"
            );
        }
    }
}

#[test]
fn test_flatten_keyword_parsed() {
    // Test that FLATTEN is parsed correctly
    let query = parse("SELECT * FLATTEN").expect("should parse");
    match query {
        rustledger_query::Query::Select(sel) => {
            assert!(sel.flatten, "FLATTEN flag should be set");
        }
        _ => panic!("Expected SELECT query"),
    }
}

#[test]
fn test_flatten_without_keyword() {
    // Test that queries without FLATTEN have flatten=false
    let query = parse("SELECT *").expect("should parse");
    match query {
        rustledger_query::Query::Select(sel) => {
            assert!(!sel.flatten, "FLATTEN flag should not be set");
        }
        _ => panic!("Expected SELECT query"),
    }
}

// ============================================================================
// New Function Tests (BQL parity)
// ============================================================================

#[test]
fn test_int_function() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT INT(number) WHERE account ~ \"Expenses:Food\"",
        &directives,
    );
    assert!(!result.is_empty());
    for row in &result.rows {
        assert!(matches!(&row[0], Value::Integer(_) | Value::Null));
    }
}

#[test]
fn test_str_function() {
    let directives = make_test_directives();
    // STR converts a number to string
    let result = execute_query(
        "SELECT STR(number) WHERE account ~ \"Expenses:Food\"",
        &directives,
    );
    assert!(!result.is_empty());
    for row in &result.rows {
        // STR should return strings or null
        assert!(matches!(&row[0], Value::String(_) | Value::Null));
    }
}

#[test]
fn test_date_diff_function() {
    let directives = make_test_directives();
    // DATE_DIFF returns days between dates
    let result = execute_query(
        "SELECT DISTINCT DATE_DIFF(date, 2024-01-01) WHERE YEAR(date) = 2024",
        &directives,
    );
    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::Integer(days) = &row[0] {
            assert!(*days >= 0, "Days should be non-negative");
        }
    }
}

#[test]
fn test_date_add_function() {
    let directives = make_test_directives();
    let result = execute_query("SELECT DATE_ADD(date, 7)", &directives);
    assert!(!result.is_empty());
    for row in &result.rows {
        assert!(matches!(&row[0], Value::Date(_)));
    }
}

#[test]
fn test_maxwidth_function() {
    let directives = make_test_directives();
    let result = execute_query("SELECT MAXWIDTH(narration, 10)", &directives);
    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::String(s) = &row[0] {
            assert!(s.len() <= 10, "String should be truncated to 10 chars: {s}");
        }
    }
}

#[test]
fn test_joinstr_function() {
    let directives = make_test_directives();
    let result = execute_query("SELECT JOINSTR(tags)", &directives);
    assert!(!result.is_empty());
    // JOINSTR returns a comma-separated string
    for row in &result.rows {
        assert!(matches!(&row[0], Value::String(_)));
    }
}
