//! Extended integration tests for the BQL query engine.
//!
//! Tests cover missing aggregates, date functions, string functions, and complex clauses.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, QueryResult, Value, parse};

// ============================================================================
// Helper Functions
// ============================================================================

#[allow(clippy::missing_const_for_fn)]
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
        // Transaction 5: More groceries (different amount for min/max testing)
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
         // Transaction 6: Big purchase (for max testing)
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Big Purchase")
                .with_payee("Tech Store")
                .with_posting(Posting::new("Expenses:Tech", Amount::new(dec!(2000), "USD")))
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-2000), "USD"),
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
// Aggregate Function Tests
// ============================================================================

#[test]
fn test_aggregate_min_max() {
    let directives = make_test_directives();
    // MIN/MAX on amounts
    let result = execute_query(
        r#"SELECT MIN(number), MAX(number) WHERE account ~ "Expenses""#, 
        &directives
    );
    
    // Expenses: 150 (Food), 45 (Transport), 80 (Food), 2000 (Tech)
    // MIN: 45, MAX: 2000
    
    assert_eq!(result.rows.len(), 1);
    match &result.rows[0][0] {
        Value::Number(n) => assert_eq!(*n, dec!(45)),
        _ => panic!("Expected number for MIN"),
    }
    match &result.rows[0][1] {
        Value::Number(n) => assert_eq!(*n, dec!(2000)),
        _ => panic!("Expected number for MAX"),
    }
}

#[test]
fn test_aggregate_avg() {
    let directives = make_test_directives();
    // AVG on amounts for Expenses:Food
    // 150 + 80 = 230 / 2 = 115
    let result = execute_query(
        r#"SELECT AVG(number) WHERE account ~ "Expenses:Food""#, 
        &directives
    );
    
    assert_eq!(result.rows.len(), 1);
    match &result.rows[0][0] {
        Value::Number(n) => assert_eq!(*n, dec!(115)),
        _ => panic!("Expected number for AVG"),
    }
}

#[test]
fn test_aggregate_first_last() {
    let directives = make_test_directives();
    // FIRST/LAST based on date
    // Expenses sorted by date:
    // 2024-01-20: Food 150
    // 2024-01-22: Transport 45
    // 2024-01-27: Food 80
    // 2024-02-01: Tech 2000
    
    let result = execute_query(
        r#"SELECT FIRST(date), LAST(date), FIRST(number), LAST(number) WHERE account ~ "Expenses""#, 
        &directives
    );
    
    assert_eq!(result.rows.len(), 1);
    match &result.rows[0][0] {
        Value::Date(d) => assert_eq!(*d, date(2024, 1, 20)),
        _ => panic!("Expected date for FIRST(date)"),
    }
    match &result.rows[0][1] {
        Value::Date(d) => assert_eq!(*d, date(2024, 2, 1)),
        _ => panic!("Expected date for LAST(date)"),
    }
    match &result.rows[0][2] {
        Value::Number(n) => assert_eq!(*n, dec!(150)),
        _ => panic!("Expected number for FIRST(number)"),
    }
    match &result.rows[0][3] {
        Value::Number(n) => assert_eq!(*n, dec!(2000)),
        _ => panic!("Expected number for LAST(number)"),
    }
}

// ============================================================================
// Date Function Tests
// ============================================================================

#[test]
fn test_date_functions() {
    let directives = make_test_directives();
    
    // Test YEAR, MONTH, DAY extraction
    let result = execute_query(
        r#"SELECT date, YEAR(date), MONTH(date), DAY(date) WHERE date = 2024-01-20"#, 
        &directives
    );
    
    // Should match Jan 20 transaction (2 postings: Expenses:Food and Assets:Bank:Checking)
    assert!(result.rows.len() >= 1);
    
    match &result.rows[0][1] {
        Value::Integer(y) => assert_eq!(*y, 2024),
        _ => panic!("Expected integer for YEAR"),
    }
    match &result.rows[0][2] {
        Value::Integer(m) => assert_eq!(*m, 1),
        _ => panic!("Expected integer for MONTH"),
    }
    match &result.rows[0][3] {
        Value::Integer(d) => assert_eq!(*d, 20),
        _ => panic!("Expected integer for DAY"),
    }
}

#[test]
fn test_date_arithmetic() {
    let directives = make_test_directives();
    
    // Test DATE_ADD and DATE_DIFF
    // 2024-01-20 + 2 days = 2024-01-22
    // DATE_DIFF(2024-01-22, 2024-01-20) = 2
    
    let result = execute_query(
        r#"SELECT date, DATE_ADD(date, 2), DATE_DIFF(DATE_ADD(date, 2), date) WHERE date = 2024-01-20"#, 
        &directives
    );
    
    assert!(result.rows.len() >= 1);
    
    match &result.rows[0][1] {
        Value::Date(d) => assert_eq!(*d, date(2024, 1, 22)),
        _ => panic!("Expected date for DATE_ADD"),
    }
    match &result.rows[0][2] {
        Value::Integer(i) => assert_eq!(*i, 2),
        _ => panic!("Expected integer for DATE_DIFF"),
    }
}

#[test]
fn test_date_trunc() {
    let directives = make_test_directives();
    
    // Test DATE_TRUNC('month', date)
    // 2024-01-20 -> 2024-01-01
    
    let result = execute_query(
        r#"SELECT date, DATE_TRUNC("month", date) WHERE date = 2024-01-20"#, 
        &directives
    );
    
    assert!(result.rows.len() >= 1);
    
    match &result.rows[0][1] {
        Value::Date(d) => assert_eq!(*d, date(2024, 1, 1)),
        _ => panic!("Expected date for DATE_TRUNC"),
    }
}

// ============================================================================
// String Function Tests
// ============================================================================

#[test]
fn test_string_grep() {
    let directives = make_test_directives();
    
    // Test GREP matching
    let result = execute_query(
        r#"SELECT payee, GREP("Grocery", payee) WHERE payee ~ "Grocery""#, 
        &directives
    );
    
    assert!(result.rows.len() >= 1);
    match &result.rows[0][1] {
        Value::String(s) => assert_eq!(s, "Grocery"),
        _ => panic!("Expected string for GREP"),
    }
}

#[test]
fn test_string_subst() {
    let directives = make_test_directives();
    
    // Test SUBST
    let result = execute_query(
        r#"SELECT payee, SUBST("Grocery", "Supermarket", payee) WHERE payee ~ "Grocery""#, 
        &directives
    );
    
    assert!(result.rows.len() >= 1);
    match &result.rows[0][1] {
        Value::String(s) => assert_eq!(s, "Supermarket Store"),
        _ => panic!("Expected string for SUBST"),
    }
}

#[test]
fn test_string_manipulation() {
    let directives = make_test_directives();
    
    // UPPER, LOWER, LENGTH
    let result = execute_query(
        r#"SELECT payee, UPPER(payee), LOWER(payee), LENGTH(payee) WHERE payee = "Employer""#, 
        &directives
    );
    
    assert!(result.rows.len() >= 1);
    match &result.rows[0][1] {
        Value::String(s) => assert_eq!(s, "EMPLOYER"),
        _ => panic!("Expected string for UPPER"),
    }
    match &result.rows[0][2] {
        Value::String(s) => assert_eq!(s, "employer"),
        _ => panic!("Expected string for LOWER"),
    }
    match &result.rows[0][3] {
        Value::Integer(i) => assert_eq!(*i, 8),
        _ => panic!("Expected integer for LENGTH"),
    }
}

// ============================================================================
// Math Function Tests
// ============================================================================

#[test]
fn test_math_functions() {
    let directives = make_test_directives();
    
    // ABS, ROUND
    // -5000 -> 5000
    let result = execute_query(
        r#"SELECT number, ABS(number) WHERE number = -5000"#, 
        &directives
    );
    
    assert!(result.rows.len() >= 1);
    match &result.rows[0][1] {
        Value::Number(n) => assert_eq!(*n, dec!(5000)),
        _ => panic!("Expected number for ABS"),
    }
}

// ============================================================================
// Grouping and Having Tests
// ============================================================================

#[test]
fn test_having_aggregate_filter() {
    let directives = make_test_directives();
    
    // Filter groups where SUM(number) > 100
    // Expenses:Food: 150 + 80 = 230
    // Expenses:Transport: 45
    // Expenses:Tech: 2000
    
    let result = execute_query(
        r#"SELECT account, SUM(number) AS total 
           WHERE account ~ "Expenses" 
           GROUP BY account 
           HAVING total > 100"#, 
        &directives
    );
    
    // Should include Food (230) and Tech (2000), but not Transport (45)
    let accounts: Vec<String> = result.rows.iter().map(|row| {
        match &row[0] {
            Value::String(s) => s.clone(),
            _ => String::new(),
        }
    }).collect();
    
    assert!(accounts.contains(&"Expenses:Food".to_string()));
    assert!(accounts.contains(&"Expenses:Tech".to_string()));
    assert!(!accounts.contains(&"Expenses:Transport".to_string()));
}

#[test]
fn test_having_count() {
    let directives = make_test_directives();
    
    // Expenses:Food has 2 transactions
    // Expenses:Transport has 1 transaction
    
    let result = execute_query(
        r#"SELECT account, COUNT(*) AS cnt 
           WHERE account ~ "Expenses" 
           GROUP BY account 
           HAVING cnt > 1"#, 
        &directives
    );
    
    assert_eq!(result.rows.len(), 1);
    match &result.rows[0][0] {
        Value::String(s) => assert_eq!(s, "Expenses:Food"),
        _ => panic!("Expected string"),
    }
}
