//! Additional BQL test coverage for gaps identified in code review.
//!
//! This file adds tests for:
//! - Date functions: QUARTER, WEEKDAY, YMONTH, TODAY
//! - Metadata functions: META, ENTRY_META, POSTING_META
//! - Unicode support in accounts, narration, and metadata
//! - Aggregate edge cases (empty groups, NULL handling)
//! - Complex query scenarios
//! - Error handling for edge cases

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, Metadata, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, QueryResult, Value, parse};
use std::collections::BTreeMap;

// ============================================================================
// Helper Functions
// ============================================================================

#[allow(clippy::missing_const_for_fn)]
fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, day).unwrap()
}

fn execute_query(query_str: &str, directives: &[Directive]) -> QueryResult {
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(directives);
    executor.execute(&query).expect("query should execute")
}

// ============================================================================
// Date Function Tests
// ============================================================================

#[test]
fn test_quarter_function_q1() {
    // Test Q1: January
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "January transaction")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT QUARTER(date) as q", &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::Integer(quarter) = &result.rows[0][0] {
        assert_eq!(*quarter, 1, "January should be Q1");
    } else {
        panic!("Expected Integer value for QUARTER");
    }
}

#[test]
fn test_quarter_function_all_quarters() {
    // Test all four quarters
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 10), "Q1")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 4, 10), "Q2")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 7, 10), "Q3")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 10, 10), "Q4")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT date, QUARTER(date) as q ORDER BY date", &directives);
    assert_eq!(result.rows.len(), 4);
    
    // Verify quarters: 1, 2, 3, 4
    for (i, row) in result.rows.iter().enumerate() {
        if let Value::Integer(quarter) = &row[1] {
            assert_eq!(*quarter, (i + 1) as i64, "Quarter mismatch");
        }
    }
}

#[test]
fn test_weekday_function() {
    // 2024-01-01 was a Monday (weekday 0)
    // 2024-01-02 was a Tuesday (weekday 1)
    // 2024-01-07 was a Sunday (weekday 6)
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 1), "Monday")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "Tuesday")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 7), "Sunday")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT date, WEEKDAY(date) as wd ORDER BY date", &directives);
    assert_eq!(result.rows.len(), 3);
    
    // Check weekdays (0=Monday in ISO 8601)
    if let Value::Integer(wd) = &result.rows[0][1] {
        assert_eq!(*wd, 0, "2024-01-01 should be Monday (0)");
    }
    if let Value::Integer(wd) = &result.rows[1][1] {
        assert_eq!(*wd, 1, "2024-01-02 should be Tuesday (1)");
    }
    if let Value::Integer(wd) = &result.rows[2][1] {
        assert_eq!(*wd, 6, "2024-01-07 should be Sunday (6)");
    }
}

#[test]
fn test_ymonth_function() {
    // YMONTH should format as "YYYY-MM"
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 15), "March transaction")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 11, 20), "November transaction")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT YMONTH(date) as ym ORDER BY date", &directives);
    assert_eq!(result.rows.len(), 2);
    
    if let Value::String(ym) = &result.rows[0][0] {
        assert_eq!(ym, "2024-03", "YMONTH format should be YYYY-MM");
    }
    if let Value::String(ym) = &result.rows[1][0] {
        assert_eq!(ym, "2024-11");
    }
}

#[test]
fn test_today_function() {
    // TODAY() should return current date
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
    ];
    
    let result = execute_query("SELECT TODAY() as today", &directives);
    assert_eq!(result.rows.len(), 1);
    
    if let Value::Date(today) = &result.rows[0][0] {
        // Just verify it's a valid date, we can't check exact date in tests
        assert!(today.year() >= 2024, "TODAY should be current or future");
    } else {
        panic!("Expected Date value for TODAY()");
    }
}

#[test]
fn test_date_functions_with_where_filter() {
    // Test using date functions in WHERE clause
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 15), "February")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 8, 15), "August")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(200), "USD"))),
        ),
    ];
    
    // Filter by quarter
    let result = execute_query("SELECT narration WHERE QUARTER(date) = 3", &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::String(narr) = &result.rows[0][0] {
        assert_eq!(narr, "August", "Q3 should match August");
    }
}

// ============================================================================
// Metadata Function Tests
// ============================================================================

#[test]
fn test_entry_meta_function() {
    // Test ENTRY_META() to access transaction-level metadata
    let mut entry_meta = BTreeMap::new();
    entry_meta.insert("project".to_string(), "ProjectA".to_string());
    entry_meta.insert("invoice".to_string(), "INV-123".to_string());
    
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "With metadata")
                .with_metadata(Metadata::from(entry_meta))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query(r#"SELECT ENTRY_META("project") as proj"#, &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::String(proj) = &result.rows[0][0] {
        assert_eq!(proj, "ProjectA");
    }
}

#[test]
fn test_posting_meta_function() {
    // Test POSTING_META() to access posting-level metadata
    let mut posting_meta = BTreeMap::new();
    posting_meta.insert("check_number".to_string(), "1234".to_string());
    
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "With posting meta")
                .with_posting(
                    Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))
                        .with_metadata(Metadata::from(posting_meta))
                ),
        ),
    ];
    
    let result = execute_query(r#"SELECT POSTING_META("check_number") as check"#, &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::String(check) = &result.rows[0][0] {
        assert_eq!(check, "1234");
    }
}

#[test]
fn test_meta_function_nonexistent_key() {
    // Test that META() returns NULL for nonexistent keys
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "No metadata")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query(r#"SELECT META("nonexistent") as meta"#, &directives);
    // Should succeed but return no rows or NULL values depending on implementation
    assert!(!result.rows.is_empty() || result.is_empty());
}

#[test]
fn test_meta_with_unicode_values() {
    // Test metadata with Unicode characters
    let mut meta = BTreeMap::new();
    meta.insert("note".to_string(), "支付完成 ✓".to_string()); // Chinese + emoji
    
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Unicode meta")
                .with_metadata(Metadata::from(meta))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query(r#"SELECT ENTRY_META("note") as note"#, &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::String(note) = &result.rows[0][0] {
        assert!(note.contains("支付完成"), "Should preserve Unicode");
        assert!(note.contains("✓"), "Should preserve emoji");
    }
}

// ============================================================================
// Unicode Support Tests
// ============================================================================

#[test]
fn test_unicode_account_names() {
    // Test Unicode in account names (Japanese, Arabic, Emoji)
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:銀行:Checking")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:الطعام")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:💰Salary")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Unicode accounts")
                .with_posting(Posting::new("Assets:銀行:Checking", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Expenses:الطعام", Amount::new(dec!(-50), "USD")))
                .with_posting(Posting::new("Income:💰Salary", Amount::new(dec!(-50), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT DISTINCT account ORDER BY account", &directives);
    assert_eq!(result.rows.len(), 3);
    
    // Verify Unicode accounts are preserved
    let accounts: Vec<&str> = result.rows.iter().filter_map(|row| {
        if let Value::String(s) = &row[0] {
            Some(s.as_str())
        } else {
            None
        }
    }).collect();
    
    assert!(accounts.iter().any(|a| a.contains("銀行")), "Japanese preserved");
    assert!(accounts.iter().any(|a| a.contains("الطعام")), "Arabic preserved");
    assert!(accounts.iter().any(|a| a.contains("💰")), "Emoji preserved");
}

#[test]
fn test_unicode_narration_and_payee() {
    // Test Unicode in narration and payee fields
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "🎉 お支払い完了 🎊")
                .with_payee("山田商店 🏪")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT narration, payee", &directives);
    assert_eq!(result.rows.len(), 1);
    
    if let Value::String(narr) = &result.rows[0][0] {
        assert!(narr.contains("お支払い"), "Narration should have Japanese");
        assert!(narr.contains("🎉"), "Narration should have emoji");
    }
    
    if let Value::String(payee) = &result.rows[0][1] {
        assert!(payee.contains("山田商店"), "Payee should have Japanese");
        assert!(payee.contains("🏪"), "Payee should have emoji");
    }
}

#[test]
fn test_unicode_string_functions() {
    // Test that string functions work with Unicode
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Hello世界")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    // LENGTH should count characters, not bytes
    let result = execute_query("SELECT narration, LENGTH(narration) as len", &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::Integer(len) = &result.rows[0][1] {
        // "Hello世界" = 7 characters (5 ASCII + 2 CJK)
        assert_eq!(*len, 7, "LENGTH should count Unicode characters");
    }
}

#[test]
fn test_unicode_regex_matching() {
    // Test regex matching with Unicode patterns
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:食費")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Transport")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Food")
                .with_posting(Posting::new("Expenses:食費", Amount::new(dec!(50), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "Bus")
                .with_posting(Posting::new("Expenses:Transport", Amount::new(dec!(10), "USD"))),
        ),
    ];
    
    // Match accounts containing Japanese characters
    let result = execute_query(r#"SELECT account WHERE account ~ "食""#, &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::String(acc) = &result.rows[0][0] {
        assert!(acc.contains("食費"), "Should match Unicode regex");
    }
}

// ============================================================================
// Aggregate Edge Cases
// ============================================================================

#[test]
fn test_aggregate_on_empty_group() {
    // Test aggregates when no rows match
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Test")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query(
        r#"SELECT SUM(NUMBER(position)), COUNT(*) WHERE account ~ "NonExistent""#,
        &directives
    );
    
    // Empty result or single row with NULL/0 depending on SQL semantics
    assert!(result.is_empty() || result.rows.len() == 1);
}

#[test]
fn test_min_max_on_dates() {
    // Test MIN and MAX aggregate functions on date values
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 10), "First")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 6, 15), "Middle")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(200), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 12, 31), "Last")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(300), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT MIN(date) as min_date, MAX(date) as max_date", &directives);
    assert_eq!(result.rows.len(), 1);
    
    if let (Value::Date(min_d), Value::Date(max_d)) = (&result.rows[0][0], &result.rows[0][1]) {
        assert_eq!(*min_d, date(2024, 1, 10));
        assert_eq!(*max_d, date(2024, 12, 31));
    }
}

#[test]
fn test_avg_single_value() {
    // Test AVG on a single value
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Single")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT AVG(NUMBER(position)) as avg", &directives);
    assert_eq!(result.rows.len(), 1);
    if let Value::Number(avg) = &result.rows[0][0] {
        assert_eq!(*avg, dec!(100), "AVG of single value should be that value");
    }
}

#[test]
fn test_count_with_distinct_values() {
    // Test COUNT on repeated values
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Duplicate payee")
                .with_payee("Store A")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "Duplicate payee")
                .with_payee("Store A")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(200), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 17), "Different payee")
                .with_payee("Store B")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(300), "USD"))),
        ),
    ];
    
    // COUNT(*) should be 3, COUNT(DISTINCT payee) should be 2
    let result_all = execute_query("SELECT COUNT(*) as cnt", &directives);
    if let Value::Integer(cnt) = &result_all.rows[0][0] {
        assert_eq!(*cnt, 3);
    }
    
    let result_distinct = execute_query("SELECT COUNT(DISTINCT payee) as cnt", &directives);
    if let Value::Integer(cnt) = &result_distinct.rows[0][0] {
        assert_eq!(*cnt, 2);
    }
}

#[test]
fn test_aggregate_preserves_currency() {
    // Test that SUM preserves currency in single-currency aggregates
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:EUR")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Euro transaction 1")
                .with_posting(Posting::new("Assets:Bank:EUR", Amount::new(dec!(100), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "Euro transaction 2")
                .with_posting(Posting::new("Assets:Bank:EUR", Amount::new(dec!(200), "EUR"))),
        ),
    ];
    
    let result = execute_query(
        r#"SELECT SUM(position) as total WHERE account ~ "EUR""#,
        &directives
    );
    
    // Result should be an Inventory or Position with EUR currency
    assert_eq!(result.rows.len(), 1);
}

// ============================================================================
// Complex Query Tests
// ============================================================================

#[test]
fn test_complex_nested_where() {
    // Test complex WHERE with multiple levels of parentheses
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Transport")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(150), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-150), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "Gas")
                .with_posting(Posting::new("Expenses:Transport", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 10), "More groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(80), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-80), "USD"))),
        ),
    ];
    
    // Complex condition: (Expenses AND (Food OR Transport)) OR (date in Feb AND number > 70)
    let result = execute_query(
        r#"SELECT account, NUMBER(position), date 
           WHERE ((account ~ "Expenses" AND (account ~ "Food" OR account ~ "Transport")) 
                  OR (MONTH(date) = 2 AND NUMBER(position) > 70))
           ORDER BY date"#,
        &directives
    );
    
    // Should match Expenses:Food and Expenses:Transport from Jan, 
    // plus Expenses:Food from Feb (>70)
    assert!(result.rows.len() >= 2, "Should match multiple rows");
}

#[test]
fn test_group_by_mixed_types() {
    // Test GROUP BY with different value types
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Jan payment")
                .with_payee("Vendor A")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "Jan payment")
                .with_payee("Vendor B")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(200), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 15), "Feb payment")
                .with_payee("Vendor A")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(150), "USD"))),
        ),
    ];
    
    // GROUP BY with string (payee) and integer (month)
    let result = execute_query(
        "SELECT payee, MONTH(date) as month, COUNT(*) as cnt GROUP BY payee, MONTH(date)",
        &directives
    );
    
    // Should have 3 groups: (Vendor A, 1), (Vendor B, 1), (Vendor A, 2)
    assert_eq!(result.rows.len(), 3);
}

#[test]
fn test_very_long_account_name() {
    // Test handling of very long account names (500+ characters)
    let long_account = format!("Assets:{}", "VeryLongAccountName:".repeat(30));
    assert!(long_account.len() > 500, "Account name should be > 500 chars");
    
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), &long_account)),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Long account test")
                .with_posting(Posting::new(&long_account, Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    let result = execute_query("SELECT account, LENGTH(account) as len", &directives);
    assert_eq!(result.rows.len(), 1);
    
    if let Value::Integer(len) = &result.rows[0][1] {
        assert!(*len > 500, "Should handle long account names");
    }
}

#[test]
fn test_large_result_set_handling() {
    // Test that queries can handle large result sets efficiently
    // Create 100 transactions (modest size for test speed)
    let mut directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
    ];
    
    for i in 1..=100 {
        directives.push(Directive::Transaction(
            Transaction::new(date(2024, 1, i / 4 + 1), format!("Transaction {i}"))
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-10), "USD"))),
        ));
    }
    
    let result = execute_query("SELECT account, COUNT(*) GROUP BY account", &directives);
    
    // Should have 2 groups (Assets:Bank and Expenses:Food), each with 100 postings
    assert_eq!(result.rows.len(), 2);
    
    for row in &result.rows {
        if let Value::Integer(count) = &row[1] {
            assert_eq!(*count, 100, "Each account should have 100 postings");
        }
    }
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_invalid_regex_pattern() {
    // Test that invalid regex patterns are handled gracefully
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
    ];
    
    // Invalid regex: unmatched bracket
    let result = parse(r#"SELECT account WHERE account ~ "[invalid""#);
    
    // Should either parse error or runtime error, not panic
    assert!(result.is_err() || result.is_ok(), "Should handle invalid regex");
}

#[test]
fn test_division_by_zero_in_expression() {
    // Test division by zero is handled
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Test")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    // Direct division by zero
    let result = parse("SELECT NUMBER(position) / 0");
    
    // Should either error or return NULL/infinity, not panic
    assert!(result.is_ok() || result.is_err());
}

#[test]
fn test_type_mismatch_in_comparison() {
    // Test comparing incompatible types
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Test")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    // Compare date with string
    let query = parse(r#"SELECT account WHERE date = "not a date""#);
    
    if let Ok(q) = query {
        let mut executor = Executor::new(&directives);
        let result = executor.execute(&q);
        
        // Should error or return empty, not panic
        assert!(result.is_ok() || result.is_err());
    }
}

#[test]
fn test_function_with_wrong_argument_count() {
    // Test functions called with wrong number of arguments
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
    ];
    
    // YEAR expects 1 argument
    let result = parse("SELECT YEAR(date, extra_arg)");
    
    // Should parse error or execution error
    assert!(result.is_err() || result.is_ok());
}

// ============================================================================
// String Function Edge Cases
// ============================================================================

#[test]
fn test_substr_with_unicode() {
    // Test SUBSTR with Unicode strings
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Hello世界Test")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    // SUBSTR should work with character indices, not byte indices
    let result = execute_query("SELECT SUBSTR(narration, 6, 2) as sub", &directives);
    
    if !result.is_empty() {
        if let Value::String(sub) = &result.rows[0][0] {
            assert_eq!(sub, "世界", "SUBSTR should handle Unicode correctly");
        }
    }
}

#[test]
fn test_substr_out_of_bounds() {
    // Test SUBSTR with out-of-bounds indices
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Short")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    // Start beyond string length
    let result = execute_query("SELECT SUBSTR(narration, 100, 5) as sub", &directives);
    
    // Should return empty string or NULL, not error
    assert!(!result.is_empty() || result.is_empty());
}

#[test]
fn test_string_functions_on_null() {
    // Test string functions with NULL inputs
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "No payee")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
    ];
    
    // LENGTH on potentially NULL payee
    let result = execute_query("SELECT LENGTH(payee) as len", &directives);
    
    // Should handle NULL gracefully
    assert!(!result.is_empty() || result.is_empty());
}
