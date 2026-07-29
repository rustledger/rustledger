//! Unit tests for the executor — moved out of the 4458-line god-module.
//! `super` is the `executor` module (mod.rs), so the original `use super::*`
//! and private-item access resolve exactly as before.

use super::types::{hash_row, hash_single_value};
use super::*;
use crate::parse;
use rust_decimal_macros::dec;
use rustledger_core::Metadata;
use rustledger_core::Posting;

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

fn sample_directives() -> Vec<Directive> {
    vec![
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Coffee")
                .with_flag('*')
                .with_payee("Coffee Shop")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food:Coffee",
                    Amount::new(dec!(5.00), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-5.00), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "Groceries")
                .with_flag('*')
                .with_payee("Supermarket")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food:Groceries",
                    Amount::new(dec!(50.00), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-50.00), "USD"),
                )),
        ),
    ]
}

#[test]
fn test_simple_select() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    let query = parse("SELECT date, account").unwrap();
    let result = executor.execute(&query).unwrap();

    assert_eq!(result.columns, vec!["date", "account"]);
    assert_eq!(result.len(), 4); // 2 transactions × 2 postings
}

#[test]
fn test_where_clause() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    let query = parse("SELECT account WHERE account ~ \"Expenses:\"").unwrap();
    let result = executor.execute(&query).unwrap();

    assert_eq!(result.len(), 2); // Only expense postings
}

#[test]
fn test_balances() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    let query = parse("BALANCES").unwrap();
    let result = executor.execute(&query).unwrap();

    assert_eq!(result.columns, vec!["account", "balance"]);
    assert!(result.len() >= 3); // At least 3 accounts
}

/// `SELECT *` expands to the `WILDCARD_COLUMNS` name list (mod.rs) and a
/// parallel hand-written value-push (evaluation.rs), coupled only by a
/// comment. This guards the two against drift: adding a name without a value
/// (or vice versa) would make every `SELECT *` row a different width than its
/// header, which this catches.
#[test]
fn test_wildcard_columns_align_with_value_push() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&parse("SELECT *").unwrap()).unwrap();

    let expected: Vec<String> = WILDCARD_COLUMNS.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(
        result.columns, expected,
        "SELECT * header != WILDCARD_COLUMNS"
    );
    assert!(
        !result.rows.is_empty(),
        "SELECT * over the sample produced no rows"
    );
    for row in &result.rows {
        assert_eq!(
            row.len(),
            WILDCARD_COLUMNS.len(),
            "wildcard row width {} != WILDCARD_COLUMNS len {} — the value-push drifted from the name list",
            row.len(),
            WILDCARD_COLUMNS.len()
        );
    }
}

#[test]
fn test_account_functions() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test LEAF function
    let query = parse("SELECT DISTINCT LEAF(account) WHERE account ~ \"Expenses:\"").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2); // Coffee, Groceries

    // Test ROOT function
    let query = parse("SELECT DISTINCT ROOT(account)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2); // Expenses, Assets

    // Test PARENT function
    let query = parse("SELECT DISTINCT PARENT(account) WHERE account ~ \"Expenses:\"").unwrap();
    let result = executor.execute(&query).unwrap();
    assert!(!result.is_empty()); // At least "Expenses:Food"
}

#[test]
fn test_min_max_aggregate() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test MIN(date)
    let query = parse("SELECT MIN(date)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15)));

    // Test MAX(date)
    let query = parse("SELECT MAX(date)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 16)));
}

#[test]
fn test_order_by() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    let query = parse("SELECT date, account ORDER BY date DESC").unwrap();
    let result = executor.execute(&query).unwrap();

    // Should have all postings, ordered by date descending
    assert_eq!(result.len(), 4);
    // First row should be from 2024-01-16 (later date)
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 16)));
}

#[test]
fn order_by_raw_column_when_aliased_in_select() {
    // #1627: ORDER BY a raw column that is aliased in SELECT must not fail with
    // "column not found". The alias renames the output column, but the raw name
    // is still a valid sort reference — a hidden sort column is appended and
    // stripped after sorting.
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Aggregate: alias the grouped column, then ORDER BY the raw column.
    let aliased = executor
        .execute(&parse("SELECT date AS d GROUP BY date ORDER BY date").unwrap())
        .expect("ORDER BY raw column should resolve even when aliased (#1627)");
    // The hidden `date` sort column is stripped; only the aliased column shows.
    assert_eq!(aliased.columns, vec!["d"]);

    // Same result as ORDER BY <alias> (the documented workaround) and as the
    // un-aliased form.
    let by_alias = executor
        .execute(&parse("SELECT date AS d GROUP BY date ORDER BY d").unwrap())
        .unwrap();
    assert_eq!(aliased.rows, by_alias.rows);

    let unaliased = executor
        .execute(&parse("SELECT date GROUP BY date ORDER BY date").unwrap())
        .unwrap();
    assert_eq!(aliased.rows, unaliased.rows);

    // DESC and the non-aggregate form must resolve too.
    executor
        .execute(&parse("SELECT date AS d GROUP BY date ORDER BY date DESC").unwrap())
        .expect("aliased ORDER BY ... DESC should resolve (#1627)");
    executor
        .execute(&parse("SELECT date AS d ORDER BY date").unwrap())
        .expect("non-aggregate aliased ORDER BY should resolve (#1627)");
}

#[test]
fn test_hash_value_all_variants() {
    use rustledger_core::{Cost, Inventory, Position};

    // Test that all Value variants can be hashed without panic
    let values = vec![
        Value::String("test".to_string()),
        Value::Number(dec!(123.45)),
        Value::Integer(42),
        Value::Date(date(2024, 1, 15)),
        Value::Boolean(true),
        Value::Boolean(false),
        Value::Amount(Amount::new(dec!(100), "USD")),
        Value::Position(Box::new(Position::simple(Amount::new(dec!(10), "AAPL")))),
        Value::Position(Box::new(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ))),
        Value::Inventory(Box::new(Inventory::new())),
        Value::StringSet(vec!["tag1".to_string(), "tag2".to_string()]),
        Value::Null,
    ];

    // Hash each value and verify no panic
    for value in &values {
        let hash = hash_single_value(value);
        assert!(hash != 0 || matches!(value, Value::Null));
    }

    // Test that different values produce different hashes (usually)
    let hash1 = hash_single_value(&Value::String("a".to_string()));
    let hash2 = hash_single_value(&Value::String("b".to_string()));
    assert_ne!(hash1, hash2);

    // Test that same values produce same hashes
    let hash3 = hash_single_value(&Value::Integer(42));
    let hash4 = hash_single_value(&Value::Integer(42));
    assert_eq!(hash3, hash4);
}

#[test]
fn test_hash_row_distinct() {
    // Test hash_row for DISTINCT deduplication
    let row1 = vec![Value::String("a".to_string()), Value::Integer(1)];
    let row2 = vec![Value::String("a".to_string()), Value::Integer(1)];
    let row3 = vec![Value::String("b".to_string()), Value::Integer(1)];

    assert_eq!(hash_row(&row1), hash_row(&row2));
    assert_ne!(hash_row(&row1), hash_row(&row3));
}

#[test]
fn test_string_set_hash_order_independent() {
    // StringSet hash should be order-independent
    let set1 = Value::StringSet(vec!["a".to_string(), "b".to_string(), "c".to_string()]);
    let set2 = Value::StringSet(vec!["c".to_string(), "a".to_string(), "b".to_string()]);
    let set3 = Value::StringSet(vec!["b".to_string(), "c".to_string(), "a".to_string()]);

    let hash1 = hash_single_value(&set1);
    let hash2 = hash_single_value(&set2);
    let hash3 = hash_single_value(&set3);

    assert_eq!(hash1, hash2);
    assert_eq!(hash2, hash3);
}

#[test]
fn test_inventory_hash_includes_cost() {
    use rustledger_core::{Cost, Inventory, Position};

    // Two inventories with same units but different costs should hash differently
    let mut inv1 = Inventory::new();
    inv1.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(100), "USD"),
    ))
    .expect("fixture fits in Decimal");

    let mut inv2 = Inventory::new();
    inv2.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(200), "USD"),
    ))
    .expect("fixture fits in Decimal");

    let hash1 = hash_single_value(&Value::Inventory(Box::new(inv1)));
    let hash2 = hash_single_value(&Value::Inventory(Box::new(inv2)));

    assert_ne!(hash1, hash2);
}

#[test]
fn test_distinct_deduplication() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Without DISTINCT - should have duplicates (same flag '*' for all)
    let query = parse("SELECT flag").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 4); // One per posting, all have flag '*'

    // With DISTINCT - should deduplicate
    let query = parse("SELECT DISTINCT flag").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 1); // Deduplicated to 1 (all '*')
}

#[test]
fn test_limit_clause() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test LIMIT restricts result count
    let query = parse("SELECT date, account LIMIT 2").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2);

    // Test LIMIT 0 returns empty
    let query = parse("SELECT date LIMIT 0").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 0);

    // Test LIMIT larger than result set returns all
    let query = parse("SELECT date LIMIT 100").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 4);
}

#[test]
fn test_group_by_with_count() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Group by account root and count postings
    let query = parse("SELECT ROOT(account), COUNT(account) GROUP BY ROOT(account)").unwrap();
    let result = executor.execute(&query).unwrap();

    assert_eq!(result.columns.len(), 2);
    // Should have 2 groups: Assets and Expenses
    assert_eq!(result.len(), 2);
}

#[test]
fn test_count_aggregate() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Count all postings
    let query = parse("SELECT COUNT(account)").unwrap();
    let result = executor.execute(&query).unwrap();

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Integer(4));

    // Count with GROUP BY
    let query = parse("SELECT ROOT(account), COUNT(account) GROUP BY ROOT(account)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2); // Assets, Expenses
}

#[test]
fn test_count_wildcard_direct() {
    // count(*) in the direct postings path (no FROM tablename)
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Pure count(*) with no GROUP BY
    let query = parse("SELECT count(*)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Integer(4)); // 4 postings total

    // count(*) with GROUP BY in direct mode
    // Sample: Expenses:Food:Coffee (1), Assets:Bank:Checking (2), Expenses:Food:Groceries (1)
    let query = parse("SELECT account, count(*) GROUP BY account").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 3); // 3 distinct accounts
}

#[test]
fn test_count_wildcard_from_postings_table() {
    // count(*) against the named postings table: FROM postings
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // GROUP BY with count(*)
    let query = parse("SELECT account, count(*) FROM postings GROUP BY account").unwrap();
    let result = executor.execute(&query).unwrap();
    // 3 distinct accounts: Expenses:Food:Coffee, Assets:Bank:Checking, Expenses:Food:Groceries
    assert_eq!(result.len(), 3);
}

#[test]
fn test_count_wildcard_from_entries_table() {
    // count(*) against the named entries table: FROM entries
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    let query = parse("SELECT type, count(*) FROM entries GROUP BY type").unwrap();
    let result = executor.execute(&query).unwrap();
    // Only transactions in the sample data
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("transaction".to_string()));
    assert_eq!(result.rows[0][1], Value::Integer(2));
}

#[test]
fn test_count_wildcard_having() {
    // count(*) in HAVING clause on postings table
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Accounts with more than 0 postings (all 3 distinct accounts)
    let query =
        parse("SELECT account, count(*) AS cnt FROM postings GROUP BY account HAVING count(*) > 0")
            .unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 3);

    // Accounts with more than 1 posting (only Assets:Bank:Checking has 2)
    let query =
        parse("SELECT account, count(*) AS cnt FROM postings GROUP BY account HAVING count(*) > 1")
            .unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(
        result.rows[0][0],
        Value::String("Assets:Bank:Checking".to_string())
    );
    assert_eq!(result.rows[0][1], Value::Integer(2));
}

#[test]
fn test_journal_query() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // JOURNAL for Expenses account
    let query = parse("JOURNAL \"Expenses\"").unwrap();
    let result = executor.execute(&query).unwrap();

    // Should have columns for journal output
    assert!(result.columns.contains(&"account".to_string()));
    // Should only show expense account entries
    assert_eq!(result.len(), 2);
}

#[test]
fn test_print_query() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // PRINT outputs formatted directives
    let query = parse("PRINT").unwrap();
    let result = executor.execute(&query).unwrap();

    // PRINT returns single column "directive" with formatted output
    assert_eq!(result.columns.len(), 1);
    assert_eq!(result.columns[0], "directive");
    // Should have one row per directive (2 transactions)
    assert_eq!(result.len(), 2);
}

#[test]
fn test_empty_directives() {
    let directives: Vec<Directive> = vec![];
    let mut executor = Executor::new(&directives);

    // SELECT on empty directives
    let query = parse("SELECT date, account").unwrap();
    let result = executor.execute(&query).unwrap();
    assert!(result.is_empty());

    // BALANCES on empty directives
    let query = parse("BALANCES").unwrap();
    let result = executor.execute(&query).unwrap();
    assert!(result.is_empty());
}

#[test]
fn test_comparison_operators() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Less than comparison on dates
    let query = parse("SELECT date WHERE date < 2024-01-16").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2); // First transaction postings

    // Greater than comparison on year
    let query = parse("SELECT date WHERE year > 2023").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 4); // All 2024 postings

    // Equality comparison on day
    let query = parse("SELECT account WHERE day = 15").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2); // First transaction postings (Jan 15)
}

#[test]
fn test_logical_operators() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // AND operator
    let query = parse("SELECT account WHERE account ~ \"Expenses\" AND day > 14").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2); // Expense postings on Jan 15 and 16

    // OR operator
    let query = parse("SELECT account WHERE day = 15 OR day = 16").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 4); // All postings (both days)
}

#[test]
fn test_arithmetic_expressions() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Negation on integer
    let query = parse("SELECT -day WHERE day = 15").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 2);
    // Day 15 negated should be -15
    for row in &result.rows {
        if let Value::Integer(n) = &row[0] {
            assert_eq!(*n, -15);
        }
    }
}

#[test]
fn test_arithmetic_overflow_yields_null_not_panic() {
    // Regression (found by the `fuzz_query_execute` fuzzer): BQL `+`/`-`/`*` on
    // values exceeding rust_decimal's 96-bit range used to panic
    // ("Multiplication overflowed") instead of yielding NULL like div-by-zero.
    // `arithmetic_op` now uses the checked operators, so overflow → NULL.
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);
    // A single overflowing operation yields NULL (like div-by-zero).
    for q in [
        "SELECT 59999999999000999999990009 * 9999999",
        "SELECT 79228162514264337593543950335 + 79228162514264337593543950335",
        "SELECT 0 - 79228162514264337593543950335 - 79228162514264337593543950335",
    ] {
        let result = executor.execute(&parse(q).unwrap()).unwrap();
        assert!(
            result.rows.iter().all(|r| r[0] == Value::Null),
            "overflow should yield NULL, not panic, for: {q}"
        );
    }
    // The exact crash input the fuzzer minimized. Here the overflowing `*`
    // yields NULL which then propagates into further arithmetic, producing a
    // graceful Type error rather than NULL — the point of this regression is
    // only that execution must not PANIC (a `rust_decimal` overflow panic would
    // abort this test). Ok or Err are both acceptable.
    let _ = executor.execute(
        &parse("SELECT -899990000999900000+59999999999000999999990009*9999999/99").unwrap(),
    );
}

#[test]
fn test_first_last_aggregates() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // FIRST aggregate
    let query = parse("SELECT FIRST(date)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15)));

    // LAST aggregate
    let query = parse("SELECT LAST(date)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 16)));
}

#[test]
fn test_wildcard_select() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // SELECT * returns all postings with expanded column names
    let query = parse("SELECT *").unwrap();
    let result = executor.execute(&query).unwrap();

    // Wildcard expands to default column names (fixes issue #577)
    assert_eq!(
        result.columns,
        vec!["date", "flag", "payee", "narration", "account", "position"]
    );
    // Each row has expanded values matching the column names
    assert_eq!(result.len(), 4);
    assert_eq!(result.rows[0].len(), 6);
}

#[test]
fn test_wildcard_alias_rejected() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // SELECT * AS alias should fail - wildcard expands to multiple columns
    let query = parse("SELECT * AS data").unwrap();
    let result = executor.execute(&query);

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("Cannot alias wildcard"),
        "Expected wildcard alias error, got: {err}"
    );
}

#[test]
fn test_query_result_methods() {
    let mut result = QueryResult::new(vec!["col1".to_string(), "col2".to_string()]);

    // Initially empty
    assert!(result.is_empty());
    assert_eq!(result.len(), 0);

    // Add rows
    result.add_row(vec![Value::Integer(1), Value::String("a".to_string())]);
    assert!(!result.is_empty());
    assert_eq!(result.len(), 1);

    result.add_row(vec![Value::Integer(2), Value::String("b".to_string())]);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_type_cast_functions() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test INT function
    let query = parse("SELECT int(5.7)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(5));

    // Test DECIMAL function
    let query = parse("SELECT decimal(42)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Number(dec!(42)));

    // Test STR function
    let query = parse("SELECT str(123)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("123".to_string()));

    // Test BOOL function
    let query = parse("SELECT bool(1)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Boolean(true));

    let query = parse("SELECT bool(0)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Boolean(false));
}

/// Test that type casting functions work in aggregate context (issue #630).
#[test]
fn test_type_casting_in_aggregate_context() {
    let txn1 = Transaction::new(date(2024, 1, 15), "Item 1")
        .with_flag('*')
        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD")));

    let txn2 = Transaction::new(date(2024, 1, 16), "Item 2")
        .with_flag('*')
        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(20), "USD")))
        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-20), "USD")));

    let directives = vec![Directive::Transaction(txn1), Directive::Transaction(txn2)];
    let mut executor = Executor::new(&directives);

    // Test STR wrapping an aggregate - this was the issue in #630
    // Each account has 2 postings summed: Expenses:Food = 30, Assets:Cash = -30
    let query =
        parse("SELECT account, str(sum(number(units))) GROUP BY account ORDER BY account").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows.len(), 2);
    // Verify actual string values
    assert_eq!(result.rows[0][0], Value::String("Assets:Cash".to_string()));
    assert_eq!(result.rows[0][1], Value::String("-30".to_string()));
    assert_eq!(
        result.rows[1][0],
        Value::String("Expenses:Food".to_string())
    );
    assert_eq!(result.rows[1][1], Value::String("30".to_string()));

    // Test INT in aggregate context - verify truncation works
    let query =
        parse("SELECT account, int(sum(number(units))) GROUP BY account ORDER BY account").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][1], Value::Integer(-30));
    assert_eq!(result.rows[1][1], Value::Integer(30));

    // Test DECIMAL in aggregate context - verify count conversion
    let query =
        parse("SELECT account, decimal(count(*)) GROUP BY account ORDER BY account").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][1], Value::Number(dec!(2))); // 2 postings per account
    assert_eq!(result.rows[1][1], Value::Number(dec!(2)));

    // Test BOOL in aggregate context - count > 0 should be true
    let query = parse("SELECT account, bool(count(*)) GROUP BY account ORDER BY account").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][1], Value::Boolean(true));
    assert_eq!(result.rows[1][1], Value::Boolean(true));
}

/// Test INT truncation behavior with decimals.
#[test]
fn test_int_truncation() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test INT truncates toward zero (not floor/ceil)
    let query = parse("SELECT int(5.7)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(5));

    let query = parse("SELECT int(-5.7)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(-5));

    let query = parse("SELECT int(0.999)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(0));
}

/// Test type casting error cases.
#[test]
fn test_type_casting_errors() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // INT with non-numeric string should error
    let query = parse("SELECT int('not-a-number')").unwrap();
    let result = executor.execute(&query);
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .to_string()
            .contains("cannot parse 'not-a-number'")
    );

    // DECIMAL with invalid string should error
    let query = parse("SELECT decimal('invalid')").unwrap();
    let result = executor.execute(&query);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("cannot parse"));

    // BOOL with unrecognized string should error
    let query = parse("SELECT bool('maybe')").unwrap();
    let result = executor.execute(&query);
    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("cannot parse"));
}

#[test]
fn test_meta_functions() {
    // Create directives with metadata
    let mut txn_meta: Metadata = Metadata::default();
    txn_meta.insert(
        "source".to_string(),
        MetaValue::String("bank_import".to_string()),
    );

    let mut posting_meta: Metadata = Metadata::default();
    posting_meta.insert(
        "category".to_string(),
        MetaValue::String("food".to_string()),
    );

    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: Some("Coffee Shop".into()),
        narration: "Coffee".into(),
        tags: vec![],
        links: vec![],
        meta: txn_meta,
        postings: vec![
            rustledger_core::Spanned::synthesized(Posting {
                account: "Expenses:Food".into(),
                units: Some(rustledger_core::IncompleteAmount::Complete(Amount::new(
                    dec!(5),
                    "USD",
                ))),
                cost: None,
                price: None,
                flag: None,
                meta: posting_meta,
                comments: Vec::new(),
                trailing_comments: Vec::new(),
            }),
            rustledger_core::Spanned::synthesized(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-5), "USD"),
            )),
        ],
        trailing_comments: Vec::new(),
    };

    let directives = vec![Directive::Transaction(txn)];
    let mut executor = Executor::new(&directives);

    // Test META (posting metadata)
    let query = parse("SELECT meta('category') WHERE account ~ 'Expenses'").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("food".to_string()));

    // Test ENTRY_META (transaction metadata)
    let query = parse("SELECT entry_meta('source') WHERE account ~ 'Expenses'").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("bank_import".to_string()));

    // Test ANY_META (falls back to txn meta when posting meta missing)
    let query = parse("SELECT any_meta('source') WHERE account ~ 'Expenses'").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("bank_import".to_string()));

    // Test ANY_META (uses posting meta when available)
    let query = parse("SELECT any_meta('category') WHERE account ~ 'Expenses'").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("food".to_string()));

    // Test missing meta returns NULL
    let query = parse("SELECT meta('nonexistent') WHERE account ~ 'Expenses'").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);
}

#[test]
fn test_getitem_meta_eager_path_postings() {
    // Regression: getitem(meta, key) errored in the eager / `#postings`
    // path (only the per-row/lazy path handled metadata). `FROM #postings`
    // routes the function through `evaluate_function_on_values`.
    let mut posting_meta: Metadata = Metadata::default();
    posting_meta.insert(
        "category".to_string(),
        MetaValue::String("food".to_string()),
    );
    let txn = Transaction {
        date: date(2024, 1, 15),
        flag: '*',
        payee: None,
        narration: "Coffee".into(),
        tags: vec![],
        links: vec![],
        meta: Metadata::default(),
        postings: vec![
            rustledger_core::Spanned::synthesized(Posting {
                account: "Expenses:Food".into(),
                units: Some(rustledger_core::IncompleteAmount::Complete(Amount::new(
                    dec!(5),
                    "USD",
                ))),
                cost: None,
                price: None,
                flag: None,
                meta: posting_meta,
                comments: Vec::new(),
                trailing_comments: Vec::new(),
            }),
            rustledger_core::Spanned::synthesized(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-5), "USD"),
            )),
        ],
        trailing_comments: Vec::new(),
    };
    let directives = vec![Directive::Transaction(txn)];
    let mut executor = Executor::new(&directives);
    let query = parse("SELECT getitem(meta, 'category') FROM #postings WHERE account ~ 'Expenses'")
        .unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("food".to_string()));
}

/// After the dual-eval-path collapse, the `#postings` / subquery front-end
/// (`evaluate_subquery_expr`) routes function calls through the same registry
/// as top-level queries, so it inherits the extended-date functions (previously
/// `UnknownFunction` there) and the reconciled function bodies. The META
/// interception must still run first (covered by the getitem-meta test above).
#[test]
fn test_unified_registry_reaches_postings_subquery_path() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Extended-date function (DATE + DATE_ADD) in the #postings path — errored
    // `UnknownFunction` here before the registry was unified.
    let result = executor
        .execute(&parse("SELECT date_add(DATE('2024-01-15'), 1) FROM #postings").unwrap())
        .unwrap();
    assert!(!result.rows.is_empty(), "#postings produced no rows");
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 16)));

    // Reconciled MAXWIDTH (Python textwrap.shorten) in the #postings path —
    // the eager registry previously did naive truncation here.
    let result = executor
        .execute(&parse("SELECT maxwidth('hello world', 8) FROM #postings").unwrap())
        .unwrap();
    assert!(!result.rows.is_empty(), "#postings produced no rows");
    assert_eq!(result.rows[0][0], Value::String("[...]".to_string()));
}

#[test]
fn test_integer_modulo_floored_sign() {
    // Integer `%` uses Python floored modulo (sign follows the divisor);
    // decimal `%` stays truncated (matching Python `Decimal`).
    let directives = vec![Directive::Transaction(
        Transaction::new(date(2024, 1, 1), "x")
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1), "USD"))),
    )];
    let mut executor = Executor::new(&directives);
    for (q, expected) in [
        ("-5 % 3", 1i64),
        ("5 % -3", -1),
        ("-7 % 4", 1),
        ("7 % -4", -1),
    ] {
        let r = executor
            .execute(&parse(&format!("SELECT {q}")).unwrap())
            .unwrap();
        assert_eq!(r.rows[0][0], Value::Integer(expected), "for {q}");
    }
    // Decimal modulo is unchanged (truncated).
    let r = executor
        .execute(&parse("SELECT -5.0 % 3").unwrap())
        .unwrap();
    assert_eq!(r.rows[0][0], Value::Number(dec!(-2)));
}

#[test]
fn test_convert_function() {
    // Create directives with price information
    let price = rustledger_core::Price {
        date: date(2024, 1, 1),
        currency: "EUR".into(),
        amount: Amount::new(dec!(1.10), "USD"),
        meta: Metadata::default(),
    };

    let txn = Transaction::new(date(2024, 1, 15), "Test")
        .with_flag('*')
        .with_synthesized_posting(Posting::new("Assets:Euro", Amount::new(dec!(100), "EUR")))
        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-110), "USD")));

    let directives = vec![Directive::Price(price), Directive::Transaction(txn)];
    let mut executor = Executor::new(&directives);

    // Test CONVERT with amount
    let query = parse("SELECT convert(position, 'USD') WHERE account ~ 'Euro'").unwrap();
    let result = executor.execute(&query).unwrap();
    // 100 EUR × 1.10 = 110 USD
    match &result.rows[0][0] {
        Value::Amount(a) => {
            assert_eq!(a.number, dec!(110));
            assert_eq!(a.currency.as_ref(), "USD");
        }
        _ => panic!("Expected Amount, got {:?}", result.rows[0][0]),
    }
}

#[test]
fn test_date_functions() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test DATE construction from string
    let query = parse("SELECT date('2024-06-15')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 15)));

    // Test DATE construction from components
    let query = parse("SELECT date(2024, 6, 15)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 15)));

    // Test DATE_DIFF
    let query = parse("SELECT date_diff(date('2024-01-20'), date('2024-01-15'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(5));

    // Test DATE_ADD
    let query = parse("SELECT date_add(date('2024-01-15'), 10)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 25)));

    // Test DATE_TRUNC year
    let query = parse("SELECT date_trunc('year', date('2024-06-15'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 1)));

    // Test DATE_TRUNC month
    let query = parse("SELECT date_trunc('month', date('2024-06-15'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 1)));

    // Test DATE_PART
    let query = parse("SELECT date_part('month', date('2024-06-15'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(6));

    // Test PARSE_DATE with custom format
    let query = parse("SELECT parse_date('15/06/2024', '%d/%m/%Y')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 15)));

    // Test DATE_BIN with day stride
    let query = parse("SELECT date_bin('7 days', date('2024-01-15'), date('2024-01-01'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15))); // 15 is 14 days from 1, so bucket starts at 15

    // Test DATE_BIN with week stride
    let query = parse("SELECT date_bin('1 week', date('2024-01-20'), date('2024-01-01'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15))); // Week 3 starts at day 15

    // Test DATE_BIN with month stride
    let query =
        parse("SELECT date_bin('1 month', date('2024-06-15'), date('2024-01-01'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 1))); // June bucket

    // Test DATE_BIN with year stride
    let query = parse("SELECT date_bin('1 year', date('2024-06-15'), date('2020-01-01'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 1))); // 2024 bucket
}

#[test]
fn test_string_functions_extended() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test GREP - returns matched portion
    let query = parse("SELECT grep('Ex[a-z]+', 'Hello Expenses World')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("Expenses".to_string()));

    // Test GREP - no match returns NULL
    let query = parse("SELECT grep('xyz', 'Hello World')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);

    // Test GREPN - capture group (using [0-9] since \d is not escaped in BQL strings)
    let query = parse("SELECT grepn('([0-9]+)-([0-9]+)', '2024-01', 1)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("2024".to_string()));

    // Test SUBST - substitution
    let query = parse("SELECT subst('-', '/', '2024-01-15')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("2024/01/15".to_string()));

    // Test SPLITCOMP
    let query = parse("SELECT splitcomp('a:b:c', ':', 1)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("b".to_string()));

    // Test JOINSTR
    let query = parse("SELECT joinstr('hello', 'world')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("hello, world".to_string()));

    // Test MAXWIDTH - no truncation needed
    let query = parse("SELECT maxwidth('hello', 10)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("hello".to_string()));

    // Test MAXWIDTH - textwrap.shorten: neither word fits with the " [...]"
    // placeholder in width 8, so it collapses to the placeholder alone.
    let query = parse("SELECT maxwidth('hello world', 8)").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("[...]".to_string()));

    // JOINSTR skips NULL args (does not stringify them as "NULL") — a path that
    // the dual-eval collapse must preserve from the former lazy `eval_joinstr`.
    let query = parse("SELECT joinstr('a', NULL, 'b')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("a, b".to_string()));
}

#[test]
fn test_inventory_functions() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test EMPTY on sum of position (sum across all postings may cancel out)
    // Use a filter to get non-canceling positions
    let query = parse("SELECT empty(sum(position)) WHERE account ~ 'Assets'").unwrap();
    let result = executor.execute(&query).unwrap();
    // Should be a boolean (the actual value depends on sample data)
    assert!(matches!(result.rows[0][0], Value::Boolean(_)));

    // Test EMPTY with null returns true
    // (null handling is already tested in the function)

    // Test POSSIGN with debit account (Assets) - no sign change
    let query = parse("SELECT possign(100, 'Assets:Bank')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Number(rust_decimal::Decimal::from(100))
    );

    // Test POSSIGN with credit account (Income) - sign is negated
    let query = parse("SELECT possign(100, 'Income:Salary')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Number(rust_decimal::Decimal::from(-100))
    );

    // Test POSSIGN with Expenses (debit normal) - no sign change
    let query = parse("SELECT possign(50, 'Expenses:Food')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Number(rust_decimal::Decimal::from(50))
    );

    // Test POSSIGN with Liabilities (credit normal) - sign is negated
    let query = parse("SELECT possign(200, 'Liabilities:CreditCard')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Number(rust_decimal::Decimal::from(-200))
    );

    // Test POSSIGN with Equity (credit normal) - sign is negated
    let query = parse("SELECT possign(300, 'Equity:OpeningBalances')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Number(rust_decimal::Decimal::from(-300))
    );
}

#[test]
fn test_account_meta_functions() {
    use rustledger_core::{Close, Metadata, Open};

    // Create directives with Open/Close
    let mut open_meta = Metadata::default();
    open_meta.insert(
        "category".to_string(),
        MetaValue::String("checking".to_string()),
    );

    let directives = vec![
        Directive::Open(Open {
            date: date(2020, 1, 1),
            account: "Assets:Bank:Checking".into(),
            currencies: vec![],
            booking: None,
            meta: open_meta,
        }),
        Directive::Open(Open::new(date(2020, 2, 15), "Expenses:Food")),
        Directive::Close(Close::new(date(2024, 12, 31), "Assets:Bank:Checking")),
        // A transaction to have postings for the query context
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Coffee")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(5.00), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-5.00), "USD"),
                )),
        ),
    ];

    let mut executor = Executor::new(&directives);

    // Test OPEN_DATE - account with open directive
    let query = parse("SELECT open_date('Assets:Bank:Checking')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2020, 1, 1)));

    // Test CLOSE_DATE - account with close directive
    let query = parse("SELECT close_date('Assets:Bank:Checking')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 12, 31)));

    // Test OPEN_DATE - account without close directive
    let query = parse("SELECT close_date('Expenses:Food')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);

    // Test OPEN_META - get metadata from open directive
    let query = parse("SELECT open_meta('Assets:Bank:Checking', 'category')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::String("checking".to_string()));

    // Test OPEN_META - non-existent key
    let query = parse("SELECT open_meta('Assets:Bank:Checking', 'nonexistent')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);

    // Test with non-existent account
    let query = parse("SELECT open_date('NonExistent:Account')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);
}

#[test]
fn test_source_location_columns_return_null_without_sources() {
    // When using the regular constructor (without source location support),
    // the filename, lineno, and location columns should return Null
    let directives = vec![Directive::Transaction(Transaction {
        date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        flag: '*',
        payee: Some("Test".into()),
        narration: "Test transaction".into(),
        tags: vec![],
        links: vec![],
        meta: Metadata::default(),
        postings: vec![
            rustledger_core::Spanned::synthesized(Posting::new(
                "Assets:Bank",
                Amount::new(dec!(100), "USD"),
            )),
            rustledger_core::Spanned::synthesized(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(-100), "USD"),
            )),
        ],
        trailing_comments: Vec::new(),
    })];

    let mut executor = Executor::new(&directives);

    // Test filename column returns Null
    let query = parse("SELECT filename").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);

    // Test lineno column returns Null
    let query = parse("SELECT lineno").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);

    // Test location column returns Null
    let query = parse("SELECT location").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Null);
}

#[test]
fn test_source_location_columns_with_sources() {
    use rustledger_loader::SourceMap;
    use rustledger_parser::Spanned;
    use std::sync::Arc;

    // Create a source map with a test file
    let mut source_map = SourceMap::new();
    let source: Arc<str> = "2024-01-15 * \"Test\"\n  Assets:Bank  100 USD\n  Expenses:Food".into();
    let file_id = source_map.add_file("test.beancount".into(), source);

    // Create a spanned directive
    let txn = Transaction {
        date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        flag: '*',
        payee: Some("Test".into()),
        narration: "Test transaction".into(),
        tags: vec![],
        links: vec![],
        meta: Metadata::default(),
        postings: vec![
            rustledger_core::Spanned::synthesized(Posting::new(
                "Assets:Bank",
                Amount::new(dec!(100), "USD"),
            )),
            rustledger_core::Spanned::synthesized(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(-100), "USD"),
            )),
        ],
        trailing_comments: Vec::new(),
    };

    let spanned_directives = vec![Spanned {
        value: Directive::Transaction(txn),
        span: rustledger_parser::Span { start: 0, end: 50 },
        file_id: file_id as u16,
    }];

    let mut executor = Executor::new_with_sources(&spanned_directives, &source_map);

    // Test filename column returns the file path
    let query = parse("SELECT filename").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::String("test.beancount".to_string())
    );

    // Test lineno column returns line number
    let query = parse("SELECT lineno").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(1));

    // Test location column returns formatted location
    let query = parse("SELECT location").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::String("test.beancount:1".to_string())
    );
}

/// Regression: `JOURNAL` must iterate the directive source that is actually
/// populated. Under `new_with_sources` (the CLI / LSP path) `self.directives`
/// is empty and the data lives in `spanned_directives`; `execute_journal`
/// read the empty `self.directives` directly and returned **zero rows**,
/// regressing BQL `JOURNAL` compatibility 93%→77%. Now routed through
/// `resolved_directives()` (like `SELECT`/`PRINT`/`BALANCES`).
#[test]
fn test_journal_via_source_mapped_executor_returns_rows() {
    use rustledger_loader::SourceMap;
    use rustledger_parser::{Span, Spanned};
    use std::sync::Arc;

    let mut source_map = SourceMap::new();
    let source: Arc<str> =
        "2024-01-15 * \"Lunch\"\n  Assets:Cash  -12.00 USD\n  Expenses:Food  12.00 USD".into();
    let file_id = source_map.add_file("test.beancount".into(), source);

    let txn = Transaction {
        date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        flag: '*',
        payee: None,
        narration: "Lunch".into(),
        tags: vec![],
        links: vec![],
        meta: Metadata::default(),
        postings: vec![
            rustledger_core::Spanned::synthesized(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-12.00), "USD"),
            )),
            rustledger_core::Spanned::synthesized(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(12.00), "USD"),
            )),
        ],
        trailing_comments: Vec::new(),
    };
    let spanned_directives = vec![Spanned {
        value: Directive::Transaction(txn),
        span: Span { start: 0, end: 60 },
        file_id: file_id as u16,
    }];

    let mut executor = Executor::new_with_sources(&spanned_directives, &source_map);
    let query = parse("JOURNAL 'Assets'").unwrap();
    let result = executor.execute(&query).unwrap();

    // Exactly the Assets:Cash posting — was 0 rows before the fix.
    assert_eq!(
        result.rows.len(),
        1,
        "JOURNAL over a source-mapped executor returned {} rows (expected 1)",
        result.rows.len()
    );
    let account_col = result
        .columns
        .iter()
        .position(|c| c == "account")
        .expect("account column");
    assert_eq!(
        result.rows[0][account_col],
        Value::String("Assets:Cash".to_string())
    );
}

/// The system-table builders (BALANCES / #commodities / #events / …) and the
/// directive walks all route through `resolved_directives`, so they must see
/// the directives under `new_with_sources` (where they live in
/// `spanned_directives`, not `directives`) — the JOURNAL bug class. Run
/// a refactored system table (`#entries` — one row per directive, built by
/// `build_entries_table`) over a source-mapped executor and confirm it sees
/// the directives.
#[test]
fn test_system_table_via_source_mapped_executor() {
    use rustledger_parser::{Span, Spanned};

    let directives = sample_directives();
    let spanned: Vec<Spanned<Directive>> = directives
        .iter()
        .map(|d| Spanned {
            value: d.clone(),
            span: Span { start: 0, end: 1 },
            file_id: 0,
        })
        .collect();
    let source_map = rustledger_loader::SourceMap::new();
    let mut executor = Executor::new_with_sources(&spanned, &source_map);

    // `#entries` lists every directive; one of the builders collapsed onto
    // `resolved_directives` in this PR. Under `new_with_sources` the
    // directives live in `spanned_directives`, so a builder that read
    // `self.directives` directly would return zero rows here.
    let result = executor
        .execute(&parse("SELECT type FROM #entries").unwrap())
        .expect("#entries query");
    assert_eq!(
        result.len(),
        directives.len(),
        "#entries via a source-mapped executor returned {} rows (expected {}, one per directive)",
        result.len(),
        directives.len()
    );
}

#[test]
fn test_per_posting_source_location() {
    use rustledger_loader::SourceMap;
    use rustledger_parser::{Span, Spanned};
    use std::sync::Arc;

    // Line 1: header, line 2: Assets:Bank, line 3: Expenses:Food.
    let source: Arc<str> =
        "2024-01-15 * \"Test\"\n  Assets:Bank  100 USD\n  Expenses:Food  -100 USD".into();
    let mut source_map = SourceMap::new();
    let file_id = source_map.add_file("test.beancount".into(), source) as u16;

    // Postings carry their OWN (non-synthesized) spans: offset 20 = line 2,
    // offset 43 = line 3.
    let txn = Transaction {
        date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        flag: '*',
        payee: Some("Test".into()),
        narration: "Test".into(),
        tags: vec![],
        links: vec![],
        meta: Metadata::default(),
        postings: vec![
            Spanned {
                value: Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")),
                span: Span { start: 20, end: 42 },
                file_id,
            },
            Spanned {
                value: Posting::new("Expenses:Food", Amount::new(dec!(-100), "USD")),
                span: Span { start: 43, end: 67 },
                file_id,
            },
        ],
        trailing_comments: Vec::new(),
    };
    let spanned = vec![Spanned {
        value: Directive::Transaction(txn),
        span: Span { start: 0, end: 67 },
        file_id,
    }];
    let mut executor = Executor::new_with_sources(&spanned, &source_map);

    // Default path: each posting reports its OWN line (2, 3), not the
    // transaction's line (1).
    let result = executor
        .execute(&parse("SELECT lineno, account").unwrap())
        .unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(2));
    assert_eq!(result.rows[1][0], Value::Integer(3));

    // `#postings` table path resolves per-posting too.
    let result = executor
        .execute(&parse("SELECT lineno FROM #postings").unwrap())
        .unwrap();
    assert_eq!(result.rows[0][0], Value::Integer(2));
    assert_eq!(result.rows[1][0], Value::Integer(3));
}

#[test]
fn test_meta_includes_source_location() {
    use rustledger_loader::SourceMap;
    use rustledger_parser::{Span, Spanned};
    use std::sync::Arc;

    let source: Arc<str> =
        "2024-01-15 * \"Test\"\n  Assets:Bank  100 USD\n  Expenses:Food  -100 USD".into();
    let mut source_map = SourceMap::new();
    let file_id = source_map.add_file("test.beancount".into(), source) as u16;

    // Posting 1 (line 2) carries a user `category` key; posting 2 (line 3)
    // has none.
    let mut p1_meta = Metadata::default();
    p1_meta.insert(
        "category".to_string(),
        MetaValue::String("food".to_string()),
    );
    let txn = Transaction {
        date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        flag: '*',
        payee: Some("Test".into()),
        narration: "Test".into(),
        tags: vec![],
        links: vec![],
        meta: Metadata::default(),
        postings: vec![
            Spanned {
                value: Posting {
                    account: "Assets:Bank".into(),
                    units: Some(rustledger_core::IncompleteAmount::Complete(Amount::new(
                        dec!(100),
                        "USD",
                    ))),
                    cost: None,
                    price: None,
                    flag: None,
                    meta: p1_meta,
                    comments: Vec::new(),
                    trailing_comments: Vec::new(),
                },
                span: Span { start: 20, end: 42 },
                file_id,
            },
            Spanned {
                value: Posting::new("Expenses:Food", Amount::new(dec!(-100), "USD")),
                span: Span { start: 43, end: 67 },
                file_id,
            },
        ],
        trailing_comments: Vec::new(),
    };
    let spanned = vec![Spanned {
        value: Directive::Transaction(txn),
        span: Span { start: 0, end: 67 },
        file_id,
    }];
    let mut executor = Executor::new_with_sources(&spanned, &source_map);

    // meta() exposes synthetic filename/lineno per posting. (lineno is a
    // true Integer — matching the dedicated `lineno` column and beanquery's
    // integer lineno.)
    let r = executor
        .execute(&parse("SELECT meta('filename'), meta('lineno')").unwrap())
        .unwrap();
    assert_eq!(r.rows[0][0], Value::String("test.beancount".to_string()));
    assert_eq!(r.rows[0][1], Value::Integer(2));
    assert_eq!(r.rows[1][1], Value::Integer(3));

    // entry_meta uses the ENTRY (directive) line, not the posting's.
    let r = executor
        .execute(&parse("SELECT entry_meta('lineno')").unwrap())
        .unwrap();
    assert_eq!(r.rows[0][0], Value::Integer(1));

    // A user meta key still resolves and takes precedence.
    let r = executor
        .execute(&parse("SELECT meta('category') WHERE account ~ 'Bank'").unwrap())
        .unwrap();
    assert_eq!(r.rows[0][0], Value::String("food".to_string()));

    // The full meta column is augmented; getitem over it (and via #postings)
    // sees the synthetic keys as integers.
    let r = executor
        .execute(&parse("SELECT getitem(meta, 'lineno') FROM #postings").unwrap())
        .unwrap();
    assert_eq!(r.rows[0][0], Value::Integer(2));
    assert_eq!(r.rows[1][0], Value::Integer(3));
}

#[test]
fn test_postings_balance_excludes_filtered_commodities() {
    // Regression: `balance` in the #postings path accumulated over ALL
    // postings (pre-WHERE), so a stock leg leaked into a cash-account
    // balance. It must be a running total over WHERE-surviving rows only,
    // in entry order.
    let p = |account: &str, n, currency: &str| {
        rustledger_core::Spanned::synthesized(Posting::new(account, Amount::new(n, currency)))
    };
    let txn = |d, postings| {
        Directive::Transaction(Transaction {
            date: d,
            flag: '*',
            payee: None,
            narration: "t".into(),
            tags: vec![],
            links: vec![],
            meta: Metadata::default(),
            postings,
            trailing_comments: Vec::new(),
        })
    };
    let directives = vec![
        txn(
            date(2020, 1, 2),
            vec![
                p("Assets:Bank", dec!(5000), "USD"),
                p("Income:Salary", dec!(-5000), "USD"),
            ],
        ),
        txn(
            date(2020, 1, 3),
            vec![
                p("Assets:Stock", dec!(10), "AAPL"),
                p("Assets:Bank", dec!(-1000), "USD"),
            ],
        ),
        txn(
            date(2020, 1, 4),
            vec![
                p("Assets:Bank", dec!(2000), "USD"),
                p("Income:Salary", dec!(-2000), "USD"),
            ],
        ),
    ];
    let mut executor = Executor::new(&directives);
    let result = executor
        .execute(
            &parse(
                "SELECT getitem(balance, 'USD'), getitem(balance, 'AAPL') \
                     FROM #postings WHERE account = 'Assets:Bank' ORDER BY date",
            )
            .unwrap(),
        )
        .unwrap();
    assert_eq!(result.rows.len(), 3);
    let usd = |n| Value::Amount(Amount::new(n, "USD"));
    assert_eq!(result.rows[0][0], usd(dec!(5000)));
    assert_eq!(result.rows[1][0], usd(dec!(4000)));
    assert_eq!(result.rows[2][0], usd(dec!(6000)));
    // The AAPL leg (Assets:Stock, filtered out by WHERE) must NOT leak into
    // the cash balance — getitem returns NULL for a zero/absent commodity.
    assert_eq!(result.rows[0][1], Value::Null);
    assert_eq!(result.rows[1][1], Value::Null);
    assert_eq!(result.rows[2][1], Value::Null);

    // `SELECT *` expands to the `balance` column too — it must be recomputed
    // the same way (wildcard doesn't name `balance` explicitly).
    let result = executor
        .execute(
            &parse("SELECT * FROM #postings WHERE account = 'Assets:Bank' ORDER BY date").unwrap(),
        )
        .unwrap();
    let bal_col = result
        .columns
        .iter()
        .position(|c| c == "balance")
        .expect("balance column present");
    for row in &result.rows {
        if let Value::Inventory(inv) = &row[bal_col] {
            assert!(
                inv.units("AAPL").is_zero(),
                "SELECT * balance must not leak the filtered AAPL leg"
            );
        } else {
            panic!("expected an Inventory in the balance column");
        }
    }
}

#[test]
fn test_interval_function() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test interval with single argument (unit only, count=1)
    let query = parse("SELECT interval('month')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(1, IntervalUnit::Month))
    );

    // Test interval with two arguments (count, unit)
    let query = parse("SELECT interval(3, 'day')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(3, IntervalUnit::Day))
    );

    // Test interval with negative count
    let query = parse("SELECT interval(-2, 'week')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(-2, IntervalUnit::Week))
    );
}

#[test]
fn test_date_add_with_interval() {
    let directives = sample_directives();
    let mut executor = Executor::new(&directives);

    // Test date_add with interval
    let query = parse("SELECT date_add(date(2024, 1, 15), interval(1, 'month'))").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Date(rustledger_core::naive_date(2024, 2, 15).unwrap())
    );

    // Test date + interval using binary operator
    let query = parse("SELECT date(2024, 1, 15) + interval(1, 'year')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Date(rustledger_core::naive_date(2025, 1, 15).unwrap())
    );

    // Test date - interval
    let query = parse("SELECT date(2024, 3, 15) - interval(2, 'month')").unwrap();
    let result = executor.execute(&query).unwrap();
    assert_eq!(
        result.rows[0][0],
        Value::Date(rustledger_core::naive_date(2024, 1, 15).unwrap())
    );
}

/// Verify `query_references_column` walks every relevant query
/// part. The `collect_postings` optimization in #1080 hinges on
/// this — a false negative here would skip the cumulative-balance
/// clone for a query that depends on it.
#[test]
fn test_query_references_column_covers_all_query_parts() {
    // Helper: parse a SELECT and assert `balance` references in it.
    fn assert_refs(sql: &str, expected: bool) {
        let q = match parse(sql).unwrap() {
            Query::Select(s) => s,
            _ => panic!("expected Select for {sql:?}"),
        };
        assert_eq!(
            query_references_column(&q, "balance"),
            expected,
            "query_references_column(balance) wrong for {sql:?}"
        );
    }

    // Negative cases — no reference, should skip the clone.
    assert_refs("SELECT account FROM #postings", false);
    assert_refs("SELECT account WHERE account ~ '^Assets' LIMIT 10", false);

    // Positive cases — balance referenced in different positions.
    assert_refs("SELECT balance FROM #postings", true);
    assert_refs("SELECT account WHERE balance > 0", true);
    assert_refs("SELECT account ORDER BY balance", true);
    assert_refs("SELECT account GROUP BY balance", true);
    assert_refs(
        "SELECT account, sum(balance) FROM #postings GROUP BY account",
        true,
    );
    // Case-insensitive
    assert_refs("SELECT BALANCE FROM #postings", true);
    // Nested in function arg
    assert_refs("SELECT account WHERE units(balance) IS NOT NULL", true);
    // Nested in BETWEEN
    assert_refs("SELECT account WHERE balance BETWEEN 0 AND 100", true);
}

/// `expr_references_column` must traverse the OVER clause of a
/// window function, not just its args. A reference to `balance`
/// inside `PARTITION BY` / `ORDER BY` of an `OVER` clause must
/// trigger the snapshot path. Caught by Copilot review on PR
/// #1085 — pre-fix this returned a false negative and the resulting
/// query would have read a `None` `ctx.balance`.
#[test]
fn test_expr_references_column_walks_window_over_clause() {
    use crate::ast::{
        BinaryOp, BinaryOperator, OrderSpec, SortDirection, WindowFunction, WindowSpec,
    };

    let col_balance = Expr::Column("balance".to_string());
    let col_unrelated = Expr::Column("amount".to_string());

    // PARTITION BY references balance.
    let win_partition = Expr::Window(WindowFunction {
        name: "row_number".to_string(),
        args: vec![],
        over: WindowSpec {
            partition_by: Some(vec![col_balance.clone()]),
            order_by: None,
        },
    });
    assert!(
        expr_references_column(&win_partition, "balance"),
        "OVER (PARTITION BY balance) must be detected"
    );
    assert!(
        !expr_references_column(&win_partition, "account"),
        "should not match unrelated column"
    );

    // ORDER BY inside OVER references balance (nested in BinaryOp).
    let win_order = Expr::Window(WindowFunction {
        name: "row_number".to_string(),
        args: vec![],
        over: WindowSpec {
            partition_by: None,
            order_by: Some(vec![OrderSpec {
                expr: Expr::BinaryOp(Box::new(BinaryOp {
                    left: col_balance,
                    op: BinaryOperator::Add,
                    right: col_unrelated,
                })),
                direction: SortDirection::Asc,
            }]),
        },
    });
    assert!(
        expr_references_column(&win_order, "balance"),
        "OVER (ORDER BY balance + amount) must be detected"
    );
}
