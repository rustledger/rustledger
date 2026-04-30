//! Integration tests for the BQL query engine.
//!
//! Tests cover parsing, execution, aggregation, filtering, and real-world query scenarios.

use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Close, Commodity, CostSpec, Directive, Document, Event, Inventory, NaiveDate, Note,
    Open, Posting, PriceAnnotation, Transaction,
};
use rustledger_query::{Executor, QueryResult, Value, parse};

// ============================================================================
// Helper Functions
// ============================================================================

#[allow(clippy::missing_const_for_fn)]
fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
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
fn test_parse_balances_where_query() {
    let query = parse(r#"BALANCES WHERE account ~ "Assets:""#).expect("should parse");
    if let rustledger_query::Query::Balances(b) = query {
        assert!(b.where_clause.is_some());
    } else {
        panic!("Expected BALANCES query");
    }
}

#[test]
fn test_parse_balances_at_cost_where_query() {
    let query = parse(r#"BALANCES AT cost WHERE account ~ "Assets:""#).expect("should parse");
    if let rustledger_query::Query::Balances(b) = query {
        assert_eq!(b.at_function, Some("cost".to_string()));
        assert!(b.where_clause.is_some());
    } else {
        panic!("Expected BALANCES query");
    }
}

#[test]
fn test_execute_balances_where() {
    let directives = make_test_directives();
    let result = execute_query(r#"BALANCES WHERE account ~ "Expenses:""#, &directives);
    assert!(!result.is_empty());
    // All accounts should match the filter
    for row in &result.rows {
        if let Value::String(account) = &row[0] {
            assert!(account.starts_with("Expenses:"), "got {account}");
        } else {
            panic!("expected Value::String, got {:?}", row[0]);
        }
    }
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

#[test]
fn test_group_by_function_alias() {
    // GROUP BY should resolve SELECT aliases to the original expression
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT year(date) AS y, COUNT(*) AS cnt GROUP BY y ORDER BY y",
        &directives,
    );
    assert!(!result.is_empty());
    assert_eq!(result.columns[0], "y");
    assert_eq!(result.columns[1], "cnt");
    // All rows should have integer year values
    for row in &result.rows {
        assert!(matches!(row[0], Value::Integer(_)));
    }
}

#[test]
fn test_group_by_month_alias() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT month(date) AS m, COUNT(*) AS cnt GROUP BY m ORDER BY m",
        &directives,
    );
    assert!(!result.is_empty());
    // Month values should be 1-12
    for row in &result.rows {
        if let Value::Integer(m) = &row[0] {
            assert!((1..=12).contains(m));
        } else {
            panic!("Expected integer month");
        }
    }
}

#[test]
fn test_group_by_parent_alias() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT PARENT(account) AS parent, COUNT(*) AS cnt GROUP BY parent ORDER BY parent",
        &directives,
    );
    assert!(!result.is_empty());
    assert_eq!(result.columns[0], "parent");
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

/// Regression test for issue #938: `ROOT(account, n)` was rejecting integer
/// literals because the parser produced `Value::Number(Decimal)` for all
/// numeric literals, while `eval_root` strictly required `Value::Integer`.
/// Fixed by teaching the parser to emit `Literal::Integer` for whole-number
/// literals.
#[test]
fn test_root_with_segment_count() {
    let directives = make_test_directives();
    let result = execute_query("SELECT DISTINCT ROOT(account, 2)", &directives);

    assert_eq!(result.columns.len(), 1);
    let roots: std::collections::HashSet<String> = result
        .rows
        .iter()
        .filter_map(|row| match &row[0] {
            Value::String(s) => Some(s.clone()),
            _ => None,
        })
        .collect();

    // Test fixture has Assets:Bank:{Checking,Savings}, Expenses:{Food,Transport},
    // Income:Salary. ROOT(_, 2) keeps the first two segments.
    assert!(roots.contains("Assets:Bank"));
    assert!(roots.contains("Expenses:Food"));
    assert!(roots.contains("Expenses:Transport"));
    assert!(roots.contains("Income:Salary"));
}

/// Follow-up to #938: now that whole-number literals reach integer-only paths,
/// `ROOT(account, -1)` would previously cast `-1i64 as usize` to `usize::MAX`
/// and silently return the full account string. The fix in `eval_root` rejects
/// negatives with a typed error.
#[test]
fn test_root_rejects_negative_segment_count() {
    let directives = make_test_directives();
    let query = parse("SELECT ROOT(account, -1)").expect("query should parse");
    let mut executor = Executor::new(&directives);
    let err = executor
        .execute(&query)
        .expect_err("ROOT with negative segment count should error");
    let msg = err.to_string();
    assert!(
        msg.contains("non-negative"),
        "error should mention non-negative, got: {msg}"
    );
}

/// Regression test for POSSIGN with literal integer arguments. Before the
/// #938 fix, `POSSIGN(100, 'Income:Salary')` reached only the `Value::Number`
/// arm because literals were always parsed as Number. After the fix, the
/// arg becomes `Value::Integer(100)` and would have failed without the
/// matching arm added in `eval_possign`.
#[test]
fn test_possign_with_integer_literal_arg() {
    let directives = make_test_directives();

    // Income (credit-normal) → sign is negated
    let result = execute_query("SELECT POSSIGN(100, 'Income:Salary')", &directives);
    assert!(matches!(result.rows[0][0], Value::Number(n) if n == dec!(-100)));

    // Assets (debit-normal) → sign preserved
    let result = execute_query("SELECT POSSIGN(100, 'Assets:Bank:Checking')", &directives);
    assert!(matches!(result.rows[0][0], Value::Number(n) if n == dec!(100)));
}

/// Side-effect of the #938 fix: SUBSTR previously could not be invoked with
/// literal integer arguments because `(String, Integer, Integer)` arms in
/// `eval_substr` were unreachable when literals only produced `Number`.
#[test]
fn test_substr_with_integer_literal_args() {
    let directives = make_test_directives();
    let result = execute_query("SELECT DISTINCT SUBSTR(account, 0, 6)", &directives);

    let prefixes: std::collections::HashSet<String> = result
        .rows
        .iter()
        .filter_map(|row| match &row[0] {
            Value::String(s) => Some(s.clone()),
            _ => None,
        })
        .collect();

    // Account names like "Assets:Bank:Checking" → first 6 chars "Assets",
    // "Expenses:Food" → "Expens", "Income:Salary" → "Income".
    assert!(prefixes.contains("Assets"));
    assert!(prefixes.contains("Expens"));
    assert!(prefixes.contains("Income"));
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

/// Regression test for issue #955 (Bug 2): the JOURNAL `balance` column was
/// per-account, but Python `bean-query` translates JOURNAL to a SELECT where
/// `balance` is the cumulative inventory across every WHERE-filtered posting
/// (same semantic adopted for SELECT in PR #940). For a multi-account
/// `JOURNAL "Assets"` query, each row should show the running combined
/// inventory of all matched accounts up to that point — including currencies
/// that this row's account doesn't directly carry.
#[test]
fn test_journal_balance_is_cumulative_across_matched_accounts() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // Row 0: deposit USD into Assets:Cash.
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Deposit")
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(1000), "USD")))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1000), "USD"),
                )),
        ),
        // Row 1: buy AAPL in Assets:Brokerage. Different currency, different
        // account from the matched set. The balance here should include both
        // the USD held in Assets:Cash AND the new AAPL.
        Directive::Transaction(
            Transaction::new(date(2024, 3, 1), "Buy AAPL")
                .with_posting(Posting::new(
                    "Assets:Brokerage",
                    Amount::new(dec!(10), "AAPL"),
                ))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets""#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    assert_eq!(result.rows.len(), 2, "two assets postings, two rows");

    // Columns: date, flag, payee, narration, account, position, balance.
    // Row 0's balance: just the USD from Assets:Cash.
    let balance_0 = match &result.rows[0][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let positions_0 = balance_0.positions();
    assert_eq!(positions_0.len(), 1);
    assert_eq!(positions_0[0].units.currency.as_str(), "USD");
    assert_eq!(positions_0[0].units.number, dec!(1000));

    // Row 1's balance: the cumulative inventory now includes BOTH USD and
    // AAPL — even though row 1's posting is on Assets:Brokerage and only
    // adds AAPL. Per-account semantics would have lost the USD here.
    let balance_1 = match &result.rows[1][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let mut currencies: Vec<&str> = balance_1
        .positions()
        .iter()
        .map(|p| p.units.currency.as_str())
        .collect();
    currencies.sort_unstable();
    assert_eq!(
        currencies,
        vec!["AAPL", "USD"],
        "JOURNAL balance must be cumulative across matched accounts"
    );
}

/// Regression test for issue #955 (Bug 1): the JOURNAL position column was
/// emitting `Value::Amount(units)` instead of `Value::Position(pos)`,
/// silently dropping cost annotations. With cost-bearing postings, the
/// position column now preserves `{ cost }` so it matches `bean-query`.
#[test]
fn test_journal_position_column_preserves_cost() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets:Brokerage""#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    assert_eq!(result.rows.len(), 1, "expected one matching posting");

    // Columns: date, flag, payee, narration, account, position, balance.
    let position = &result.rows[0][5];
    let position_with_cost = match position {
        Value::Position(p) => p,
        other => panic!("expected Value::Position, got {other:?}"),
    };
    assert_eq!(position_with_cost.units.number, dec!(10));
    assert_eq!(position_with_cost.units.currency.as_str(), "AAPL");
    let cost = position_with_cost
        .cost
        .as_ref()
        .expect("position column must preserve cost annotation");
    assert_eq!(cost.number, dec!(150));
    assert_eq!(cost.currency.as_str(), "USD");
}

/// Regression test for #955 deep review: `JOURNAL ... FROM <filter>` should
/// only count postings from transactions that pass the FROM filter into the
/// cumulative balance. A wildcard `JOURNAL "Assets"` over a ledger with two
/// transactions, one matching the FROM filter and one not, should show only
/// one row whose balance reflects only the matched transaction.
#[test]
fn test_journal_from_clause_filters_cumulative_balance() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // 2024 transaction — should pass `FROM year = 2024` filter.
        Directive::Transaction(
            Transaction::new(date(2024, 6, 1), "Deposit 2024")
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-100), "USD"),
                )),
        ),
        // 2025 transaction — should NOT pass the filter.
        Directive::Transaction(
            Transaction::new(date(2025, 6, 1), "Deposit 2025")
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(500), "USD")))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-500), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets" FROM year = 2024"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    assert_eq!(result.rows.len(), 1, "FROM filter should drop the 2025 row");

    let balance = match &result.rows[0][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let positions = balance.positions();
    assert_eq!(positions.len(), 1);
    assert_eq!(
        positions[0].units.number,
        dec!(100),
        "cumulative balance must only include FROM-matched postings"
    );
}

/// Regression test for #955 deep review: `JOURNAL ... AT cost` and
/// `JOURNAL ... AT units` are documented to project the position column away
/// from the full Position shape. They should keep emitting `Value::Amount`,
/// not the Position the default branch now uses.
///
/// (Note: AT cost / AT units balance-column behavior diverges from
/// bean-query and is tracked separately in #957.)
#[test]
fn test_journal_at_cost_position_is_amount_not_position() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets:Brokerage" AT cost"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    assert_eq!(result.rows.len(), 1);
    let position = &result.rows[0][5];
    match position {
        Value::Amount(a) => {
            // cost-currency total = 10 × 150 USD = 1500 USD
            assert_eq!(a.number, dec!(1500));
            assert_eq!(a.currency.as_str(), "USD");
        }
        other => panic!("AT cost should produce Value::Amount, got {other:?}"),
    }
}

#[test]
fn test_journal_at_units_position_is_amount_not_position() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets:Brokerage" AT units"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    assert_eq!(result.rows.len(), 1);
    let position = &result.rows[0][5];
    match position {
        Value::Amount(a) => {
            // units only — cost dropped by definition of AT units.
            assert_eq!(a.number, dec!(10));
            assert_eq!(a.currency.as_str(), "AAPL");
        }
        other => panic!("AT units should produce Value::Amount, got {other:?}"),
    }
}

/// Regression test for issue #957: `JOURNAL ... AT cost` must collapse the
/// balance column to cost-currency totals, matching `bean-query`'s
/// `cost(balance)` translation. Previously the balance column showed the
/// full lot detail regardless of AT mode.
#[test]
fn test_journal_at_cost_collapses_balance_to_cost_currency() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets:Brokerage" AT cost"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    assert_eq!(result.rows.len(), 1);
    let balance = match &result.rows[0][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let positions = balance.positions();
    assert_eq!(positions.len(), 1);
    // 10 AAPL { 150 USD } collapsed to 1500 USD (cost-currency total).
    assert_eq!(positions[0].units.number, dec!(1500));
    assert_eq!(positions[0].units.currency.as_str(), "USD");
    assert!(
        positions[0].cost.is_none(),
        "AT cost balance must drop the lot annotation; got {:?}",
        positions[0].cost
    );
}

/// Lock-in test for #957 deep review: `JOURNAL ... AT cost FROM <filter>`
/// must compose correctly. The FROM clause filters which transactions enter
/// the cumulative balance, and AT cost then collapses what's there to cost
/// currency totals. Both mechanisms exist (covered separately by
/// `test_journal_from_clause_filters_cumulative_balance` and
/// `test_journal_at_cost_collapses_balance_to_cost_currency`); this asserts
/// they work together in the same row.
#[test]
fn test_journal_at_cost_with_from_clause_filters_then_collapses() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // 2024 transaction — should pass `FROM year = 2024` filter.
        Directive::Transaction(
            Transaction::new(date(2024, 6, 1), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
        // 2025 transaction — should be filtered out, not contribute to balance.
        Directive::Transaction(
            Transaction::new(date(2025, 6, 1), "Buy MSFT")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(20), "MSFT")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(300))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-6000), "USD"),
                )),
        ),
    ];
    let query =
        parse(r#"JOURNAL "Assets:Brokerage" AT cost FROM year = 2024"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    // Only the 2024 row passes FROM; AT cost collapses its balance to 1500 USD.
    assert_eq!(result.rows.len(), 1);
    let balance = match &result.rows[0][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let positions = balance.positions();
    assert_eq!(
        positions.len(),
        1,
        "only 2024 transaction should contribute"
    );
    assert_eq!(positions[0].units.number, dec!(1500));
    assert_eq!(positions[0].units.currency.as_str(), "USD");
}

/// Regression test for issue #957: `JOURNAL ... AT units` must strip cost
/// annotations from every position in the balance column.
#[test]
fn test_journal_at_units_strips_cost_from_balance() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets:Brokerage" AT units"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    let balance = match &result.rows[0][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let positions = balance.positions();
    assert_eq!(positions.len(), 1);
    // AT units shows units only — same number / currency as the position.
    assert_eq!(positions[0].units.number, dec!(10));
    assert_eq!(positions[0].units.currency.as_str(), "AAPL");
    assert!(
        positions[0].cost.is_none(),
        "AT units balance must drop the lot annotation; got {:?}",
        positions[0].cost
    );
}

/// Regression test for issue #957 edge case: positions without cost are kept
/// as-is by `Inventory::at_cost()` (matches bean-query's `cost()` fallback).
/// A `JOURNAL ... AT cost` over a USD-only ledger should pass USD through
/// unchanged in the balance, not error or drop the position.
#[test]
fn test_journal_at_cost_balance_preserves_no_cost_positions() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Deposit")
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-100), "USD"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets:Cash" AT cost"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    let balance = match &result.rows[0][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let positions = balance.positions();
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].units.number, dec!(100));
    assert_eq!(positions[0].units.currency.as_str(), "USD");
}

/// Regression test for issue #957 edge case: a balance with positions in
/// multiple cost currencies stays multi-currency under `AT cost` (matches
/// bean-query — `cost(balance)` does not unify across cost currencies).
#[test]
fn test_journal_at_cost_balance_keeps_mixed_cost_currencies() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // Lot 1: 10 AAPL @ 150 USD = 1500 USD cost basis.
        Directive::Transaction(
            Transaction::new(date(2024, 2, 1), "Buy AAPL USD lot")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1500), "USD"),
                )),
        ),
        // Lot 2: 5 AAPL @ 130 EUR = 650 EUR cost basis. (Same commodity,
        // different cost currency — atypical but legal.)
        Directive::Transaction(
            Transaction::new(date(2024, 3, 1), "Buy AAPL EUR lot")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(5), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(130))
                            .with_currency("EUR"),
                    ),
                )
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-650), "EUR"),
                )),
        ),
    ];
    let query = parse(r#"JOURNAL "Assets:Brokerage" AT cost"#).expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    // After both rows, the balance has both USD and EUR cost-currency totals.
    let last_balance = match &result.rows[1][6] {
        Value::Inventory(inv) => inv,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let mut by_currency: std::collections::HashMap<&str, rust_decimal::Decimal> =
        std::collections::HashMap::new();
    for p in last_balance.positions() {
        by_currency.insert(p.units.currency.as_str(), p.units.number);
    }
    assert_eq!(by_currency.get("USD"), Some(&dec!(1500)));
    assert_eq!(by_currency.get("EUR"), Some(&dec!(650)));
    assert_eq!(
        by_currency.len(),
        2,
        "AT cost must not collapse across cost currencies; got {by_currency:?}"
    );
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

/// Regression test for issue #958: sequential `BALANCES` queries on the same
/// `Executor` must produce identical results. Before the fix,
/// `build_balances_with_filter` accumulated into a struct field without
/// clearing, so the second run returned doubled balances.
#[test]
fn test_balances_idempotent_across_sequential_runs() {
    let directives = make_test_directives();
    let query = parse("BALANCES").expect("should parse");
    let mut executor = Executor::new(&directives);

    let r1 = executor.execute(&query).expect("first run");
    let r2 = executor.execute(&query).expect("second run");

    assert_eq!(
        r1.rows, r2.rows,
        "BALANCES must return identical results when run twice on the same Executor"
    );
}

/// Regression test for the Copilot-flagged sub-issue on PR #959: an
/// `Executor` constructed via `new_with_sources` (used when source-location
/// info is needed) put directives in `spanned_directives` and left
/// `directives` empty. `build_balances_with_filter` previously iterated
/// only `self.directives`, so BALANCES on a source-mapped Executor silently
/// returned an empty result. The fix iterates whichever source is
/// populated, mirroring `collect_postings` and the system-table builders.
#[test]
fn test_balances_works_with_spanned_directives_executor() {
    use rustledger_loader::SourceMap;
    use rustledger_parser::{Span, Spanned};

    let dirs = make_test_directives();
    let spanned: Vec<Spanned<rustledger_core::Directive>> = dirs
        .iter()
        .cloned()
        .map(|d| Spanned {
            value: d,
            span: Span::new(0, 50),
            file_id: 0,
        })
        .collect();
    let source_map = SourceMap::new();

    let mut executor = Executor::new_with_sources(&spanned, &source_map);
    let result = executor
        .execute(&parse("BALANCES").expect("should parse"))
        .expect("BALANCES on source-mapped Executor should work");

    assert!(
        !result.is_empty(),
        "source-mapped Executor must return non-empty BALANCES; previously returned empty"
    );
}

/// Regression test for issue #958 (FROM-filter variant): sequential `BALANCES`
/// with different FROM clauses must each return only their own filter's
/// view. Before the fix, the second run accumulated its filter on top of
/// the first run's residual state — a union, not a fresh view — producing
/// output matching no single query.
#[test]
fn test_balances_with_different_from_filters_are_independent() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 6, 1), "2024 deposit")
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-100), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2025, 6, 1), "2025 deposit")
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(500), "USD")))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-500), "USD"),
                )),
        ),
    ];

    let mut executor = Executor::new(&directives);

    // Run year=2024 first to populate any latent state.
    let q_2024 = parse("BALANCES FROM year = 2024").expect("should parse");
    let _ = executor.execute(&q_2024).expect("2024 run");

    // Now run year=2025. Should reflect only 2025 transactions.
    let q_2025 = parse("BALANCES FROM year = 2025").expect("should parse");
    let r_2025 = executor.execute(&q_2025).expect("2025 run");

    // Find the Assets:Cash row.
    let cash_row = r_2025
        .rows
        .iter()
        .find(|row| matches!(&row[0], Value::String(s) if s == "Assets:Cash"))
        .expect("Assets:Cash should appear in 2025 results");

    let inv = match &cash_row[1] {
        Value::Inventory(i) => i,
        other => panic!("expected Inventory, got {other:?}"),
    };
    let positions = inv.positions();
    assert_eq!(positions.len(), 1);
    assert_eq!(
        positions[0].units.number,
        dec!(500),
        "year=2025 BALANCES must show 500 USD, not 600 USD (2024 + 2025 union)"
    );
}

// ----------------------------------------------------------------------------
// `balance` column — cumulative across WHERE-filtered postings (bean-query
// semantics). See issue #929 and the surrounding discussion.
// ----------------------------------------------------------------------------

#[test]
fn test_balance_is_cumulative_across_accounts() {
    // The fixture's first three Asset-touching postings (in iteration order):
    //  txn 1 (2024-01-15 salary): Assets:Bank:Checking +5000
    //  txn 2 (2024-01-20 groceries): Assets:Bank:Checking -150
    //  txn 3 (2024-01-22 gas): Assets:Bank:Checking -45
    // With cumulative semantics each row's `balance` is the running total of
    // all WHERE-matched postings up to and including that row, regardless of
    // account. So the third row (still Checking) should be 5000 - 150 - 45 = 4805.
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT date, balance WHERE account ~ "^Assets" ORDER BY date"#,
        &directives,
    );
    assert!(
        result.len() >= 3,
        "expected at least 3 rows, got {}",
        result.len()
    );
    // Row 3 cumulative: 5000 - 150 - 45 = 4805 USD.
    if let Value::Inventory(inv) = &result.rows[2][1] {
        let positions = inv.positions();
        assert_eq!(
            positions.len(),
            1,
            "expected single-currency total, got {positions:?}"
        );
        assert_eq!(positions[0].units.number, dec!(4805));
        assert_eq!(positions[0].units.currency.as_ref(), "USD");
    } else {
        panic!("expected Inventory, got {:?}", result.rows[2][1]);
    }
}

/// Find the first row whose `account` column equals the given name and
/// return its `balance` column as an Inventory. Avoids depending on the
/// executor's sort being stable for equal date keys (txn 4 has both
/// Savings and Checking on 2024-01-25, so a positional lookup like
/// `result.rows[3]` is flaky).
fn find_balance_by_account<'a>(
    result: &'a QueryResult,
    account: &str,
    balance_col_idx: usize,
) -> &'a Inventory {
    for row in &result.rows {
        if let Value::String(a) = &row[1]
            && a == account
            && let Value::Inventory(inv) = &row[balance_col_idx]
        {
            return inv;
        }
    }
    panic!("no row with account={account} and Inventory balance found")
}

#[test]
fn test_balance_carries_across_different_accounts() {
    // Txn 4 (2024-01-25) adds Assets:Bank:Savings +1000 AND
    // Assets:Bank:Checking -1000. Cumulative after the Savings row should
    // be 4805 + 1000 = 5805 USD — i.e., it carries forward the Checking
    // history from earlier rows. The previous (per-account) implementation
    // would have shown only 1000, since that's all Savings has seen.
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT date, account, balance WHERE account ~ "^Assets" ORDER BY date, account"#,
        &directives,
    );
    let inv = find_balance_by_account(&result, "Assets:Bank:Savings", 2);
    assert_eq!(inv.positions()[0].units.number, dec!(5805));
}

#[test]
fn test_account_balance_is_per_account() {
    // `account_balance` keeps the per-account view we used to expose as
    // `balance`. For the same query, each row should show only that
    // account's cumulative posting amounts — Savings shows 1000, NOT the
    // cumulative 5805.
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT date, account, account_balance WHERE account ~ "^Assets" ORDER BY date, account"#,
        &directives,
    );
    let savings = find_balance_by_account(&result, "Assets:Bank:Savings", 2);
    assert_eq!(savings.positions()[0].units.number, dec!(1000));

    // Pre-Savings, Checking has run 5000 - 150 - 45 = 4805 across the
    // first three Assets postings. Find the gas row (2024-01-22) by
    // account to verify its account_balance (date matching first row
    // would otherwise be ambiguous if multiple Checking rows exist).
    let mut last_checking_balance = None;
    for row in &result.rows {
        if let Value::String(a) = &row[1]
            && a == "Assets:Bank:Checking"
            && let Value::Inventory(inv) = &row[2]
        {
            last_checking_balance = Some(inv.positions()[0].units.number);
        }
    }
    // After all 5 Checking postings (5000, -150, -45, -1000, -80): final = 3725.
    assert_eq!(last_checking_balance, Some(dec!(3725)));
}

#[test]
fn test_where_rejected_postings_do_not_pollute_cumulative_balance() {
    // The fixture has Income/Expenses postings paired with every Assets
    // posting. If the cumulative balance were updated before the WHERE
    // filter, the Income postings (-5000) would cancel the Assets +5000.
    // After the fix, only WHERE-matching postings contribute.
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT date, balance WHERE account ~ "^Assets" ORDER BY date"#,
        &directives,
    );
    // The very first row is the salary posting to Checking: balance = 5000.
    // If cumulative were polluted by Income's -5000, this would be 0.
    if let Value::Inventory(inv) = &result.rows[0][1] {
        assert_eq!(inv.positions()[0].units.number, dec!(5000));
    } else {
        panic!("expected Inventory at first row");
    }
}

#[test]
fn test_close_on_is_exclusive() {
    // `FROM CLOSE ON D` matches bean-query semantics: the books are closed AT D,
    // so a transaction stamped exactly on D is NOT included. See issue #935.
    //
    // Test fixture txns: 2024-01-15, 2024-01-20, 2024-01-22, 2024-01-25, 2024-01-27.
    // With CLOSE ON 2024-01-22, only the 2024-01-15 and 2024-01-20 txns remain
    // (2 postings each = 4 rows). The 2024-01-22 txn must be excluded.
    let directives = make_test_directives();
    let result = execute_query("SELECT date FROM CLOSE ON 2024-01-22", &directives);
    assert_eq!(
        result.len(),
        4,
        "expected 4 rows (txns before 2024-01-22, 2 postings each); got {}",
        result.len()
    );
    let boundary = date(2024, 1, 22);
    for row in &result.rows {
        match &row[0] {
            Value::Date(d) => assert!(
                *d < boundary,
                "row at {d} violates exclusive close: should be < {boundary}"
            ),
            other => panic!("expected Value::Date in column 0, got {other:?}"),
        }
    }
}

#[test]
fn test_close_on_first_txn_date_yields_empty() {
    // Boundary case from issue #935: CLOSE ON the very first transaction date
    // should return zero rows (everything is >= the close date and thus excluded).
    let directives = make_test_directives();
    let result = execute_query("SELECT date FROM CLOSE ON 2024-01-15", &directives);
    assert!(
        result.is_empty(),
        "expected no rows for CLOSE ON the earliest txn date; got {}",
        result.len()
    );
}

#[test]
fn test_execute_balances_with_where() {
    let directives = make_test_directives();
    let query = parse("BALANCES WHERE account ~ 'Assets:'").expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query).expect("should execute");

    // Should only have Assets: accounts (Checking and Savings)
    assert_eq!(result.len(), 2);
    for row in &result.rows {
        if let Value::String(acct) = &row[0] {
            assert!(
                acct.starts_with("Assets:"),
                "Expected Assets: account, got {acct}"
            );
        } else {
            panic!("Expected string account");
        }
    }
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

#[test]
fn test_distinct_coalesce_deduplicates_rows() {
    // The default directives have two transactions with payee "Grocery Store"
    // and one with no payee (narration "Transfer to savings"). DISTINCT should
    // collapse the duplicate payee into a single row.
    let directives = make_test_directives();

    // Without DISTINCT we get one row per transaction (5 total).
    let all_rows = execute_query(
        r"SELECT COALESCE(payee, narration) AS payee FROM transactions ORDER BY payee",
        &directives,
    );

    // With DISTINCT the duplicate "Grocery Store" rows should be collapsed.
    let distinct_rows = execute_query(
        r"SELECT DISTINCT(COALESCE(payee, narration)) AS payee FROM transactions ORDER BY payee",
        &directives,
    );

    // Verify deduplication: distinct result must have fewer rows.
    assert!(
        distinct_rows.len() < all_rows.len(),
        "DISTINCT should produce fewer rows than the full result set ({} vs {})",
        distinct_rows.len(),
        all_rows.len(),
    );

    // Verify no duplicate values remain in the distinct result.
    let values: Vec<&Value> = distinct_rows.rows.iter().map(|row| &row[0]).collect();
    let unique: std::collections::HashSet<String> =
        values.iter().map(|v| format!("{v:?}")).collect();
    assert_eq!(
        values.len(),
        unique.len(),
        "DISTINCT result should contain no duplicate values"
    );
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
// Subquery Tests
// ============================================================================

#[test]
fn test_subquery_basic() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT * FROM (SELECT account, position WHERE account ~ \"Expenses:\")",
        &directives,
    );

    // Should return expenses postings from subquery
    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 2); // account, position
}

#[test]
fn test_subquery_with_aggregation() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT account, total FROM (SELECT account, SUM(position) AS total GROUP BY account)",
        &directives,
    );

    // Should have aggregated results from subquery
    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 2);
}

#[test]
fn test_subquery_with_inner_filter() {
    let directives = make_test_directives();
    // Get expense totals with filtering inside subquery
    let result = execute_query(
        "SELECT * FROM (SELECT account, SUM(position) AS total WHERE account ~ \"Expenses:\" GROUP BY account)",
        &directives,
    );

    assert!(!result.is_empty());
}

// ============================================================================
// HAVING Clause Tests
// ============================================================================

#[test]
fn test_having_basic() {
    let directives = make_test_directives();
    let result = execute_query(
        r"SELECT account, COUNT(*) AS cnt GROUP BY account HAVING cnt >= 2",
        &directives,
    );

    // Should only return accounts with count >= 2
    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::Integer(cnt) = &row[1] {
            assert!(*cnt >= 2, "expected count >= 2, got {cnt}");
        }
    }
}

#[test]
fn test_having_with_count() {
    let directives = make_test_directives();
    let result = execute_query(
        r"SELECT account, COUNT(*) AS cnt GROUP BY account HAVING cnt > 1",
        &directives,
    );

    // Should only return accounts with more than 1 posting
    for row in &result.rows {
        if let Value::Integer(cnt) = &row[1] {
            assert!(*cnt > 1, "expected count > 1, got {cnt}");
        }
    }
}

#[test]
fn test_having_filters_all() {
    let directives = make_test_directives();
    // Very high threshold that no account should meet
    let result = execute_query(
        r"SELECT account, COUNT(*) AS cnt GROUP BY account HAVING cnt > 999999",
        &directives,
    );

    assert!(
        result.is_empty(),
        "expected no results with very high threshold"
    );
}

// ============================================================================
// PIVOT BY Tests
// ============================================================================

#[test]
fn test_parse_pivot_by() {
    let query =
        parse("SELECT account, YEAR(date), SUM(position) GROUP BY 1, 2 PIVOT BY YEAR(date)")
            .expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Select(_)));
}

// ============================================================================
// Window Function Tests
// ============================================================================

#[test]
fn test_parse_window_function_row_number() {
    let query = parse("SELECT account, ROW_NUMBER() OVER (ORDER BY date)").expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Select(_)));
}

#[test]
fn test_parse_window_function_with_partition() {
    let query = parse("SELECT account, ROW_NUMBER() OVER (PARTITION BY account ORDER BY date)")
        .expect("should parse");
    assert!(matches!(query, rustledger_query::Query::Select(_)));
}

#[test]
fn test_execute_window_row_number() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT date, narration, ROW_NUMBER() OVER (ORDER BY date) AS rn",
        &directives,
    );

    assert!(!result.is_empty());

    // Row numbers should be sequential
    let row_nums: Vec<i64> = result
        .rows
        .iter()
        .filter_map(|row| {
            if let Value::Integer(n) = &row[2] {
                Some(*n)
            } else {
                None
            }
        })
        .collect();

    for (i, &rn) in row_nums.iter().enumerate() {
        assert_eq!(
            rn,
            (i + 1) as i64,
            "expected row_number {}, got {rn}",
            i + 1
        );
    }
}

#[test]
fn test_execute_window_rank() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT account, RANK() OVER (ORDER BY account)",
        &directives,
    );

    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 2);
}

#[test]
fn test_execute_window_dense_rank() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT account, DENSE_RANK() OVER (ORDER BY account)",
        &directives,
    );

    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 2);
}

#[test]
fn test_execute_window_with_partition_by() {
    let directives = make_test_directives();
    let result = execute_query(
        r"SELECT account, date, ROW_NUMBER() OVER (PARTITION BY account ORDER BY date) AS rn",
        &directives,
    );

    assert!(!result.is_empty());
    // Each partition should have its own row numbering starting from 1
}

// ============================================================================
// Tags and Links Tests
// ============================================================================

#[test]
fn test_select_tags() {
    let directives = make_test_directives();
    // Transaction 2 has tag "food"
    let result = execute_query(
        r#"SELECT date, narration, tags WHERE "food" IN tags"#,
        &directives,
    );

    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 3);
    // Should find the groceries transaction
    for row in &result.rows {
        if let Value::StringSet(tags) = &row[2] {
            assert!(
                tags.contains(&"food".to_string()),
                "expected 'food' in tags"
            );
        }
    }
}

#[test]
fn test_select_links() {
    // Create directives with a linked transaction
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Linked transaction")
                .with_link("invoice-123")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "USD"))),
        ),
    ];

    let result = execute_query(
        r#"SELECT date, narration, links WHERE "invoice-123" IN links"#,
        &directives,
    );

    assert!(!result.is_empty());
    assert_eq!(result.columns.len(), 3);
    for row in &result.rows {
        if let Value::StringSet(links) = &row[2] {
            assert!(
                links.contains(&"invoice-123".to_string()),
                "expected 'invoice-123' in links"
            );
        }
    }
}

#[test]
fn test_select_payee_and_narration() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT date, payee, narration WHERE payee = "Grocery Store""#,
        &directives,
    );

    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::String(payee) = &row[1] {
            assert_eq!(payee, "Grocery Store");
        }
        // Just verify narration is a non-empty string
        if let Value::String(narration) = &row[2] {
            assert!(!narration.is_empty(), "narration should not be empty");
        }
    }
}

// ============================================================================
// CREATE TABLE and INSERT Tests
// ============================================================================

#[test]
fn test_create_table_simple() {
    let directives = make_test_directives();
    let create_query = parse("CREATE TABLE test_table (col1, col2, col3)").expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&create_query).expect("should execute");

    assert_eq!(result.columns, vec!["result"]);
    assert_eq!(result.rows.len(), 1);
    if let Value::String(msg) = &result.rows[0][0] {
        assert!(msg.contains("Created table"));
    }
}

#[test]
fn test_create_table_as_select() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create a table from a SELECT query (using GROUP BY account which is simpler)
    let create_query =
        parse("CREATE TABLE balances AS SELECT account, sum(number) GROUP BY account")
            .expect("should parse");
    let result = executor.execute(&create_query).expect("should execute");

    assert_eq!(result.columns, vec!["result"]);
    if let Value::String(msg) = &result.rows[0][0] {
        assert!(msg.contains("Created table 'balances'"));
    }

    // Now select from the created table
    let select_query = parse("SELECT * FROM balances").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert!(!result.is_empty());
    assert_eq!(result.columns, vec!["account", "sum"]);
}

#[test]
fn test_insert_values() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create a table
    let create_query = parse("CREATE TABLE accounts (name, balance)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert values
    let insert_query = parse("INSERT INTO accounts VALUES ('Checking', 100), ('Savings', 500)")
        .expect("should parse");
    let result = executor.execute(&insert_query).expect("should execute");

    if let Value::String(msg) = &result.rows[0][0] {
        assert!(msg.contains("Inserted 2 row(s)"));
    }

    // Select from the table
    let select_query = parse("SELECT * FROM accounts").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.rows.len(), 2);
    assert_eq!(result.rows[0][0], Value::String("Checking".to_string()));
    // Whole-number literals parse as Integer (see issue #938).
    assert_eq!(result.rows[0][1], Value::Integer(100));
    assert_eq!(result.rows[1][0], Value::String("Savings".to_string()));
    assert_eq!(result.rows[1][1], Value::Integer(500));
}

#[test]
fn test_insert_select() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create a table from SELECT
    let create_query = parse("CREATE TABLE expenses (account)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert from a SELECT query
    let insert_query =
        parse("INSERT INTO expenses SELECT DISTINCT account WHERE account ~ 'Expenses:'")
            .expect("should parse");
    let result = executor.execute(&insert_query).expect("should execute");

    if let Value::String(msg) = &result.rows[0][0] {
        assert!(msg.contains("Inserted"));
    }

    // Select from the table
    let select_query = parse("SELECT * FROM expenses").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::String(acct) = &row[0] {
            assert!(acct.starts_with("Expenses:"));
        }
    }
}

#[test]
fn test_select_from_table_with_where() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate a table
    let create_query = parse("CREATE TABLE items (name, price)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query = parse("INSERT INTO items VALUES ('Apple', 1), ('Banana', 2), ('Cherry', 5)")
        .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Select with a WHERE clause
    let select_query = parse("SELECT name FROM items WHERE price > 1").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.rows.len(), 2);
    let names: Vec<_> = result.rows.iter().map(|r| &r[0]).collect();
    assert!(names.contains(&&Value::String("Banana".to_string())));
    assert!(names.contains(&&Value::String("Cherry".to_string())));
}

#[test]
fn test_select_from_table_with_order_limit() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate a table
    let create_query = parse("CREATE TABLE nums (value)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query =
        parse("INSERT INTO nums VALUES (3), (1), (4), (1), (5)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Select with ORDER BY and LIMIT
    let select_query =
        parse("SELECT value FROM nums ORDER BY value DESC LIMIT 3").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.rows.len(), 3);
    // Whole-number literals parse as Integer (see issue #938).
    assert_eq!(result.rows[0][0], Value::Integer(5));
    assert_eq!(result.rows[1][0], Value::Integer(4));
    assert_eq!(result.rows[2][0], Value::Integer(3));
}

#[test]
fn test_create_table_duplicate_error() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let create_query = parse("CREATE TABLE mytable (col1)").expect("should parse");
    executor
        .execute(&create_query)
        .expect("should execute first time");

    // Try to create the same table again - should error
    let result = executor.execute(&create_query);
    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.to_string().contains("already exists"));
    }
}

#[test]
fn test_insert_table_not_exists_error() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let insert_query = parse("INSERT INTO nonexistent VALUES (1)").expect("should parse");
    let result = executor.execute(&insert_query);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.to_string().contains("does not exist"));
    }
}

#[test]
fn test_select_table_not_exists_error() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let select_query = parse("SELECT * FROM nonexistent").expect("should parse");
    let result = executor.execute(&select_query);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.to_string().contains("does not exist"));
    }
}

// ============================================================================
// Interval Function Tests
// ============================================================================

#[test]
fn test_interval_basic_construction() {
    use rustledger_query::{Interval, IntervalUnit};

    let directives = make_test_directives();
    let result = execute_query("SELECT interval(1, 'day') LIMIT 1", &directives);

    assert_eq!(result.len(), 1);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(1, IntervalUnit::Day))
    );
}

#[test]
fn test_interval_all_units() {
    use rustledger_query::{Interval, IntervalUnit};

    let directives = make_test_directives();

    // Day
    let result = execute_query("SELECT interval(5, 'day') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(5, IntervalUnit::Day))
    );

    // Week
    let result = execute_query("SELECT interval(2, 'week') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(2, IntervalUnit::Week))
    );

    // Month
    let result = execute_query("SELECT interval(3, 'month') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(3, IntervalUnit::Month))
    );

    // Quarter
    let result = execute_query("SELECT interval(4, 'quarter') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(4, IntervalUnit::Quarter))
    );

    // Year
    let result = execute_query("SELECT interval(1, 'year') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(1, IntervalUnit::Year))
    );
}

#[test]
fn test_interval_negative() {
    use rustledger_query::{Interval, IntervalUnit};

    let directives = make_test_directives();

    let result = execute_query("SELECT interval(-7, 'day') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(-7, IntervalUnit::Day))
    );
}

#[test]
fn test_interval_invalid_unit() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let query = parse("SELECT interval(1, 'invalid_unit')").expect("should parse");
    let result = executor.execute(&query);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.to_string().contains("invalid interval unit"));
    }
}

#[test]
fn test_interval_date_arithmetic() {
    let directives = make_test_directives();

    // Date + interval (days)
    let result = execute_query(
        "SELECT date('2024-01-15') + interval(10, 'day') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 25)));

    // Date + interval (months)
    let result = execute_query(
        "SELECT date('2024-01-15') + interval(2, 'month') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 3, 15)));

    // Date - interval (days)
    let result = execute_query(
        "SELECT date('2024-01-15') - interval(5, 'day') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 10)));

    // Date - interval (months)
    let result = execute_query(
        "SELECT date('2024-03-15') - interval(1, 'month') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 2, 15)));
}

#[test]
fn test_interval_decimal_count_error() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Decimal count should fail - must be an integer
    let query = parse("SELECT interval(3.5, 'day')").expect("should parse");
    let result = executor.execute(&query);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.to_string().contains("must be an integer"));
    }
}

// ============================================================================
// INSERT Column Mapping Tests
// ============================================================================

#[test]
fn test_insert_with_reordered_columns() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table with col1, col2
    let create_query = parse("CREATE TABLE test_reorder (col1, col2)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert with columns in reverse order
    let insert_query = parse("INSERT INTO test_reorder (col2, col1) VALUES ('second', 'first')")
        .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Verify the values are in the correct positions
    let select_query = parse("SELECT col1, col2 FROM test_reorder").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("first".to_string()));
    assert_eq!(result.rows[0][1], Value::String("second".to_string()));
}

#[test]
fn test_insert_with_column_subset() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table with 3 columns
    let create_query = parse("CREATE TABLE test_subset (a, b, c)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert only into column 'b' - others should be NULL
    let insert_query =
        parse("INSERT INTO test_subset (b) VALUES ('middle')").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Verify the values
    let select_query = parse("SELECT a, b, c FROM test_subset").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Null);
    assert_eq!(result.rows[0][1], Value::String("middle".to_string()));
    assert_eq!(result.rows[0][2], Value::Null);
}

#[test]
fn test_insert_invalid_column_error() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table
    let create_query = parse("CREATE TABLE test_invalid (col1, col2)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert with non-existent column
    let insert_query =
        parse("INSERT INTO test_invalid (nonexistent) VALUES ('value')").expect("should parse");
    let result = executor.execute(&insert_query);

    assert!(result.is_err());
    if let Err(e) = result {
        assert!(e.to_string().contains("does not exist"));
    }
}

// ============================================================================
// SELECT FROM Table Aggregation Tests
// ============================================================================

#[test]
fn test_select_from_table_all_rows() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate table
    let create_query = parse("CREATE TABLE numbers (value)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query =
        parse("INSERT INTO numbers VALUES (1), (2), (3), (4), (5)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Select all values and verify row count
    let result = executor
        .execute(&parse("SELECT value FROM numbers").expect("should parse"))
        .expect("should execute");
    assert_eq!(result.len(), 5);
}

#[test]
fn test_select_from_table_filter() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate table
    let create_query = parse("CREATE TABLE prices (category, price)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query = parse(
        "INSERT INTO prices VALUES ('food', 10), ('food', 20), ('transport', 15), ('transport', 25)",
    )
    .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Filter by category
    let result = executor
        .execute(
            &parse("SELECT price FROM prices WHERE category = 'food' ORDER BY price")
                .expect("should parse"),
        )
        .expect("should execute");

    assert_eq!(result.len(), 2);
    assert_eq!(result.rows[0][0], Value::Integer(10));
    assert_eq!(result.rows[1][0], Value::Integer(20));
}

#[test]
fn test_select_from_table_distinct() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate table with duplicates
    let create_query = parse("CREATE TABLE items (name)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query =
        parse("INSERT INTO items VALUES ('apple'), ('banana'), ('apple'), ('cherry'), ('banana')")
            .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // SELECT DISTINCT
    let result = executor
        .execute(&parse("SELECT DISTINCT name FROM items ORDER BY name").expect("should parse"))
        .expect("should execute");

    assert_eq!(result.len(), 3);
    assert_eq!(result.rows[0][0], Value::String("apple".to_string()));
    assert_eq!(result.rows[1][0], Value::String("banana".to_string()));
    assert_eq!(result.rows[2][0], Value::String("cherry".to_string()));
}

// ============================================================================
// Interval Edge Case Tests
// ============================================================================

#[test]
fn test_interval_zero() {
    use rustledger_query::{Interval, IntervalUnit};

    let directives = make_test_directives();

    // Zero interval should work
    let result = execute_query("SELECT interval(0, 'day') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(0, IntervalUnit::Day))
    );

    // Date + zero interval should return same date
    let result = execute_query(
        "SELECT date('2024-01-15') + interval(0, 'day') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15)));

    // Zero months
    let result = execute_query(
        "SELECT date('2024-01-15') + interval(0, 'month') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15)));
}

#[test]
fn test_interval_month_end_arithmetic() {
    let directives = make_test_directives();

    // Jan 31 + 1 month = Feb 29 (2024 is leap year)
    let result = execute_query(
        "SELECT date('2024-01-31') + interval(1, 'month') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 2, 29)));

    // Mar 31 - 1 month = Feb 29 (2024 is leap year)
    let result = execute_query(
        "SELECT date('2024-03-31') - interval(1, 'month') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 2, 29)));

    // Jan 31 + 1 month in non-leap year = Feb 28
    let result = execute_query(
        "SELECT date('2023-01-31') + interval(1, 'month') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2023, 2, 28)));
}

#[test]
fn test_interval_quarter_arithmetic() {
    let directives = make_test_directives();

    // Jan 15 + 1 quarter = Apr 15
    let result = execute_query(
        "SELECT date('2024-01-15') + interval(1, 'quarter') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 4, 15)));

    // Jan 15 + 2 quarters = Jul 15
    let result = execute_query(
        "SELECT date('2024-01-15') + interval(2, 'quarter') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 7, 15)));

    // Oct 15 - 2 quarters = Apr 15
    let result = execute_query(
        "SELECT date('2024-10-15') - interval(2, 'quarter') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 4, 15)));
}

#[test]
fn test_interval_year_arithmetic() {
    let directives = make_test_directives();

    // Regular year arithmetic
    let result = execute_query(
        "SELECT date('2024-06-15') + interval(1, 'year') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2025, 6, 15)));

    // Feb 29 + 1 year = Feb 28 (2025 is not a leap year)
    let result = execute_query(
        "SELECT date('2024-02-29') + interval(1, 'year') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2025, 2, 28)));

    // Year subtraction
    let result = execute_query(
        "SELECT date('2024-06-15') - interval(2, 'year') LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Date(date(2022, 6, 15)));
}

#[test]
fn test_interval_case_insensitive_unit() {
    use rustledger_query::{Interval, IntervalUnit};

    let directives = make_test_directives();

    // Uppercase
    let result = execute_query("SELECT interval(1, 'DAY') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(1, IntervalUnit::Day))
    );

    // Mixed case
    let result = execute_query("SELECT interval(1, 'Month') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(1, IntervalUnit::Month))
    );

    // Short form
    let result = execute_query("SELECT interval(1, 'd') LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::Interval(Interval::new(1, IntervalUnit::Day))
    );
}

// ============================================================================
// INSERT Column Mapping Extended Tests
// ============================================================================

#[test]
fn test_insert_multiple_rows_with_columns() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table
    let create_query = parse("CREATE TABLE multi_insert (col1, col2)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert multiple rows with reordered columns
    let insert_query =
        parse("INSERT INTO multi_insert (col2, col1) VALUES ('a', 'b'), ('c', 'd'), ('e', 'f')")
            .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Verify all rows are correctly mapped
    let select_query =
        parse("SELECT col1, col2 FROM multi_insert ORDER BY col1").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 3);
    assert_eq!(result.rows[0][0], Value::String("b".to_string()));
    assert_eq!(result.rows[0][1], Value::String("a".to_string()));
    assert_eq!(result.rows[1][0], Value::String("d".to_string()));
    assert_eq!(result.rows[1][1], Value::String("c".to_string()));
    assert_eq!(result.rows[2][0], Value::String("f".to_string()));
    assert_eq!(result.rows[2][1], Value::String("e".to_string()));
}

#[test]
fn test_insert_column_case_insensitive() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table with lowercase column names
    let create_query = parse("CREATE TABLE case_test (name, value)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert with uppercase column names
    let insert_query =
        parse("INSERT INTO case_test (NAME, VALUE) VALUES ('test', 123)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Verify insert worked
    let select_query = parse("SELECT name, value FROM case_test").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("test".to_string()));
}

#[test]
fn test_insert_natural_column_order() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table
    let create_query = parse("CREATE TABLE natural_order (a, b, c)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert in natural order (same as table definition)
    let insert_query =
        parse("INSERT INTO natural_order (a, b, c) VALUES ('x', 'y', 'z')").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Verify correct ordering
    let select_query = parse("SELECT a, b, c FROM natural_order").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("x".to_string()));
    assert_eq!(result.rows[0][1], Value::String("y".to_string()));
    assert_eq!(result.rows[0][2], Value::String("z".to_string()));
}

// ============================================================================
// SELECT FROM Table Extended Tests
// ============================================================================

#[test]
fn test_select_from_empty_table() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create empty table
    let create_query = parse("CREATE TABLE empty_table (col)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Select from empty table should return 0 rows
    let select_query = parse("SELECT col FROM empty_table").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 0);
}

#[test]
fn test_select_multi_column() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate table
    let create_query =
        parse("CREATE TABLE products (name, price, category)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query =
        parse("INSERT INTO products VALUES ('Apple', 1.50, 'fruit'), ('Bread', 2.00, 'bakery')")
            .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Select multiple columns
    let select_query =
        parse("SELECT name, price, category FROM products ORDER BY name").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 2);
    assert_eq!(result.columns, vec!["name", "price", "category"]);
    assert_eq!(result.rows[0][0], Value::String("Apple".to_string()));
    assert_eq!(result.rows[0][1], Value::Number(dec!(1.50)));
    assert_eq!(result.rows[0][2], Value::String("fruit".to_string()));
}

#[test]
fn test_select_order_by_desc() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate table
    let create_query = parse("CREATE TABLE scores (name, score)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query = parse("INSERT INTO scores VALUES ('Alice', 85), ('Bob', 92), ('Carol', 78)")
        .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Order by score descending
    let select_query =
        parse("SELECT name, score FROM scores ORDER BY score DESC").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 3);
    assert_eq!(result.rows[0][0], Value::String("Bob".to_string())); // 92
    assert_eq!(result.rows[1][0], Value::String("Alice".to_string())); // 85
    assert_eq!(result.rows[2][0], Value::String("Carol".to_string())); // 78
}

/// Test ORDER BY with GROUP BY expressions that are not in SELECT.
///
/// This test verifies that ORDER BY can reference expressions that appear in
/// GROUP BY but not in SELECT (hidden columns). This is valid SQL semantics
/// and matches Python beancount behavior.
#[test]
fn test_order_by_group_by_expression_not_in_select() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Query with account_sortkey in GROUP BY and ORDER BY but not in SELECT
    // This should work because account_sortkey(account) is a GROUP BY expression
    let query = parse(
        "SELECT account, sum(number) \
         GROUP BY account, account_sortkey(account) \
         ORDER BY account_sortkey(account)",
    )
    .expect("should parse");
    let result = executor.execute(&query).expect("should execute");

    // The result should only have 2 columns (account and sum), not the hidden sortkey column
    assert_eq!(result.columns.len(), 2);
    assert_eq!(result.columns[0], "account");
    assert_eq!(result.columns[1], "sum");

    // Verify all rows have exactly 2 values
    for row in &result.rows {
        assert_eq!(
            row.len(),
            2,
            "Row should have 2 columns, not hidden columns"
        );
    }
}

/// Test ORDER BY with multiple GROUP BY expressions, some not in SELECT.
#[test]
fn test_order_by_multiple_hidden_columns() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Multiple ORDER BY expressions where some are not in SELECT
    let query = parse(
        "SELECT account, sum(number), currency \
         GROUP BY account, currency, account_sortkey(account) \
         ORDER BY account_sortkey(account), currency",
    )
    .expect("should parse");
    let result = executor.execute(&query).expect("should execute");

    // Should have 3 visible columns
    assert_eq!(result.columns.len(), 3);
    assert_eq!(result.columns[0], "account");
    assert_eq!(result.columns[1], "sum");
    assert_eq!(result.columns[2], "currency");

    // Verify all rows have exactly 3 values
    for row in &result.rows {
        assert_eq!(
            row.len(),
            3,
            "Row should have 3 columns, not hidden columns"
        );
    }
}

/// Test ORDER BY with hidden columns in non-aggregate query.
///
/// This tests the edge case where a query has GROUP BY but no aggregate functions.
#[test]
fn test_order_by_hidden_column_non_aggregate() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Query without aggregate functions but with GROUP BY and ORDER BY
    // Note: This is unusual but valid SQL semantics
    let query = parse(
        "SELECT account \
         GROUP BY account, account_sortkey(account) \
         ORDER BY account_sortkey(account)",
    )
    .expect("should parse");
    let result = executor.execute(&query).expect("should execute");

    // Should only have 1 column (account), hidden column should be removed
    assert_eq!(result.columns.len(), 1);
    assert_eq!(result.columns[0], "account");

    // Verify all rows have exactly 1 value
    for row in &result.rows {
        assert_eq!(
            row.len(),
            1,
            "Row should have 1 column, hidden column removed"
        );
    }
}

#[test]
fn test_select_with_limit() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate table
    let create_query = parse("CREATE TABLE many_rows (val)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query =
        parse("INSERT INTO many_rows VALUES (1), (2), (3), (4), (5), (6), (7), (8), (9), (10)")
            .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Select with limit
    let select_query = parse("SELECT val FROM many_rows LIMIT 3").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 3);
}

#[test]
fn test_select_distinct_with_nulls() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table with 3 columns (we'll only populate first column)
    let create_query = parse("CREATE TABLE nulls_test (a, b)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert using column subset - 'b' will be NULL for all rows
    let insert_query =
        parse("INSERT INTO nulls_test (a) VALUES ('x'), ('y'), ('x')").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // DISTINCT on column 'b' should return single NULL
    let select_query = parse("SELECT DISTINCT b FROM nulls_test").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Null);
}

#[test]
fn test_select_where_is_null() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table
    let create_query = parse("CREATE TABLE null_filter (name, value)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert some rows with NULL values (using column subset)
    let insert_query =
        parse("INSERT INTO null_filter (name) VALUES ('has_null')").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    let insert_query2 =
        parse("INSERT INTO null_filter VALUES ('has_value', 42)").expect("should parse");
    executor.execute(&insert_query2).expect("should execute");

    // Filter for NULL values
    let select_query =
        parse("SELECT name FROM null_filter WHERE value IS NULL").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("has_null".to_string()));
}

#[test]
fn test_select_complex_where() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create and populate table
    let create_query =
        parse("CREATE TABLE inventory (item, price, category)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query = parse(
        "INSERT INTO inventory VALUES ('Apple', 1, 'fruit'), ('Steak', 15, 'meat'), ('Banana', 2, 'fruit'), ('Chicken', 8, 'meat')",
    )
    .expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Complex WHERE with AND
    let select_query =
        parse("SELECT item FROM inventory WHERE price > 5 AND category = 'meat' ORDER BY item")
            .expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 2);
    assert_eq!(result.rows[0][0], Value::String("Chicken".to_string()));
    assert_eq!(result.rows[1][0], Value::String("Steak".to_string()));
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_error_unknown_column() {
    let directives = make_test_directives();
    let query = parse("SELECT nonexistent_column").expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query);
    assert!(result.is_err());
}

#[test]
fn test_error_unknown_function() {
    let directives = make_test_directives();
    let query = parse("SELECT NONEXISTENT_FUNC(account)").expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query);
    assert!(result.is_err());
}

#[test]
fn test_error_type_mismatch_comparison() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create table with mixed types
    let create_query = parse("CREATE TABLE types (name, value)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query = parse("INSERT INTO types VALUES ('text', 42)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Try to compare string column with number (should still work - coercion)
    let select_query = parse("SELECT name FROM types WHERE name > 10").expect("should parse");
    // This may or may not error depending on implementation - just verify it doesn't panic
    let _ = executor.execute(&select_query);
}

#[test]
fn test_division_behavior() {
    // Test division using literal expressions - use LIMIT 1 to get single row
    let directives = make_test_directives();
    let result = execute_query("SELECT 10 / 2 LIMIT 1", &directives);
    // Division should work and return single row
    assert_eq!(result.len(), 1);
    // Result should be 5
    if let Value::Integer(val) = &result.rows[0][0] {
        assert_eq!(*val, 5);
    } else if let Value::Number(val) = &result.rows[0][0] {
        assert_eq!(*val, dec!(5));
    }
}

#[test]
fn test_error_invalid_function_args_year() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let create_query = parse("CREATE TABLE func_test (val)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query = parse("INSERT INTO func_test VALUES ('not a date')").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // YEAR expects a date, not a string
    let select_query = parse("SELECT YEAR(val) FROM func_test").expect("should parse");
    let result = executor.execute(&select_query);
    assert!(result.is_err());
}

#[test]
fn test_error_invalid_function_args_length() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let create_query = parse("CREATE TABLE len_test (val)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query = parse("INSERT INTO len_test VALUES (12345)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // LENGTH expects a string, not a number
    let select_query = parse("SELECT LENGTH(val) FROM len_test").expect("should parse");
    let result = executor.execute(&select_query);
    assert!(result.is_err());
}

// ============================================================================
// Aggregate Edge Cases
// ============================================================================

#[test]
fn test_aggregate_sum_on_ledger() {
    // Test SUM on ledger data
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT SUM(number) WHERE account ~ "Expenses:Food""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // We have 150 + 80 = 230 USD in Food expenses
    if let Value::Number(sum) = &result.rows[0][0] {
        assert_eq!(*sum, dec!(230));
    }
}

#[test]
fn test_aggregate_count_on_ledger() {
    // Test COUNT on ledger data
    let directives = make_test_directives();

    // COUNT(*) counts all postings matching filter
    let result = execute_query(r#"SELECT COUNT(*) WHERE account ~ "Expenses""#, &directives);
    if let Value::Integer(count) = &result.rows[0][0] {
        assert_eq!(*count, 3); // 2 Food + 1 Transport
    }
}

#[test]
fn test_aggregate_avg_on_ledger() {
    // Test AVG on ledger data
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT AVG(number) WHERE account ~ "Expenses:Food""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Average of 150 and 80 = 115
    if let Value::Number(avg) = &result.rows[0][0] {
        assert_eq!(*avg, dec!(115));
    }
}

#[test]
fn test_aggregate_min_max_on_ledger() {
    // Test MIN/MAX on ledger data
    let directives = make_test_directives();

    let result = execute_query(
        r#"SELECT MIN(number), MAX(number) WHERE account ~ "Expenses""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Min expense: 45 (Transport), Max expense: 150 (Food)
    if let Value::Number(min) = &result.rows[0][0] {
        assert_eq!(*min, dec!(45));
    }
    if let Value::Number(max) = &result.rows[0][1] {
        assert_eq!(*max, dec!(150));
    }
}

#[test]
fn test_aggregate_filtered() {
    // Test aggregates with specific filter
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT SUM(number), COUNT(*), AVG(number) WHERE account = "Expenses:Food""#,
        &directives,
    );

    // Should have 1 row with aggregate results
    assert_eq!(result.len(), 1);
    // COUNT should be 2 (two Food transactions)
    if let Value::Integer(count) = &result.rows[0][1] {
        assert_eq!(*count, 2);
    }
}

// ============================================================================
// GROUP BY Edge Cases
// ============================================================================

#[test]
fn test_group_by_multiple_columns_ledger() {
    // Test GROUP BY with multiple columns on ledger data
    let directives = make_test_directives();

    // Group by account root (first component) and currency
    let result = execute_query(
        r"SELECT account, currency, SUM(number) AS total GROUP BY account, currency ORDER BY account",
        &directives,
    );

    // Should have multiple groups for different accounts
    assert!(result.len() >= 3);
}

#[test]
fn test_group_by_with_having_ledger() {
    // Test GROUP BY with HAVING on ledger data
    let directives = make_test_directives();

    // Only show accounts with more than 1 posting
    let result = execute_query(
        r"SELECT account, COUNT(*) AS cnt GROUP BY account HAVING cnt > 1 ORDER BY account",
        &directives,
    );

    // Assets:Bank:Checking has multiple postings
    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::Integer(cnt) = &row[1] {
            assert!(*cnt > 1);
        }
    }
}

// ============================================================================
// Window Function Edge Cases
// ============================================================================

#[test]
fn test_window_rank_with_ties() {
    // Test RANK with ties using ledger data (window functions not supported in FROM table)
    let directives = make_test_directives();
    // Use existing ledger postings - we have 5 transactions
    // Group by account to get tie-breaking scenarios
    let result = execute_query(
        r"SELECT account, RANK() OVER (ORDER BY account) AS rnk WHERE account ~ 'Assets' ORDER BY account",
        &directives,
    );

    // We have 4 postings to Assets accounts (Checking gets multiple)
    assert!(result.len() >= 2);
    // First posting should have rank 1
    if let Value::Integer(rank) = &result.rows[0][1] {
        assert_eq!(*rank, 1);
    }
}

#[test]
fn test_window_dense_rank_with_ties() {
    // Test DENSE_RANK using ledger data
    let directives = make_test_directives();
    let result = execute_query(
        r"SELECT account, DENSE_RANK() OVER (ORDER BY account) AS drnk WHERE account ~ 'Expenses' ORDER BY account",
        &directives,
    );

    // We have Expenses:Food and Expenses:Transport
    assert!(result.len() >= 2);
    // All Food postings should have same dense_rank
    if let Value::Integer(rank) = &result.rows[0][1] {
        assert!(*rank >= 1);
    }
}

#[test]
fn test_window_row_number_on_ledger() {
    // Test ROW_NUMBER using ledger data
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT date, narration, ROW_NUMBER() OVER (ORDER BY date) AS rn ORDER BY date LIMIT 5",
        &directives,
    );

    assert!(result.len() >= 3);
    // Row numbers should be sequential
    for (i, row) in result.rows.iter().enumerate() {
        if let Value::Integer(rn) = &row[2] {
            assert_eq!(*rn, (i + 1) as i64, "Row number should be sequential");
        }
    }
}

// ============================================================================
// String Function Tests
// ============================================================================

#[test]
fn test_string_upper_lower_ledger() {
    // Test UPPER/LOWER on ledger narration
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT UPPER(narration), LOWER(narration) WHERE narration = "Monthly salary" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(
        result.rows[0][0],
        Value::String("MONTHLY SALARY".to_string())
    );
    assert_eq!(
        result.rows[0][1],
        Value::String("monthly salary".to_string())
    );
}

#[test]
fn test_string_length_ledger() {
    // Test LENGTH on ledger account names
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account, LENGTH(account) AS len WHERE account ~ "Assets" LIMIT 3"#,
        &directives,
    );

    assert!(!result.is_empty());
    // All lengths should be positive
    for row in &result.rows {
        if let Value::Integer(len) = &row[1] {
            assert!(*len > 0);
        }
    }
}

#[test]
fn test_string_trim_literal() {
    // Test TRIM with literal string
    let directives = make_test_directives();
    let result = execute_query(r#"SELECT TRIM("  hello  ") LIMIT 1"#, &directives);

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("hello".to_string()));
}

// ============================================================================
// Math Function Tests
// ============================================================================

#[test]
fn test_math_abs_ledger() {
    // Test ABS on ledger amounts (negative income postings)
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT number, ABS(number) AS abs_val WHERE account ~ "Income" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Income posting is negative, ABS should be positive
    if let Value::Number(abs_val) = &result.rows[0][1] {
        assert!(*abs_val > dec!(0));
    }
}

#[test]
fn test_math_round_ledger() {
    // Test ROUND on ledger amounts (ROUND takes 1 arg in BQL)
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT number, ROUND(number) AS rounded WHERE account ~ "Expenses:Food" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Should have a result
    assert!(!matches!(result.rows[0][1], Value::Null));
}

// ============================================================================
// COALESCE Function Tests
// ============================================================================

#[test]
fn test_coalesce_with_payee() {
    // Test COALESCE with payee (some transactions have payee, some don't)
    let directives = make_test_directives();
    let result = execute_query(
        r"SELECT COALESCE(payee, narration) AS description LIMIT 5",
        &directives,
    );

    // Should have results
    assert!(!result.is_empty());
    // All should be non-null (either payee or narration)
    for row in &result.rows {
        assert!(!matches!(row[0], Value::Null));
    }
}

#[test]
fn test_coalesce_first_non_null() {
    // Test COALESCE returns first non-null value
    let directives = make_test_directives();
    // Use payee (which may be NULL) with narration fallback
    let result = execute_query(
        r"SELECT payee, narration, COALESCE(payee, narration) AS desc LIMIT 5",
        &directives,
    );

    assert!(!result.is_empty());
    // COALESCE result should never be NULL when narration exists
    for row in &result.rows {
        assert!(!matches!(row[2], Value::Null));
    }
}

// ============================================================================
// Boolean Expression Tests
// ============================================================================

#[test]
fn test_boolean_and_or_not() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let create_query = parse("CREATE TABLE bools (a, b)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query =
        parse("INSERT INTO bools VALUES (1, 0), (1, 1), (0, 0), (0, 1)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // Test AND
    let select_query = parse("SELECT a, b FROM bools WHERE a = 1 AND b = 1").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");
    assert_eq!(result.len(), 1);

    // Test OR
    let select_query2 = parse("SELECT a, b FROM bools WHERE a = 1 OR b = 1").expect("should parse");
    let result2 = executor.execute(&select_query2).expect("should execute");
    assert_eq!(result2.len(), 3);

    // Test NOT
    let select_query3 = parse("SELECT a, b FROM bools WHERE NOT (a = 1)").expect("should parse");
    let result3 = executor.execute(&select_query3).expect("should execute");
    assert_eq!(result3.len(), 2);
}

#[test]
fn test_between_clause() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    let create_query = parse("CREATE TABLE range_test (val)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    let insert_query =
        parse("INSERT INTO range_test VALUES (1), (5), (10), (15), (20)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    let select_query = parse("SELECT val FROM range_test WHERE val BETWEEN 5 AND 15 ORDER BY val")
        .expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    assert_eq!(result.len(), 3);
    if let Value::Integer(v) = &result.rows[0][0] {
        assert_eq!(*v, 5);
    }
    if let Value::Integer(v) = &result.rows[1][0] {
        assert_eq!(*v, 10);
    }
    if let Value::Integer(v) = &result.rows[2][0] {
        assert_eq!(*v, 15);
    }
}

#[test]
fn test_in_clause_with_accounts() {
    // Test IN clause on ledger accounts
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account WHERE account = "Expenses:Food" OR account = "Expenses:Transport""#,
        &directives,
    );

    // Should find Food and Transport expense postings
    assert!(result.len() >= 2);
    for row in &result.rows {
        if let Value::String(acc) = &row[0] {
            assert!(acc.contains("Expenses"));
        }
    }
}

/// Regression test for issue #580: IN operator with tuple/set literal
/// <https://github.com/rustledger/rustledger/issues/580>
#[test]
fn test_issue_580_in_operator_with_set_literal() {
    // Test IN clause with a set literal like ('EUR', 'USD')
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:EUR")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:USD")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:GBP")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "EUR expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR")))
                .with_posting(Posting::new(
                    "Assets:Bank:EUR",
                    Amount::new(dec!(-100), "EUR"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "USD expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new(
                    "Assets:Bank:USD",
                    Amount::new(dec!(-50), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 17), "GBP expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(30), "GBP")))
                .with_posting(Posting::new(
                    "Assets:Bank:GBP",
                    Amount::new(dec!(-30), "GBP"),
                )),
        ),
    ];

    // Filter using IN with set literal - should match EUR and USD only
    let result = execute_query(
        r"SELECT account, currency, number WHERE currency IN ('EUR', 'USD')",
        &directives,
    );

    // Should find 4 postings: 2 EUR (expense + bank) + 2 USD (expense + bank)
    // GBP postings should be excluded
    assert_eq!(result.rows.len(), 4, "Expected 4 postings (2 EUR + 2 USD)");

    for row in &result.rows {
        let currency = match &row[1] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for currency, got {other:?}"),
        };
        assert!(
            currency == "EUR" || currency == "USD",
            "Expected EUR or USD, got {currency}"
        );
    }
}

/// Test NOT IN operator with set literal
#[test]
fn test_not_in_operator_with_set_literal() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "EUR expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "USD expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 17), "GBP expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(30), "GBP")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-30), "GBP"))),
        ),
    ];

    // Filter using NOT IN with set literal - should match only GBP
    let result = execute_query(
        r"SELECT currency, number WHERE currency NOT IN ('EUR', 'USD')",
        &directives,
    );

    // Should find 2 postings: GBP expense + GBP bank
    assert_eq!(result.rows.len(), 2, "Expected 2 GBP postings");

    for row in &result.rows {
        let currency = match &row[0] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for currency, got {other:?}"),
        };
        assert_eq!(currency, "GBP", "Expected only GBP postings");
    }
}

/// Test IN with single element set
#[test]
fn test_in_operator_single_element_set() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "EUR expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "USD expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
    ];

    // Single element set with trailing comma parses as Expr::Set([..])
    let result = execute_query(r"SELECT currency WHERE currency IN ('EUR',)", &directives);

    assert_eq!(result.rows.len(), 2, "Expected 2 EUR postings");
    for row in &result.rows {
        let currency = match &row[0] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for currency, got {other:?}"),
        };
        assert_eq!(currency, "EUR");
    }
}

/// Regression test for issue #916: `IN ('one_value')` (no trailing comma)
/// should match `'one_value'`, behaving like `= 'one_value'`. The parser
/// resolves this to a parenthesized scalar; the executor falls back to
/// scalar equality, matching SQL/Python bean-query semantics.
#[test]
fn test_in_operator_single_element_no_trailing_comma() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "EUR expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "USD expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
    ];

    let result = execute_query(r"SELECT currency WHERE currency IN ('EUR')", &directives);
    assert_eq!(result.rows.len(), 2, "Expected 2 EUR postings");
    for row in &result.rows {
        let currency = match &row[0] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for currency, got {other:?}"),
        };
        assert_eq!(currency, "EUR");
    }

    // NOT IN ('EUR') should select non-EUR rows
    let result = execute_query(
        r"SELECT currency WHERE currency NOT IN ('EUR')",
        &directives,
    );
    assert_eq!(result.rows.len(), 2, "Expected 2 non-EUR postings");
    for row in &result.rows {
        let currency = match &row[0] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for currency, got {other:?}"),
        };
        assert_eq!(currency, "USD");
    }

    // HAVING uses the borrowed `binary_op_on_values` path; exercise the same
    // single-element fallback there so both code paths are covered.
    let result = execute_query(
        r"SELECT currency, sum(number) AS total
          GROUP BY currency
          HAVING currency IN ('EUR')",
        &directives,
    );
    assert_eq!(result.rows.len(), 1, "Expected 1 EUR group");
    let currency = match &result.rows[0][0] {
        Value::String(s) => s.as_str(),
        other => panic!("Expected String for currency, got {other:?}"),
    };
    assert_eq!(currency, "EUR");
}

/// Test IN with parenthesized column (not a set literal).
/// Verifies that `IN (tags)` is parsed as checking membership in the `tags` column,
/// not as a single-element set literal containing the column name.
#[test]
fn test_in_operator_parenthesized_column() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Tagged expense")
                .with_tag("food")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "Untagged expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "EUR"))),
        ),
    ];

    // IN (tags) should work - parentheses around column, not a set literal
    let result = execute_query(r#"SELECT narration WHERE "food" IN (tags)"#, &directives);

    // Should find 2 postings from the tagged transaction
    assert_eq!(result.rows.len(), 2, "Expected 2 postings with 'food' tag");
    for row in &result.rows {
        let narration = match &row[0] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for narration, got {other:?}"),
        };
        assert_eq!(narration, "Tagged expense");
    }
}

/// Test IN operator with numeric set (integers)
/// Regression test: Numeric sets should work, not just string sets.
#[test]
fn test_in_operator_numeric_set() {
    let directives = vec![
        Directive::Open(Open::new(date(2023, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2023, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2023, 6, 15), "2023 expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 20), "2024 expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2025, 9, 10), "2025 expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(30), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-30), "EUR"))),
        ),
    ];

    // Filter by year using IN with numeric set
    let result = execute_query(
        r"SELECT year, account, number WHERE year IN (2023, 2024)",
        &directives,
    );

    // Should find 4 postings: 2 from 2023 + 2 from 2024
    // 2025 postings should be excluded
    assert_eq!(
        result.rows.len(),
        4,
        "Expected 4 postings (2 from 2023 + 2 from 2024)"
    );

    for row in &result.rows {
        let year = match &row[0] {
            Value::Integer(y) => *y,
            other => panic!("Expected Integer for year, got {other:?}"),
        };
        assert!(
            year == 2023 || year == 2024,
            "Expected year 2023 or 2024, got {year}"
        );
    }
}

/// Test NOT IN operator with numeric set
#[test]
fn test_not_in_operator_numeric_set() {
    let directives = vec![
        Directive::Open(Open::new(date(2023, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2023, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2023, 6, 15), "2023 expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 20), "2024 expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2025, 9, 10), "2025 expense")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(30), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-30), "EUR"))),
        ),
    ];

    // Filter by year using NOT IN with numeric set
    let result = execute_query(
        r"SELECT year, account, number WHERE year NOT IN (2023, 2024)",
        &directives,
    );

    // Should find 2 postings: both from 2025
    assert_eq!(result.rows.len(), 2, "Expected 2 postings from 2025");

    for row in &result.rows {
        let year = match &row[0] {
            Value::Integer(y) => *y,
            other => panic!("Expected Integer for year, got {other:?}"),
        };
        assert_eq!(year, 2025, "Expected only 2025 postings");
    }
}

#[test]
fn test_filter_with_not_equal() {
    // Test filtering with !=
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT DISTINCT account WHERE account ~ "Assets" AND account != "Assets:Bank:Savings""#,
        &directives,
    );

    // Should only have Checking, not Savings
    for row in &result.rows {
        if let Value::String(acc) = &row[0] {
            assert!(!acc.contains("Savings"));
        }
    }
}

// ============================================================================
// Nested Aggregate Function Tests (Holdings-style queries)
// ============================================================================

use rustledger_core::{Balance, Price};

fn make_holdings_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        // Price directives
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "AAPL",
            Amount::new(dec!(150), "USD"),
        )),
        Directive::Price(Price::new(
            date(2024, 6, 1),
            "AAPL",
            Amount::new(dec!(180), "USD"),
        )),
        // Buy 10 AAPL at $100
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(100))
                            .with_currency("USD")
                            .with_date(date(2024, 1, 15)),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD"))),
        ),
        // Buy 5 more AAPL at $120
        Directive::Transaction(
            Transaction::new(date(2024, 3, 20), "Buy more AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(5), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(120))
                            .with_currency("USD")
                            .with_date(date(2024, 3, 20)),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-600), "USD"))),
        ),
    ]
}

#[test]
fn test_units_sum_position() {
    // Test units(sum(position)) - nested aggregate with non-aggregate function
    let directives = make_holdings_directives();
    let result = execute_query(
        r"SELECT account, units(sum(position)) as units GROUP BY account",
        &directives,
    );

    // Should have 2 rows: Brokerage and Cash
    assert_eq!(result.len(), 2);
}

#[test]
fn test_cost_sum_position() {
    // Test cost(sum(position)) - book value calculation
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT account, cost(sum(position)) as book_value
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Book value should be 10*100 + 5*120 = 1600 USD
    if let Value::Amount(amt) = &result.rows[0][1] {
        assert_eq!(amt.number, dec!(1600));
        assert_eq!(amt.currency.as_str(), "USD");
    } else {
        panic!("Expected Amount value for book_value");
    }
}

#[test]
fn test_number_cost_sum_position() {
    // Test number(cost(sum(position))) - deeply nested
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT number(cost(sum(position))) as cost_number
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(1600));
    } else {
        panic!("Expected Number value");
    }
}

#[test]
fn test_safediv_with_aggregates() {
    // Test safediv with aggregate expressions - like profit percentage calculation
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT safediv(number(cost(sum(position))), 100) as cost_pct
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(16)); // 1600 / 100 = 16
    } else {
        panic!("Expected Number value");
    }
}

#[test]
fn test_parenthesized_aggregate_expression() {
    // Test that parentheses work correctly with aggregate expressions
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT (cost(sum(position))) as book_value
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Amount(amt) = &result.rows[0][0] {
        assert_eq!(amt.number, dec!(1600));
    } else {
        panic!("Expected Amount value");
    }
}

#[test]
fn test_complex_arithmetic_with_aggregates() {
    // Test complex arithmetic expressions with aggregates
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT (number(cost(sum(position))) - 1000) * 2 as calc
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        // (1600 - 1000) * 2 = 1200
        assert_eq!(*n, dec!(1200));
    } else {
        panic!("Expected Number value");
    }
}

#[test]
fn test_multiple_nested_aggregates_in_select() {
    // Test multiple columns with nested aggregates
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT
             account,
             units(sum(position)) as units,
             cost(sum(position)) as book_value,
             number(cost(sum(position))) as cost_num
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Verify cost_num column
    if let Value::Number(n) = &result.rows[0][3] {
        assert_eq!(*n, dec!(1600));
    } else {
        panic!("Expected Number value for cost_num");
    }
}

// ============================================================================
// Unit tests for evaluate_function_on_values code path
// These test non-aggregate functions wrapping aggregate expressions
// ============================================================================

#[test]
fn test_currency_on_aggregate() {
    // Test currency(cost(sum(position))) - currency extraction from aggregate result
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT currency(cost(sum(position))) as cost_curr
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert_eq!(s, "USD");
    } else {
        panic!("Expected String value for currency");
    }
}

#[test]
fn test_deeply_nested_aggregate_functions() {
    // Test abs(number(cost(sum(position)))) - 3 levels of nesting
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT abs(number(cost(sum(position)))) as abs_cost
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(1600));
    } else {
        panic!("Expected Number value");
    }
}

#[test]
fn test_safediv_with_two_aggregate_args() {
    // Test safediv with two aggregate arguments: safediv(sum(...), count(...))
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT safediv(number(cost(sum(position))), count(1)) as avg_cost
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        // 1600 / 2 postings = 800
        assert_eq!(*n, dec!(800));
    } else {
        panic!("Expected Number value");
    }
}

#[test]
fn test_null_propagation_in_nested_aggregates() {
    // Test that cost() returns units when no cost basis (Python beancount compat)
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT number(cost(sum(position))) as cost_num
           WHERE account ~ "Cash"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Cash positions have no cost basis, so cost() returns units: -1000 + -600 = -1600
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(-1600));
    } else {
        panic!("Expected Number value, got {:?}", &result.rows[0][0]);
    }
}

#[test]
fn test_number_cost_position_without_cost() {
    // Regression test for issue #819: number(cost(position)) should work for
    // positions without an explicit cost basis, returning the units number.
    let directives = vec![
        Directive::Open(Open::new(date(2020, 1, 1), "Assets:Checking")),
        Directive::Open(Open::new(date(2020, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2020, 1, 2), "Grocery")
                .with_posting(Posting::new(
                    "Assets:Checking",
                    Amount::new(dec!(-10), "USD"),
                ))
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD"))),
        ),
    ];
    let result = execute_query("SELECT number(cost(position))", &directives);
    assert_eq!(result.len(), 2);
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(-10));
    } else {
        panic!("Expected Number, got {:?}", &result.rows[0][0]);
    }
    if let Value::Number(n) = &result.rows[1][0] {
        assert_eq!(*n, dec!(10));
    } else {
        panic!("Expected Number, got {:?}", &result.rows[1][0]);
    }
}

#[test]
fn test_cost_mixed_inventory_with_and_without_cost() {
    // Regression test: cost() on an inventory with mixed positions
    // (some with cost, some without) should sum cost for positions with cost
    // and units for positions without cost.
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(100))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD"))),
        ),
    ];
    // cost(sum(position)) for Cash: no cost basis, returns units = -1000 USD
    let result = execute_query(
        r#"SELECT number(cost(sum(position))) as cost_num
           WHERE account = "Assets:Cash"
           GROUP BY account"#,
        &directives,
    );
    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(-1000));
    } else {
        panic!("Expected Number, got {:?}", &result.rows[0][0]);
    }
}

#[test]
fn test_unary_negation_on_aggregate() {
    // Test -number(cost(sum(position))) - unary operator on aggregate
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT -number(cost(sum(position))) as neg_cost
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(-1600));
    } else {
        panic!("Expected Number value");
    }
}

#[test]
fn test_number_on_single_currency_inventory() {
    // When inventory has one currency, NUMBER should return the total
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT currency, number(units(sum(position))) as units_num
           WHERE account ~ "Brokerage"
           GROUP BY currency"#,
        &directives,
    );

    // Should have 1 row for AAPL
    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][1] {
        assert_eq!(*n, dec!(15)); // 10 + 5 AAPL
    } else {
        panic!("Expected Number value");
    }
}

fn make_multi_currency_holdings() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        // Buy 10 AAPL
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy AAPL")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(100))
                            .with_currency("USD")
                            .with_date(date(2024, 1, 15)),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD"))),
        ),
        // Buy 5 GOOG (different currency/stock)
        Directive::Transaction(
            Transaction::new(date(2024, 2, 10), "Buy GOOG")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(5), "GOOG")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD")
                            .with_date(date(2024, 2, 10)),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-750), "USD"))),
        ),
    ]
}

#[test]
fn test_number_returns_null_for_mixed_currency_inventory() {
    // When an inventory contains multiple currencies (AAPL + GOOG),
    // NUMBER should return NULL rather than a meaningless sum
    let directives = make_multi_currency_holdings();
    let result = execute_query(
        r#"SELECT number(units(sum(position))) as units_num
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Should be NULL because inventory has AAPL and GOOG
    assert!(
        matches!(&result.rows[0][0], Value::Null),
        "Expected Null for multi-currency inventory, got {:?}",
        result.rows[0][0]
    );
}

// ============================================================================
// Additional coverage tests for evaluate_function_on_values
// ============================================================================

#[test]
fn test_safediv_division_by_zero() {
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT safediv(number(cost(sum(position))), 0) as div_zero
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert!(matches!(&result.rows[0][0], Value::Null));
}

#[test]
fn test_safediv_with_null() {
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT safediv(number(cost(sum(position))), number(cost(sum(position)))) as ratio
           WHERE account ~ "Cash"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Cash has no cost basis, cost() returns units (-1600), safediv(-1600, -1600) = 1
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(1));
    } else {
        panic!("Expected Number value, got {:?}", &result.rows[0][0]);
    }
}

#[test]
fn test_value_function_with_conversion() {
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT number(value(sum(position), "USD")) as market_value
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // 15 AAPL * 180 USD = 2700 USD
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(2700));
    } else {
        panic!("Expected Number value for market value");
    }
}

#[test]
fn test_empty_function() {
    let directives = make_test_directives();
    let result = execute_query(
        r"SELECT empty(sum(position)) as is_empty GROUP BY account LIMIT 1",
        &directives,
    );

    assert!(!result.is_empty());
    // Most accounts have postings, so should be false
    assert!(matches!(&result.rows[0][0], Value::Boolean(_)));
}

#[test]
fn test_only_function_with_inventory() {
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT only(currency, sum(position)) as only_amt
           WHERE account ~ "Brokerage"
           GROUP BY currency"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Amount(a) = &result.rows[0][0] {
        assert_eq!(a.number, dec!(15)); // 10 + 5 AAPL
    } else {
        panic!("Expected Amount value");
    }
}

#[test]
fn test_filter_currency_function() {
    let directives = make_multi_currency_holdings();
    let result = execute_query(
        r#"SELECT number(units(filter_currency(sum(position), "AAPL"))) as aapl_units
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(10)); // Only 10 AAPL, not GOOG
    } else {
        panic!("Expected Number value");
    }
}

#[test]
fn test_currency_on_inventory() {
    let directives = make_holdings_directives();
    let result = execute_query(
        r#"SELECT currency(units(sum(position))) as curr
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert_eq!(s, "AAPL");
    } else {
        panic!("Expected String value for currency");
    }
}

#[test]
fn test_number_on_empty_inventory() {
    let directives = make_test_directives();
    // Query an account with no postings to get empty inventory
    let result = execute_query(
        r#"SELECT number(sum(position)) as num
           WHERE account = "NonExistent:Account"
           GROUP BY account"#,
        &directives,
    );

    // No results since account doesn't exist
    assert!(result.is_empty());
}

// ============================================================================
// String Functions Tests (Coverage improvement)
// ============================================================================

#[test]
fn test_string_startswith() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account WHERE STARTSWITH(account, "Assets")"#,
        &directives,
    );

    // Should have all Asset account postings
    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::String(s) = &row[0] {
            assert!(s.starts_with("Assets"));
        }
    }
}

#[test]
fn test_string_endswith() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT account WHERE ENDSWITH(account, "Checking")"#,
        &directives,
    );

    // Should have all Checking account postings
    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::String(s) = &row[0] {
            assert!(s.ends_with("Checking"));
        }
    }
}

#[test]
fn test_string_grep_match() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT GREP("Bank", account) WHERE account ~ "Bank" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert_eq!(s, "Bank");
    }
}

#[test]
fn test_string_grep_no_match() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT GREP("XYZ", account) WHERE account ~ "Bank" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert!(matches!(&result.rows[0][0], Value::Null));
}

#[test]
fn test_string_grepn_capture_group() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT GREPN("Assets:([^:]+)", account, 1) WHERE account ~ "Assets" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Should capture the first component after Assets:
    if let Value::String(s) = &result.rows[0][0] {
        assert_eq!(s, "Bank");
    }
}

#[test]
fn test_string_subst() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT SUBST("Bank", "Institution", account) WHERE account ~ "Bank" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert!(s.contains("Institution"));
        assert!(!s.contains("Bank"));
    }
}

#[test]
fn test_string_splitcomp() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT SPLITCOMP(account, ":", 1) WHERE account ~ "Assets:Bank" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert_eq!(s, "Bank");
    }
}

#[test]
fn test_string_splitcomp_out_of_bounds() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT SPLITCOMP(account, ":", 100) WHERE account ~ "Assets" LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert!(matches!(&result.rows[0][0], Value::Null));
}

#[test]
fn test_string_joinstr() {
    let directives = make_test_directives();
    let result = execute_query(r#"SELECT JOINSTR("A", "B", "C") LIMIT 1"#, &directives);

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert_eq!(s, "A, B, C");
    }
}

#[test]
fn test_string_maxwidth_truncate() {
    let directives = make_test_directives();
    let result = execute_query(r"SELECT MAXWIDTH(narration, 10) LIMIT 1", &directives);

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert!(s.len() <= 10);
        if s.len() == 10 {
            assert!(s.ends_with("..."));
        }
    }
}

#[test]
fn test_string_maxwidth_no_truncate() {
    let directives = make_test_directives();
    let result = execute_query(r#"SELECT MAXWIDTH("short", 100) LIMIT 1"#, &directives);

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        assert_eq!(s, "short");
    }
}

#[test]
fn test_string_length_on_set() {
    let directives = make_test_directives();
    // LENGTH on tags set should return count
    let result = execute_query(
        r"SELECT LENGTH(tags) WHERE LENGTH(tags) > 0 LIMIT 1",
        &directives,
    );

    // At least some transactions have tags
    if !result.is_empty()
        && let Value::Integer(n) = &result.rows[0][0]
    {
        assert!(*n > 0);
    }
}

// ============================================================================
// Aggregation Functions Tests (Coverage improvement)
// ============================================================================

#[test]
fn test_aggregation_avg() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT AVG(number) as avg_amount WHERE account ~ "Expenses:Food""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        // Average of Food expenses (150 + 80) / 2 = 115
        assert_eq!(*n, dec!(115));
    } else {
        panic!("Expected Number value for AVG");
    }
}

#[test]
fn test_aggregation_min_number() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT MIN(number) as min_amount WHERE account ~ "Expenses" AND number > 0"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        // Minimum expense should be 45 (Transport)
        assert_eq!(*n, dec!(45));
    } else {
        panic!("Expected Number value for MIN");
    }
}

#[test]
fn test_aggregation_max_number() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT MAX(number) as max_amount WHERE account ~ "Expenses" AND number > 0"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        // Maximum expense should be 150 (Food groceries)
        assert_eq!(*n, dec!(150));
    } else {
        panic!("Expected Number value for MAX");
    }
}

#[test]
fn test_aggregation_min_date() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT MIN(date) as earliest_date WHERE account ~ "Expenses""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Date(d) = &result.rows[0][0] {
        assert_eq!(*d, date(2024, 1, 20)); // First expense transaction
    } else {
        panic!("Expected Date value for MIN(date)");
    }
}

#[test]
fn test_aggregation_max_date() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT MAX(date) as latest_date WHERE account ~ "Expenses""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Date(d) = &result.rows[0][0] {
        assert_eq!(*d, date(2024, 1, 27)); // Last expense transaction
    } else {
        panic!("Expected Date value for MAX(date)");
    }
}

#[test]
fn test_aggregation_first() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT FIRST(narration) as first_narration WHERE account ~ "Expenses""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        // First chronologically should be "Weekly groceries"
        assert_eq!(s, "Weekly groceries");
    } else {
        panic!("Expected String value for FIRST");
    }
}

#[test]
fn test_aggregation_last() {
    let directives = make_test_directives();
    let result = execute_query(
        r#"SELECT LAST(narration) as last_narration WHERE account ~ "Expenses""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::String(s) = &result.rows[0][0] {
        // Last chronologically should be "More groceries"
        assert_eq!(s, "More groceries");
    } else {
        panic!("Expected String value for LAST");
    }
}

#[test]
fn test_aggregation_group_key_types() {
    // Test that various value types work as GROUP BY keys
    let directives = make_test_directives();

    // Group by string
    let result = execute_query(r"SELECT account, COUNT(*) GROUP BY account", &directives);
    assert!(!result.is_empty());

    // Group by date
    let result = execute_query(r"SELECT date, COUNT(*) GROUP BY date", &directives);
    assert!(!result.is_empty());
}

#[test]
fn test_aggregation_having_with_alias() {
    let directives = make_test_directives();
    let result = execute_query(
        r"SELECT account, COUNT(*) as cnt
           GROUP BY account
           HAVING cnt > 1",
        &directives,
    );

    // Only accounts with more than 1 posting
    for row in &result.rows {
        if let Value::Integer(n) = &row[1] {
            assert!(*n > 1);
        }
    }
}

#[test]
fn test_aggregation_nested_function() {
    let directives = make_test_directives();
    // Test nested aggregate: units(sum(position))
    let result = execute_query(
        r#"SELECT units(sum(position)) as total_units
           WHERE account ~ "Expenses:Food"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Amount(a) = &result.rows[0][0] {
        // 150 + 80 = 230 USD in food expenses
        assert_eq!(a.number, dec!(230));
    }
}

#[test]
fn test_aggregation_sum_integers() {
    let directives = make_test_directives();
    // COUNT returns integers, can we sum them?
    let result = execute_query(
        r#"SELECT SUM(1) as total_count WHERE account ~ "Expenses""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        // Should be the count of expense postings (3 total)
        assert_eq!(*n, dec!(3));
    }
}

// ============================================================================
// Parallel Execution Tests
// ============================================================================

/// Generate a large number of postings to test parallel query execution path.
/// The parallel threshold is 1000 postings, so we need at least 1001.
fn make_large_directives() -> Vec<Directive> {
    let mut directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Test")),
    ];

    // Generate 510 transactions with 2 postings each = 1020 postings
    // This exceeds PARALLEL_THRESHOLD (1000) to trigger parallel execution
    for i in 0u32..510 {
        let day = (i % 28) + 1; // Day 1-28
        let txn = Transaction::new(date(2024, 1, day), format!("Transaction {i}"))
            .with_posting(Posting::new(
                "Expenses:Test",
                Amount::new(dec!(10) + rust_decimal::Decimal::from(i64::from(i)), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Bank",
                Amount::new(dec!(-10) - rust_decimal::Decimal::from(i64::from(i)), "USD"),
            ));
        directives.push(Directive::Transaction(txn));
    }

    directives
}

#[test]
fn test_parallel_execution_simple_select() {
    // Test that parallel execution produces correct results
    let directives = make_large_directives();
    let result = execute_query(r"SELECT account, number", &directives);

    // Should have 1020 postings (510 transactions × 2 postings each)
    assert_eq!(
        result.len(),
        1020,
        "expected 1020 postings for parallel path"
    );
}

#[test]
fn test_parallel_execution_with_filter() {
    let directives = make_large_directives();
    let result = execute_query(
        r#"SELECT account, number WHERE account ~ "Expenses""#,
        &directives,
    );

    // Should have 510 expense postings
    assert_eq!(result.len(), 510, "expected 510 expense postings");
}

#[test]
fn test_parallel_execution_with_distinct() {
    let directives = make_large_directives();
    let result = execute_query(r"SELECT DISTINCT account", &directives);

    // Should have 2 distinct accounts: Assets:Bank and Expenses:Test
    assert_eq!(result.len(), 2, "expected 2 distinct accounts");
}

#[test]
fn test_parallel_execution_aggregation() {
    let directives = make_large_directives();
    let result = execute_query(r"SELECT account, SUM(number) GROUP BY account", &directives);

    // Should have 2 groups (one per account)
    assert_eq!(result.len(), 2, "expected 2 account groups");
}

#[test]
fn test_parallel_execution_matches_sequential() {
    // Verify parallel and sequential produce the same results
    // We can't directly compare because the threshold is compile-time,
    // but we can verify the results are mathematically correct
    let directives = make_large_directives();

    // Sum of 10+0 + 10+1 + 10+2 + ... + 10+509 for expenses
    // = 510*10 + sum(0..509) = 5100 + (509*510/2) = 5100 + 129795 = 134895
    let result = execute_query(
        r#"SELECT SUM(number) WHERE account ~ "Expenses""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // SUM(number) returns a Number (Decimal), not an Amount
    match &result.rows[0][0] {
        Value::Number(n) => {
            assert_eq!(*n, dec!(134895), "parallel SUM should equal expected total");
        }
        Value::Amount(a) => {
            assert_eq!(
                a.number,
                dec!(134895),
                "parallel SUM should equal expected total"
            );
        }
        other => panic!("expected Number or Amount result, got {other:?}"),
    }
}

// Regression test for issue #532: BQL regex should be case-insensitive
// https://github.com/rustledger/rustledger/issues/532
#[test]
fn test_regex_case_insensitive() {
    let directives = make_test_directives();

    // Test lowercase pattern matches uppercase account component
    let result = execute_query(
        r#"SELECT DISTINCT account WHERE account ~ "food""#,
        &directives,
    );
    assert_eq!(
        result.len(),
        1,
        "lowercase 'food' should match 'Expenses:Food'"
    );

    // Test uppercase pattern matches mixed-case account
    let result = execute_query(
        r#"SELECT DISTINCT account WHERE account ~ "EXPENSES""#,
        &directives,
    );
    // Should match Expenses:Food and Expenses:Transport
    assert_eq!(
        result.len(),
        2,
        "uppercase 'EXPENSES' should match 'Expenses:*' accounts"
    );

    // Test mixed-case pattern
    let result = execute_query(
        r#"SELECT DISTINCT account WHERE account ~ "eXpEnSeS""#,
        &directives,
    );
    assert_eq!(
        result.len(),
        2,
        "mixed-case pattern should match case-insensitively"
    );
}

// ============================================================================
// VALUE() function beancount compatibility tests (issue #568)
// ============================================================================

#[test]
fn test_value_infers_currency_from_cost() {
    // Regression test for issue #568 (Problem 1):
    // VALUE(position) without explicit currency should infer from cost basis.
    // Python beancount uses position.cost.currency as the target currency.
    let directives = make_holdings_directives();

    // Test on individual positions (not aggregated) to verify currency inference
    let result = execute_query(
        r#"SELECT number(value(position)) as market_value
           WHERE account ~ "Brokerage"
           LIMIT 1"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Position has cost in USD, so currency should be inferred
    // Latest price is 180 USD per AAPL
    // Either 10 * 180 = 1800 or 5 * 180 = 900 depending on which comes first
    if let Value::Number(n) = &result.rows[0][0] {
        // Either the 10 AAPL position (1800) or 5 AAPL position (900) is valid
        assert!(
            *n == dec!(1800) || *n == dec!(900),
            "Expected 1800 or 900, got {n}"
        );
    } else {
        panic!("Expected Number value for market value");
    }
}

#[test]
fn test_value_uses_latest_price_not_transaction_date() {
    // Regression test for issue #568 (Problem 2):
    // VALUE() should use the latest available price, not the transaction date price.
    // Python beancount's value() passes None as the date parameter to convert.get_value(),
    // which means "use the most recent price".
    let directives = make_holdings_directives();

    // Prices in make_holdings_directives:
    // 2024-01-01: AAPL = 150 USD
    // 2024-06-01: AAPL = 180 USD (latest)
    //
    // Transactions:
    // 2024-01-15: Buy 10 AAPL (at this date, price was 150)
    // 2024-03-20: Buy 5 AAPL (at this date, price was still 150)
    //
    // If using transaction date: 10*150 + 5*150 = 2250 USD
    // If using latest price: 15*180 = 2700 USD (correct beancount behavior)

    let result = execute_query(
        r#"SELECT number(value(sum(position), "USD")) as market_value
           WHERE account ~ "Brokerage"
           GROUP BY account"#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Number(n) = &result.rows[0][0] {
        // Should be 2700 (latest price), not 2250 (transaction date prices)
        assert_eq!(
            *n,
            dec!(2700),
            "VALUE() should use latest price, not transaction date"
        );
    } else {
        panic!("Expected Number value for market value");
    }
}

#[test]
fn test_value_individual_positions_use_latest_price() {
    // Regression test for issue #568 (Problem 2):
    // Verify that VALUE() on individual postings (not aggregated) also uses latest price.
    let directives = make_holdings_directives();

    let result = execute_query(
        r#"SELECT date, number(value(position, "USD")) as val
           WHERE account ~ "Brokerage"
           ORDER BY date"#,
        &directives,
    );

    assert_eq!(result.len(), 2);

    // First posting: 10 AAPL on 2024-01-15
    // Latest price (2024-06-01) is 180 USD, so value = 10 * 180 = 1800
    if let Value::Number(n) = &result.rows[0][1] {
        assert_eq!(
            *n,
            dec!(1800),
            "First position should use latest price (180), not price at transaction date (150)"
        );
    } else {
        panic!("Expected Number value for first position market value");
    }

    // Second posting: 5 AAPL on 2024-03-20
    // Latest price is 180 USD, so value = 5 * 180 = 900
    if let Value::Number(n) = &result.rows[1][1] {
        assert_eq!(
            *n,
            dec!(900),
            "Second position should use latest price (180)"
        );
    } else {
        panic!("Expected Number value for second position market value");
    }
}

#[test]
fn test_value_chained_price_conversion() {
    // Related to issue #568: VALUE() should support chained price conversion.
    // If STOCK is priced in EUR and EUR is priced in USD, VALUE(position, "USD")
    // should convert via the chain: STOCK → EUR → USD.
    let directives = make_chained_price_directives();
    let result = execute_query(
        r#"SELECT number(value(position, "USD")) as val
           WHERE account ~ "Stocks""#,
        &directives,
    );

    assert_eq!(result.len(), 1);

    // Chained conversion: 5 GOOG × 120 EUR × 1.10 USD/EUR = 660 USD
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(
            *n,
            dec!(660),
            "VALUE() should support chained price conversion (GOOG→EUR→USD)"
        );
    } else {
        panic!("Expected Number value for chained conversion");
    }
}

fn make_chained_price_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stocks")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        // GOOG priced in EUR
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "GOOG",
            Amount::new(dec!(100), "EUR"),
        )),
        Directive::Price(Price::new(
            date(2024, 6, 1),
            "GOOG",
            Amount::new(dec!(120), "EUR"),
        )),
        // EUR priced in USD (exchange rate for chained lookup)
        Directive::Price(Price::new(
            date(2024, 6, 1),
            "EUR",
            Amount::new(dec!(1.10), "USD"),
        )),
        // Buy 5 GOOG at 80 EUR cost
        Directive::Transaction(
            Transaction::new(date(2024, 2, 15), "Buy GOOG")
                .with_posting(
                    Posting::new("Assets:Stocks", Amount::new(dec!(5), "GOOG")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(80))
                            .with_currency("EUR")
                            .with_date(date(2024, 2, 15)),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-400), "EUR"))),
        ),
    ]
}

// ============================================================================
// VALUE() returns as-is when no target currency (Issue #641)
// ============================================================================

#[test]
fn test_value_no_currency_returns_as_is() {
    // Regression test for issue #641:
    // VALUE() with no explicit currency and no cost basis should return the
    // value as-is (the units themselves), matching Python beancount behavior.
    // Previously this errored with "no target currency set".

    // Create directives with positions that have NO cost basis
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Grocery store")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-50), "USD"))),
        ),
    ];

    // VALUE(position) on a position without cost basis and no explicit currency
    // should return the units as-is instead of erroring
    let result = execute_query(
        r#"SELECT account, value(position) as val
           WHERE account = "Expenses:Food""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::Amount(a) = &result.rows[0][1] {
        assert_eq!(a.number, dec!(50));
        assert_eq!(a.currency, "USD");
    } else {
        panic!(
            "Expected Amount value when VALUE() has no target currency, got {:?}",
            result.rows[0][1]
        );
    }
}

#[test]
fn test_value_no_currency_aggregated_returns_as_is() {
    // Regression test for issue #641:
    // VALUE(SUM(position)) with no explicit currency and no cost basis should
    // return the inventory as-is, matching Python beancount behavior.

    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Grocery store")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-50), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 2, 10), "Restaurant")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(30), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-30), "USD"))),
        ),
    ];

    // VALUE(SUM(position)) with no currency should not error
    let result = execute_query(
        r#"SELECT account, value(sum(position)) as val
           GROUP BY account
           HAVING account = "Expenses:Food""#,
        &directives,
    );

    assert_eq!(result.len(), 1);
    // The result should be an inventory returned as-is (not converted)
    // or an amount if the inventory collapses to a single currency.
    // Either way, the value must be 80 USD (50 + 30).
    let expected = Amount::new(dec!(80), "USD");
    match &result.rows[0][1] {
        Value::Amount(a) => {
            assert_eq!(*a, expected, "Expected 80 USD amount");
        }
        Value::Inventory(inv) => {
            let positions = inv.positions();
            assert_eq!(positions.len(), 1, "Expected single-currency inventory");
            assert_eq!(positions[0].units, expected, "Expected 80 USD in inventory");
        }
        other => panic!(
            "Expected Inventory or Amount when VALUE() has no target currency, got {other:?}",
        ),
    }
}

// ============================================================================
// VALUE(position, DATE) Python-beancount compat tests (issue #892)
// ============================================================================

/// Mirrors the fixture used to empirically validate Python bean-query behavior:
/// one position of 4 SP purchased at 250 USD cost, with four price points
/// spanning before and after the relevant dates (including a far-future price).
fn make_issue_892_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2020, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2020, 1, 1), "Equity:Opening")),
        Directive::Price(Price::new(
            date(2020, 1, 1),
            "SP",
            Amount::new(dec!(250), "USD"),
        )),
        Directive::Price(Price::new(
            date(2020, 6, 1),
            "SP",
            Amount::new(dec!(300), "USD"),
        )),
        Directive::Price(Price::new(
            date(2021, 1, 1),
            "SP",
            Amount::new(dec!(500), "USD"),
        )),
        // Far-future price to prove that `value(pos)` with no date argument
        // uses the latest price (which matches Python's date=None behavior)
        // rather than today's date.
        Directive::Price(Price::new(
            date(2099, 1, 1),
            "SP",
            Amount::new(dec!(9999), "USD"),
        )),
        Directive::Transaction(
            Transaction::new(date(2020, 1, 1), "Buy stock").with_posting(
                Posting::new("Assets:Brokerage", Amount::new(dec!(4), "SP")).with_cost(
                    CostSpec::empty()
                        .with_number_per(dec!(250))
                        .with_currency("USD")
                        .with_date(date(2020, 1, 1)),
                ),
            ),
        ),
    ]
}

#[test]
fn test_value_date_arg_returns_price_at_or_before() {
    // value(position, 2020-06-01) should use the price on-or-before 2020-06-01.
    // The fixture has a 300 USD price dated 2020-06-01, so 4 SP * 300 = 1200 USD.
    let directives = make_issue_892_directives();
    let result = execute_query(
        r"SELECT number(value(position, 2020-06-01)) AS v
          WHERE account ~ 'Brokerage'",
        &directives,
    );
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Number(dec!(1200)));
}

#[test]
fn test_value_date_arg_uses_earlier_price_when_no_match_on_date() {
    // value(position, 2020-02-15): no price directive on that exact date,
    // so use the most recent price before it — the 250 USD price from 2020-01-01.
    // 4 SP * 250 = 1000 USD (this matches the result the issue reporter got from
    // Python bean-query with their own simpler fixture).
    let directives = make_issue_892_directives();
    let result = execute_query(
        r"SELECT number(value(position, 2020-02-15)) AS v
          WHERE account ~ 'Brokerage'",
        &directives,
    );
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Number(dec!(1000)));
}

#[test]
fn test_value_date_arg_returns_raw_units_when_no_price_available() {
    // value(position, 2019-01-01): no price exists on or before that date,
    // so the position is returned as-is (raw units). Python beancount does
    // the same — its convert.get_value() falls through to `return units`.
    let directives = make_issue_892_directives();
    let result = execute_query(
        r"SELECT number(value(position, 2019-01-01)) AS v
          WHERE account ~ 'Brokerage'",
        &directives,
    );
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Number(dec!(4)));
}

#[test]
fn test_value_no_date_arg_still_uses_latest_price() {
    // Regression: value(position) without a date continues to use the latest
    // price (4 * 9999 = 39996), including future-dated prices. Matches Python.
    let directives = make_issue_892_directives();
    let result = execute_query(
        r"SELECT number(value(position)) AS v
          WHERE account ~ 'Brokerage'",
        &directives,
    );
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Number(dec!(39996)));
}

#[test]
fn test_value_date_arg_in_aggregate_context() {
    // Issue #892 fix must cover the aggregate-evaluation path too —
    // see executor/mod.rs `evaluate_function_on_values` for "VALUE".
    let directives = make_issue_892_directives();
    let result = execute_query(
        r"SELECT account, number(value(sum(position), 2020-06-01)) AS v
          WHERE account ~ 'Brokerage'
          GROUP BY account",
        &directives,
    );
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][1], Value::Number(dec!(1200)));
}

#[test]
fn test_value_currency_string_is_rustledger_extension() {
    // Regression: the existing `value(x, 'USD')` extension (not in Python
    // beancount — Python uses CONVERT for this) continues to work and uses
    // the latest price. A caller wanting an explicit currency AND a historical
    // price should use CONVERT(x, 'USD', date).
    let directives = make_issue_892_directives();
    let result = execute_query(
        r"SELECT number(value(position, 'USD')) AS v
          WHERE account ~ 'Brokerage'",
        &directives,
    );
    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::Number(dec!(39996)));
}

#[test]
fn test_value_rejects_invalid_second_argument_type() {
    // The error message should mention both accepted types (date and currency).
    let directives = make_issue_892_directives();
    let query = parse(r"SELECT value(position, 42) AS v WHERE account ~ 'Brokerage'")
        .expect("query should parse");
    let mut executor = Executor::new(&directives);
    let err = executor.execute(&query).expect_err("should reject integer");
    let msg = format!("{err}");
    assert!(
        msg.contains("date") && msg.contains("currency"),
        "error should mention both accepted types, got: {msg}"
    );
}

#[test]
fn test_value_rejects_invalid_second_argument_in_aggregate_context() {
    // Parallel coverage to the non-aggregate test above: the aggregate-evaluation
    // path (evaluate_function_on_values) has its own dispatch and should reject
    // non-date/non-string second arguments with the same error message.
    let directives = make_issue_892_directives();
    let query = parse(
        r"SELECT account, value(sum(position), 42) AS v
          WHERE account ~ 'Brokerage'
          GROUP BY account",
    )
    .expect("query should parse");
    let mut executor = Executor::new(&directives);
    let err = executor
        .execute(&query)
        .expect_err("aggregate-context should reject integer too");
    let msg = format!("{err}");
    assert!(
        msg.contains("date") && msg.contains("currency"),
        "aggregate error should mention both accepted types, got: {msg}"
    );
}

// ============================================================================
// #prices System Table Tests (Issue #562)
// ============================================================================

/// Helper to create directives with price data for #prices table tests.
fn make_prices_test_directives() -> Vec<Directive> {
    vec![
        // Multiple price directives
        Directive::Price(Price::new(
            date(2025, 1, 1),
            "EUR",
            Amount::new(dec!(1.95583), "BAM"),
        )),
        Directive::Price(Price::new(
            date(2025, 1, 1),
            "EUR",
            Amount::new(dec!(1.0268), "USD"),
        )),
        Directive::Price(Price::new(
            date(2025, 1, 1),
            "EUR",
            Amount::new(dec!(1.1325), "USD"),
        )),
        Directive::Price(Price::new(
            date(2025, 1, 10),
            "CHF",
            Amount::new(dec!(1.0647), "EUR"),
        )),
        Directive::Price(Price::new(
            date(2025, 3, 30),
            "ABC",
            Amount::new(dec!(1.20), "EUR"),
        )),
        Directive::Price(Price::new(
            date(2025, 4, 15),
            "ABC",
            Amount::new(dec!(1.35), "EUR"),
        )),
    ]
}

#[test]
fn test_prices_table_basic_select() {
    // Test: SELECT date, currency, amount FROM #prices
    let directives = make_prices_test_directives();
    let result = execute_query("SELECT date, currency, amount FROM #prices", &directives);

    assert_eq!(result.columns, vec!["date", "currency", "amount"]);
    assert_eq!(result.len(), 6); // 6 price directives

    // Verify first row (should be sorted by date)
    assert_eq!(result.rows[0][0], Value::Date(date(2025, 1, 1)));
}

#[test]
fn test_prices_table_select_all() {
    // Test: SELECT * FROM #prices
    let directives = make_prices_test_directives();
    let result = execute_query("SELECT * FROM #prices", &directives);

    // Wildcard expands to all columns
    assert_eq!(result.len(), 6);
}

#[test]
fn test_prices_table_with_where_clause() {
    // Test: SELECT * FROM #prices WHERE currency = 'EUR'
    let directives = make_prices_test_directives();
    let result = execute_query("SELECT * FROM #prices WHERE currency = 'EUR'", &directives);

    // EUR has 3 price entries (2025-01-01 x3 = different quote currencies)
    assert_eq!(result.len(), 3);
}

#[test]
fn test_prices_table_with_date_filter() {
    // Test: SELECT * FROM #prices WHERE date > 2025-01-01
    let directives = make_prices_test_directives();
    let result = execute_query("SELECT * FROM #prices WHERE date > 2025-01-01", &directives);

    // After 2025-01-01: CHF on 01-10, ABC on 03-30 and 04-15
    assert_eq!(result.len(), 3);
}

#[test]
fn test_prices_table_with_order_by() {
    // Test: SELECT * FROM #prices ORDER BY date DESC
    let directives = make_prices_test_directives();
    let result = execute_query("SELECT * FROM #prices ORDER BY date DESC", &directives);

    // Most recent date should be first (2025-04-15)
    assert_eq!(result.rows[0][0], Value::Date(date(2025, 4, 15)));
    // Oldest date should be last (2025-01-01)
    assert_eq!(
        result.rows[result.len() - 1][0],
        Value::Date(date(2025, 1, 1))
    );
}

#[test]
fn test_prices_table_with_limit() {
    // Test: SELECT * FROM #prices LIMIT 2
    let directives = make_prices_test_directives();
    let result = execute_query("SELECT * FROM #prices LIMIT 2", &directives);

    assert_eq!(result.len(), 2);
}

#[test]
fn test_prices_table_currency_column_value() {
    // Test that currency column contains base currency strings
    let directives = vec![Directive::Price(Price::new(
        date(2024, 1, 1),
        "AAPL",
        Amount::new(dec!(150), "USD"),
    ))];
    let result = execute_query("SELECT currency FROM #prices", &directives);

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("AAPL".to_string()));
}

#[test]
fn test_prices_table_amount_column_value() {
    // Test that amount column contains Amount values with price + quote currency
    let directives = vec![Directive::Price(Price::new(
        date(2024, 1, 1),
        "AAPL",
        Amount::new(dec!(150.50), "USD"),
    ))];
    let result = execute_query("SELECT amount FROM #prices", &directives);

    assert_eq!(result.len(), 1);
    match &result.rows[0][0] {
        Value::Amount(amt) => {
            assert_eq!(amt.number, dec!(150.50));
            assert_eq!(amt.currency.as_ref(), "USD");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_prices_table_empty() {
    // Test: SELECT * FROM #prices with no price directives
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #prices", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_prices_table_with_distinct() {
    // Test: SELECT DISTINCT currency FROM #prices
    let directives = make_prices_test_directives();
    let result = execute_query("SELECT DISTINCT currency FROM #prices", &directives);

    // Should have 4 distinct currencies: EUR, CHF, ABC
    // Actually EUR appears 3 times, CHF 1 time, ABC 2 times
    assert_eq!(result.len(), 3);
}

#[test]
fn test_prices_table_all_columns() {
    // Test: Verify all columns are accessible and have correct types
    let directives = vec![Directive::Price(Price::new(
        date(2024, 6, 15),
        "MSFT",
        Amount::new(dec!(400.50), "USD"),
    ))];
    let result = execute_query("SELECT date, currency, amount FROM #prices", &directives);

    assert_eq!(result.len(), 1);
    assert_eq!(result.columns, vec!["date", "currency", "amount"]);

    // Verify date column
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 15)));
    // Verify currency column
    assert_eq!(result.rows[0][1], Value::String("MSFT".to_string()));
    // Verify amount column
    match &result.rows[0][2] {
        Value::Amount(amt) => {
            assert_eq!(amt.number, dec!(400.50));
            assert_eq!(amt.currency.as_ref(), "USD");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_prices_table_case_insensitive() {
    // Test: #prices, #PRICES, and #Prices should all work
    let directives = vec![Directive::Price(Price::new(
        date(2024, 6, 15),
        "EUR",
        Amount::new(dec!(1.10), "USD"),
    ))];

    // Lowercase
    let result_lower = execute_query("SELECT * FROM #prices", &directives);
    assert_eq!(result_lower.len(), 1);

    // Uppercase
    let result_upper = execute_query("SELECT * FROM #PRICES", &directives);
    assert_eq!(result_upper.len(), 1);

    // Mixed case
    let result_mixed = execute_query("SELECT * FROM #Prices", &directives);
    assert_eq!(result_mixed.len(), 1);

    // All results should be identical
    assert_eq!(result_lower.rows, result_upper.rows);
    assert_eq!(result_lower.rows, result_mixed.rows);
}

#[test]
fn test_prices_table_unknown_system_table_error() {
    // Test: Unknown system table should show helpful error message
    let directives: Vec<Directive> = vec![];
    let query = parse("SELECT * FROM #unknown").expect("query should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query);

    match result {
        Err(e) => {
            let msg = e.to_string();
            assert!(
                msg.contains("#unknown"),
                "Error should mention the table name"
            );
            assert!(
                msg.contains("#balances") && msg.contains("#prices"),
                "Error should hint about available system tables"
            );
        }
        Ok(_) => panic!("Expected error for unknown system table"),
    }
}

#[test]
fn test_prices_table_deterministic_ordering() {
    // Test: Multiple prices on the same date should have deterministic order by currency
    let directives = vec![
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "EUR",
            Amount::new(dec!(1.10), "USD"),
        )),
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "CHF",
            Amount::new(dec!(1.15), "USD"),
        )),
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "ABC",
            Amount::new(dec!(50.00), "USD"),
        )),
    ];
    let result = execute_query("SELECT currency FROM #prices", &directives);

    // Should be sorted by (date, currency), so ABC, CHF, EUR
    assert_eq!(result.len(), 3);
    assert_eq!(result.rows[0][0], Value::String("ABC".to_string()));
    assert_eq!(result.rows[1][0], Value::String("CHF".to_string()));
    assert_eq!(result.rows[2][0], Value::String("EUR".to_string()));
}

// ============================================================================
// #balances System Table Tests (Issue #563)
// ============================================================================

fn make_balances_test_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Checking")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Savings")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Balance(Balance::new(
            date(2024, 11, 7),
            "Assets:Bank:Checking",
            Amount::new(dec!(595.47), "EUR"),
        )),
        Directive::Balance(Balance::new(
            date(2024, 11, 8),
            "Assets:Bank:Savings",
            Amount::new(dec!(5775.09), "EUR"),
        )),
        Directive::Balance(Balance::new(
            date(2024, 11, 9),
            "Assets:Cash",
            Amount::new(dec!(0.00), "EUR"),
        )),
    ]
}

#[test]
fn test_balances_table_basic_select() {
    // Test: SELECT date, account, amount FROM #balances
    let directives = make_balances_test_directives();
    let result = execute_query("SELECT date, account, amount FROM #balances", &directives);

    assert_eq!(result.len(), 3);
    assert_eq!(result.columns, vec!["date", "account", "amount"]);
}

#[test]
fn test_balances_table_select_all() {
    // Test: SELECT * FROM #balances
    let directives = make_balances_test_directives();
    let result = execute_query("SELECT * FROM #balances", &directives);

    assert_eq!(result.len(), 3);
    assert_eq!(result.columns, vec!["date", "account", "amount"]);
}

#[test]
fn test_balances_table_with_where_clause() {
    // Test: SELECT * FROM #balances WHERE account ~ 'Checking'
    let directives = make_balances_test_directives();
    let result = execute_query(
        "SELECT * FROM #balances WHERE account ~ 'Checking'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(
        result.rows[0][1],
        Value::String("Assets:Bank:Checking".to_string())
    );
}

#[test]
fn test_balances_table_with_date_filter() {
    // Test: SELECT * FROM #balances WHERE date >= 2024-11-08
    let directives = make_balances_test_directives();
    let result = execute_query(
        "SELECT * FROM #balances WHERE date >= 2024-11-08",
        &directives,
    );

    assert_eq!(result.len(), 2);
}

#[test]
fn test_balances_table_with_order_by() {
    // Test: SELECT * FROM #balances ORDER BY account
    let directives = make_balances_test_directives();
    let result = execute_query(
        "SELECT account FROM #balances ORDER BY account",
        &directives,
    );

    assert_eq!(result.len(), 3);
    // Alphabetical order: Assets:Bank:Checking, Assets:Bank:Savings, Assets:Cash
    assert_eq!(
        result.rows[0][0],
        Value::String("Assets:Bank:Checking".to_string())
    );
    assert_eq!(
        result.rows[1][0],
        Value::String("Assets:Bank:Savings".to_string())
    );
    assert_eq!(result.rows[2][0], Value::String("Assets:Cash".to_string()));
}

#[test]
fn test_balances_table_with_limit() {
    // Test: SELECT * FROM #balances LIMIT 2
    let directives = make_balances_test_directives();
    let result = execute_query("SELECT * FROM #balances LIMIT 2", &directives);

    assert_eq!(result.len(), 2);
}

#[test]
fn test_balances_table_empty() {
    // Test: SELECT * FROM #balances with no balance directives
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #balances", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_balances_table_amount_column_value() {
    // Test: Verify amount column contains proper Amount values
    let directives = vec![Directive::Balance(Balance::new(
        date(2024, 6, 15),
        "Assets:Checking",
        Amount::new(dec!(1234.56), "USD"),
    ))];
    let result = execute_query("SELECT amount FROM #balances", &directives);

    assert_eq!(result.len(), 1);
    match &result.rows[0][0] {
        Value::Amount(amt) => {
            assert_eq!(amt.number, dec!(1234.56));
            assert_eq!(amt.currency.as_ref(), "USD");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_balances_table_all_columns() {
    // Test: Verify all columns are accessible and have correct types
    let directives = vec![Directive::Balance(Balance::new(
        date(2024, 11, 7),
        "Assets:Bank:Checking",
        Amount::new(dec!(595.47), "EUR"),
    ))];
    let result = execute_query("SELECT date, account, amount FROM #balances", &directives);

    assert_eq!(result.len(), 1);
    assert_eq!(result.columns, vec!["date", "account", "amount"]);

    // Verify date column
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 11, 7)));
    // Verify account column
    assert_eq!(
        result.rows[0][1],
        Value::String("Assets:Bank:Checking".to_string())
    );
    // Verify amount column
    match &result.rows[0][2] {
        Value::Amount(amt) => {
            assert_eq!(amt.number, dec!(595.47));
            assert_eq!(amt.currency.as_ref(), "EUR");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_balances_table_case_insensitive() {
    // Test: #balances, #BALANCES, and #Balances should all work
    let directives = vec![Directive::Balance(Balance::new(
        date(2024, 6, 15),
        "Assets:Checking",
        Amount::new(dec!(100.00), "USD"),
    ))];

    // Lowercase
    let result_lower = execute_query("SELECT * FROM #balances", &directives);
    assert_eq!(result_lower.len(), 1);

    // Uppercase
    let result_upper = execute_query("SELECT * FROM #BALANCES", &directives);
    assert_eq!(result_upper.len(), 1);

    // Mixed case
    let result_mixed = execute_query("SELECT * FROM #Balances", &directives);
    assert_eq!(result_mixed.len(), 1);

    // All results should be identical
    assert_eq!(result_lower.rows, result_upper.rows);
    assert_eq!(result_lower.rows, result_mixed.rows);
}

#[test]
fn test_balances_table_deterministic_ordering() {
    // Test: Multiple balances on the same date should have deterministic order by account
    let directives = vec![
        Directive::Balance(Balance::new(
            date(2024, 1, 1),
            "Assets:Zebra",
            Amount::new(dec!(100.00), "USD"),
        )),
        Directive::Balance(Balance::new(
            date(2024, 1, 1),
            "Assets:Apple",
            Amount::new(dec!(200.00), "USD"),
        )),
        Directive::Balance(Balance::new(
            date(2024, 1, 1),
            "Assets:Banana",
            Amount::new(dec!(300.00), "USD"),
        )),
    ];
    let result = execute_query("SELECT account FROM #balances", &directives);

    // Should be sorted by (date, account), so Apple, Banana, Zebra
    assert_eq!(result.len(), 3);
    assert_eq!(result.rows[0][0], Value::String("Assets:Apple".to_string()));
    assert_eq!(
        result.rows[1][0],
        Value::String("Assets:Banana".to_string())
    );
    assert_eq!(result.rows[2][0], Value::String("Assets:Zebra".to_string()));
}

// ============================================================================
// #commodities System Table Tests
// ============================================================================

fn make_commodities_test_directives() -> Vec<Directive> {
    vec![
        Directive::Commodity(Commodity::new(date(2024, 1, 1), "USD")),
        Directive::Commodity(Commodity::new(date(2024, 1, 1), "EUR")),
        Directive::Commodity(Commodity::new(date(2024, 2, 1), "AAPL")),
        Directive::Commodity(Commodity::new(date(2024, 2, 15), "BTC")),
    ]
}

#[test]
fn test_commodities_table_basic_select() {
    let directives = make_commodities_test_directives();
    let result = execute_query("SELECT date, name FROM #commodities", &directives);

    assert_eq!(result.columns, vec!["date", "name"]);
    assert_eq!(result.len(), 4);
}

#[test]
fn test_commodities_table_select_all() {
    let directives = make_commodities_test_directives();
    let result = execute_query("SELECT * FROM #commodities", &directives);

    assert_eq!(result.len(), 4);
}

#[test]
fn test_commodities_table_with_where_clause() {
    let directives = make_commodities_test_directives();
    let result = execute_query("SELECT * FROM #commodities WHERE name = 'EUR'", &directives);

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][1], Value::String("EUR".to_string()));
}

#[test]
fn test_commodities_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #commodities", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_commodities_table_case_insensitive() {
    let directives = make_commodities_test_directives();

    let result_lower = execute_query("SELECT * FROM #commodities", &directives);
    let result_upper = execute_query("SELECT * FROM #COMMODITIES", &directives);
    let result_mixed = execute_query("SELECT * FROM #Commodities", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
    assert_eq!(result_lower.rows, result_mixed.rows);
}

#[test]
fn test_commodities_table_deterministic_ordering() {
    let directives = vec![
        Directive::Commodity(Commodity::new(date(2024, 1, 1), "ZZZ")),
        Directive::Commodity(Commodity::new(date(2024, 1, 1), "AAA")),
        Directive::Commodity(Commodity::new(date(2024, 1, 1), "MMM")),
    ];
    let result = execute_query("SELECT name FROM #commodities", &directives);

    // Should be sorted by (date, name)
    assert_eq!(result.rows[0][0], Value::String("AAA".to_string()));
    assert_eq!(result.rows[1][0], Value::String("MMM".to_string()));
    assert_eq!(result.rows[2][0], Value::String("ZZZ".to_string()));
}

// ============================================================================
// #events System Table Tests
// ============================================================================

fn make_events_test_directives() -> Vec<Directive> {
    vec![
        Directive::Event(Event::new(date(2024, 1, 1), "location", "New York")),
        Directive::Event(Event::new(date(2024, 3, 15), "employer", "Acme Corp")),
        Directive::Event(Event::new(date(2024, 6, 1), "location", "San Francisco")),
    ]
}

#[test]
fn test_events_table_basic_select() {
    let directives = make_events_test_directives();
    let result = execute_query("SELECT date, type, description FROM #events", &directives);

    assert_eq!(result.columns, vec!["date", "type", "description"]);
    assert_eq!(result.len(), 3);
}

#[test]
fn test_events_table_select_all() {
    let directives = make_events_test_directives();
    let result = execute_query("SELECT * FROM #events", &directives);

    assert_eq!(result.len(), 3);
}

#[test]
fn test_events_table_with_where_clause() {
    let directives = make_events_test_directives();
    let result = execute_query("SELECT * FROM #events WHERE type = 'location'", &directives);

    assert_eq!(result.len(), 2);
}

#[test]
fn test_events_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #events", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_events_table_case_insensitive() {
    let directives = make_events_test_directives();

    let result_lower = execute_query("SELECT * FROM #events", &directives);
    let result_upper = execute_query("SELECT * FROM #EVENTS", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
}

// ============================================================================
// #notes System Table Tests
// ============================================================================

fn make_notes_test_directives() -> Vec<Directive> {
    vec![
        Directive::Note(Note::new(
            date(2024, 1, 15),
            "Assets:Bank:Checking",
            "Opened checking account",
        )),
        Directive::Note(Note::new(
            date(2024, 2, 20),
            "Expenses:Food",
            "Started tracking food expenses",
        )),
        Directive::Note(Note::new(
            date(2024, 3, 1),
            "Assets:Bank:Checking",
            "Changed overdraft settings",
        )),
    ]
}

#[test]
fn test_notes_table_basic_select() {
    let directives = make_notes_test_directives();
    let result = execute_query("SELECT date, account, comment FROM #notes", &directives);

    assert_eq!(result.columns, vec!["date", "account", "comment"]);
    assert_eq!(result.len(), 3);
}

#[test]
fn test_notes_table_select_all() {
    let directives = make_notes_test_directives();
    let result = execute_query("SELECT * FROM #notes", &directives);

    assert_eq!(result.len(), 3);
}

#[test]
fn test_notes_table_with_where_clause() {
    let directives = make_notes_test_directives();
    let result = execute_query(
        "SELECT * FROM #notes WHERE account ~ 'Checking'",
        &directives,
    );

    assert_eq!(result.len(), 2);
}

#[test]
fn test_notes_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #notes", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_notes_table_case_insensitive() {
    let directives = make_notes_test_directives();

    let result_lower = execute_query("SELECT * FROM #notes", &directives);
    let result_upper = execute_query("SELECT * FROM #NOTES", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
}

// ============================================================================
// #documents System Table Tests
// ============================================================================

fn make_documents_test_directives() -> Vec<Directive> {
    vec![
        Directive::Document(
            Document::new(
                date(2024, 1, 15),
                "Assets:Bank:Checking",
                "/docs/statement-jan.pdf",
            )
            .with_tag("statement")
            .with_link("doc-001"),
        ),
        Directive::Document(Document::new(
            date(2024, 2, 15),
            "Assets:Bank:Checking",
            "/docs/statement-feb.pdf",
        )),
        Directive::Document(
            Document::new(date(2024, 3, 1), "Expenses:Food", "/receipts/grocery.jpg")
                .with_tag("receipt"),
        ),
    ]
}

#[test]
fn test_documents_table_basic_select() {
    let directives = make_documents_test_directives();
    let result = execute_query(
        "SELECT date, account, filename, tags, links FROM #documents",
        &directives,
    );

    assert_eq!(
        result.columns,
        vec!["date", "account", "filename", "tags", "links"]
    );
    assert_eq!(result.len(), 3);
}

#[test]
fn test_documents_table_select_all() {
    let directives = make_documents_test_directives();
    let result = execute_query("SELECT * FROM #documents", &directives);

    assert_eq!(result.len(), 3);
}

#[test]
fn test_documents_table_with_where_clause() {
    let directives = make_documents_test_directives();
    let result = execute_query(
        "SELECT * FROM #documents WHERE account ~ 'Checking'",
        &directives,
    );

    assert_eq!(result.len(), 2);
}

#[test]
fn test_documents_table_tags_column() {
    let directives = make_documents_test_directives();
    let result = execute_query(
        "SELECT filename, tags FROM #documents WHERE filename ~ 'jan'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::StringSet(tags) = &result.rows[0][1] {
        assert!(tags.contains(&"statement".to_string()));
    } else {
        panic!("Expected StringSet for tags");
    }
}

#[test]
fn test_documents_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #documents", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_documents_table_case_insensitive() {
    let directives = make_documents_test_directives();

    let result_lower = execute_query("SELECT * FROM #documents", &directives);
    let result_upper = execute_query("SELECT * FROM #DOCUMENTS", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
}

// ============================================================================
// #accounts System Table Tests
// ============================================================================

fn make_accounts_test_directives() -> Vec<Directive> {
    vec![
        Directive::Open(
            Open::new(date(2024, 1, 1), "Assets:Bank:Checking")
                .with_currencies(vec!["USD".into(), "EUR".into()]),
        ),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Savings")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Investment").with_booking("FIFO")),
        Directive::Open(Open::new(date(2024, 2, 1), "Expenses:Food")),
        Directive::Close(Close::new(date(2024, 12, 31), "Assets:Bank:Savings")),
    ]
}

#[test]
fn test_accounts_table_basic_select() {
    let directives = make_accounts_test_directives();
    let result = execute_query(
        "SELECT account, open, close, currencies, booking FROM #accounts",
        &directives,
    );

    assert_eq!(
        result.columns,
        vec!["account", "open", "close", "currencies", "booking"]
    );
    // 4 unique accounts
    assert_eq!(result.len(), 4);
}

#[test]
fn test_accounts_table_select_all() {
    let directives = make_accounts_test_directives();
    let result = execute_query("SELECT * FROM #accounts", &directives);

    assert_eq!(result.len(), 4);
}

#[test]
fn test_accounts_table_open_close_dates() {
    let directives = make_accounts_test_directives();
    let result = execute_query(
        "SELECT account, open, close FROM #accounts WHERE account = 'Assets:Bank:Savings'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][1], Value::Date(date(2024, 1, 1)));
    assert_eq!(result.rows[0][2], Value::Date(date(2024, 12, 31)));
}

#[test]
fn test_accounts_table_currencies_column() {
    let directives = make_accounts_test_directives();
    let result = execute_query(
        "SELECT account, currencies FROM #accounts WHERE account = 'Assets:Bank:Checking'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::StringSet(currencies) = &result.rows[0][1] {
        assert!(currencies.contains(&"USD".to_string()));
        assert!(currencies.contains(&"EUR".to_string()));
    } else {
        panic!("Expected StringSet for currencies");
    }
}

#[test]
fn test_accounts_table_booking_column() {
    let directives = make_accounts_test_directives();
    let result = execute_query(
        "SELECT account, booking FROM #accounts WHERE account = 'Assets:Investment'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][1], Value::String("FIFO".to_string()));
}

#[test]
fn test_accounts_table_null_values() {
    let directives = make_accounts_test_directives();
    let result = execute_query(
        "SELECT account, close, booking FROM #accounts WHERE account = 'Expenses:Food'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    // close should be null (not closed)
    assert_eq!(result.rows[0][1], Value::Null);
    // booking should be null (not specified)
    assert_eq!(result.rows[0][2], Value::Null);
}

#[test]
fn test_accounts_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #accounts", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_accounts_table_case_insensitive() {
    let directives = make_accounts_test_directives();

    let result_lower = execute_query("SELECT * FROM #accounts", &directives);
    let result_upper = execute_query("SELECT * FROM #ACCOUNTS", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
}

#[test]
fn test_accounts_table_deterministic_ordering() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Zebra")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Apple")),
        Directive::Open(Open::new(date(2024, 1, 1), "Liabilities:Banana")),
    ];
    let result = execute_query("SELECT account FROM #accounts", &directives);

    // Should be sorted by account name
    assert_eq!(result.rows[0][0], Value::String("Assets:Apple".to_string()));
    assert_eq!(
        result.rows[1][0],
        Value::String("Expenses:Zebra".to_string())
    );
    assert_eq!(
        result.rows[2][0],
        Value::String("Liabilities:Banana".to_string())
    );
}

// ============================================================================
// #transactions System Table Tests
// ============================================================================

#[test]
fn test_transactions_table_basic_select() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT date, flag, payee, narration, tags, links, accounts FROM #transactions",
        &directives,
    );

    assert_eq!(
        result.columns,
        vec![
            "date",
            "flag",
            "payee",
            "narration",
            "tags",
            "links",
            "accounts"
        ]
    );
    // make_test_directives() has 5 transactions
    assert_eq!(result.len(), 5);
}

#[test]
fn test_transactions_table_select_all() {
    let directives = make_test_directives();
    let result = execute_query("SELECT * FROM #transactions", &directives);

    assert_eq!(result.len(), 5);
}

#[test]
fn test_transactions_table_with_where_clause() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT * FROM #transactions WHERE payee = 'Grocery Store'",
        &directives,
    );

    // 2 grocery transactions
    assert_eq!(result.len(), 2);
}

#[test]
fn test_transactions_table_tags_column() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT narration, tags FROM #transactions WHERE narration ~ 'groceries'",
        &directives,
    );

    assert!(!result.is_empty());
    for row in &result.rows {
        if let Value::StringSet(tags) = &row[1] {
            assert!(tags.contains(&"food".to_string()));
        }
    }
}

#[test]
fn test_transactions_table_accounts_column() {
    let directives = make_test_directives();
    let result = execute_query(
        "SELECT narration, accounts FROM #transactions WHERE narration = 'Monthly salary'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    if let Value::StringSet(accounts) = &result.rows[0][1] {
        assert!(accounts.contains(&"Income:Salary".to_string()));
        assert!(accounts.contains(&"Assets:Bank:Checking".to_string()));
    } else {
        panic!("Expected StringSet for accounts");
    }
}

#[test]
fn test_transactions_table_null_payee() {
    let directives = make_test_directives();
    // Transaction 4 (transfer) has no payee
    let result = execute_query(
        "SELECT narration, payee FROM #transactions WHERE narration = 'Transfer to savings'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][1], Value::Null);
}

#[test]
fn test_transactions_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #transactions", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_transactions_table_case_insensitive() {
    let directives = make_test_directives();

    let result_lower = execute_query("SELECT * FROM #transactions", &directives);
    let result_upper = execute_query("SELECT * FROM #TRANSACTIONS", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
}

// ============================================================================
// #entries System Table Tests
// ============================================================================

fn make_entries_test_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Commodity(Commodity::new(date(2024, 1, 1), "USD")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Test transaction")
                .with_payee("Test Payee")
                .with_tag("testtag")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD"))),
        ),
        Directive::Note(Note::new(date(2024, 2, 1), "Assets:Bank", "A note")),
        Directive::Event(Event::new(date(2024, 3, 1), "location", "NYC")),
    ]
}

#[test]
fn test_entries_table_basic_select() {
    let directives = make_entries_test_directives();
    let result = execute_query(
        "SELECT id, type, date, flag, payee, narration FROM #entries",
        &directives,
    );

    assert!(result.columns.contains(&"id".to_string()));
    assert!(result.columns.contains(&"type".to_string()));
    assert!(result.columns.contains(&"date".to_string()));
    assert_eq!(result.len(), 5);
}

#[test]
fn test_entries_table_select_all() {
    let directives = make_entries_test_directives();
    let result = execute_query("SELECT * FROM #entries", &directives);

    assert_eq!(result.len(), 5);
}

#[test]
fn test_entries_table_type_column() {
    let directives = make_entries_test_directives();
    let result = execute_query("SELECT type FROM #entries", &directives);

    let types: Vec<&Value> = result.rows.iter().map(|r| &r[0]).collect();
    assert!(types.contains(&&Value::String("open".to_string())));
    assert!(types.contains(&&Value::String("commodity".to_string())));
    assert!(types.contains(&&Value::String("transaction".to_string())));
    assert!(types.contains(&&Value::String("note".to_string())));
    assert!(types.contains(&&Value::String("event".to_string())));
}

#[test]
fn test_entries_table_with_where_clause() {
    let directives = make_entries_test_directives();
    let result = execute_query(
        "SELECT * FROM #entries WHERE type = 'transaction'",
        &directives,
    );

    assert_eq!(result.len(), 1);
}

#[test]
fn test_entries_table_transaction_fields() {
    let directives = make_entries_test_directives();
    let result = execute_query(
        "SELECT flag, payee, narration, tags, accounts FROM #entries WHERE type = 'transaction'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("*".to_string()));
    assert_eq!(result.rows[0][1], Value::String("Test Payee".to_string()));
    assert_eq!(
        result.rows[0][2],
        Value::String("Test transaction".to_string())
    );
    if let Value::StringSet(tags) = &result.rows[0][3] {
        assert!(tags.contains(&"testtag".to_string()));
    }
}

#[test]
fn test_entries_table_non_transaction_nulls() {
    let directives = make_entries_test_directives();
    let result = execute_query(
        "SELECT flag, payee, narration FROM #entries WHERE type = 'open'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Non-transaction entries should have null for transaction-specific fields
    assert_eq!(result.rows[0][0], Value::Null);
    assert_eq!(result.rows[0][1], Value::Null);
    assert_eq!(result.rows[0][2], Value::Null);
}

#[test]
fn test_entries_table_id_column() {
    let directives = make_entries_test_directives();
    let result = execute_query("SELECT id FROM #entries", &directives);

    // IDs should be sequential integers starting from 0
    for (i, row) in result.rows.iter().enumerate() {
        assert_eq!(row[0], Value::Integer(i as i64));
    }
}

#[test]
fn test_entries_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #entries", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_entries_table_case_insensitive() {
    let directives = make_entries_test_directives();

    let result_lower = execute_query("SELECT * FROM #entries", &directives);
    let result_upper = execute_query("SELECT * FROM #ENTRIES", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
}

// ============================================================================
// #postings System Table Tests
// ============================================================================

fn make_postings_test_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_payee("Store")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "More food")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(30), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-30), "USD"))),
        ),
    ]
}

#[test]
fn test_postings_table_basic_select() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT date, account, number, currency FROM #postings",
        &directives,
    );

    assert!(result.columns.contains(&"date".to_string()));
    assert!(result.columns.contains(&"account".to_string()));
    assert!(result.columns.contains(&"number".to_string()));
    assert!(result.columns.contains(&"currency".to_string()));
    // 2 transactions × 2 postings each = 4 postings
    assert_eq!(result.len(), 4);
}

#[test]
fn test_postings_table_select_all() {
    let directives = make_postings_test_directives();
    let result = execute_query("SELECT * FROM #postings", &directives);

    assert_eq!(result.len(), 4);
    // Check all columns are present
    assert!(result.columns.contains(&"date".to_string()));
    assert!(result.columns.contains(&"flag".to_string()));
    assert!(result.columns.contains(&"payee".to_string()));
    assert!(result.columns.contains(&"narration".to_string()));
    assert!(result.columns.contains(&"account".to_string()));
    assert!(result.columns.contains(&"number".to_string()));
    assert!(result.columns.contains(&"currency".to_string()));
    assert!(result.columns.contains(&"balance".to_string()));
}

#[test]
fn test_postings_table_with_where_clause() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT * FROM #postings WHERE account = 'Expenses:Food'",
        &directives,
    );

    assert_eq!(result.len(), 2);
}

#[test]
fn test_postings_table_running_balance() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT account, number, balance FROM #postings WHERE account = 'Expenses:Food'",
        &directives,
    );

    assert_eq!(result.len(), 2);
    // First posting: 50 USD, balance should be 50 USD
    // Second posting: 30 USD, balance should be 80 USD
    // Balance is an Inventory, check the values
    for row in &result.rows {
        if let Value::Inventory(_inv) = &row[2] {
            // Running balance is present
        } else if row[2] != Value::Null {
            panic!("Expected Inventory for balance, got {:?}", row[2]);
        }
    }
}

#[test]
fn test_postings_table_parent_transaction_columns() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT date, flag, payee, narration, account FROM #postings WHERE payee = 'Store'",
        &directives,
    );

    assert_eq!(result.len(), 2); // 2 postings from the transaction with payee "Store"
    for row in &result.rows {
        assert_eq!(row[0], Value::Date(date(2024, 1, 15)));
        assert_eq!(row[1], Value::String("*".to_string()));
        assert_eq!(row[2], Value::String("Store".to_string()));
        assert_eq!(row[3], Value::String("Groceries".to_string()));
    }
}

#[test]
fn test_postings_table_null_payee() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT payee, narration FROM #postings WHERE narration = 'More food'",
        &directives,
    );

    assert_eq!(result.len(), 2);
    // Second transaction has no payee
    assert_eq!(result.rows[0][0], Value::Null);
}

#[test]
fn test_postings_table_empty() {
    let directives: Vec<Directive> = vec![];
    let result = execute_query("SELECT * FROM #postings", &directives);

    assert!(result.is_empty());
}

#[test]
fn test_postings_table_case_insensitive() {
    let directives = make_postings_test_directives();

    let result_lower = execute_query("SELECT * FROM #postings", &directives);
    let result_upper = execute_query("SELECT * FROM #POSTINGS", &directives);

    assert_eq!(result_lower.rows, result_upper.rows);
}

#[test]
fn test_postings_table_with_order_by() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT date, account FROM #postings ORDER BY date DESC",
        &directives,
    );

    // Most recent date should be first (2024-01-20)
    assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 20)));
}

#[test]
fn test_postings_table_with_limit() {
    let directives = make_postings_test_directives();
    let result = execute_query("SELECT * FROM #postings LIMIT 2", &directives);

    assert_eq!(result.len(), 2);
}

#[test]
fn test_postings_table_cost_columns() {
    // Test that cost basis columns are populated correctly
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy stock")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD")
                            .with_date(date(2024, 1, 15))
                            .with_label("lot1"),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT account, number, currency, cost_number, cost_currency, cost_date, cost_label FROM #postings WHERE account = 'Assets:Brokerage'",
        &directives,
    );

    assert_eq!(result.len(), 1);

    // Verify posting units
    assert_eq!(
        result.rows[0][0],
        Value::String("Assets:Brokerage".to_string())
    );
    assert_eq!(result.rows[0][1], Value::Number(dec!(10)));
    assert_eq!(result.rows[0][2], Value::String("AAPL".to_string()));

    // Verify cost basis columns
    assert_eq!(result.rows[0][3], Value::Number(dec!(150)));
    assert_eq!(result.rows[0][4], Value::String("USD".to_string()));
    assert_eq!(result.rows[0][5], Value::Date(date(2024, 1, 15)));
    assert_eq!(result.rows[0][6], Value::String("lot1".to_string()));
}

#[test]
fn test_postings_table_cost_columns_null_when_no_cost() {
    // Test that cost columns are NULL when posting has no cost basis
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT account, cost_number, cost_currency, cost_date, cost_label FROM #postings WHERE account = 'Expenses:Food'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(
        result.rows[0][0],
        Value::String("Expenses:Food".to_string())
    );
    // All cost columns should be NULL
    assert_eq!(result.rows[0][1], Value::Null);
    assert_eq!(result.rows[0][2], Value::Null);
    assert_eq!(result.rows[0][3], Value::Null);
    assert_eq!(result.rows[0][4], Value::Null);
}

#[test]
fn test_postings_table_price_column() {
    // Test that price column is populated for postings with price annotation
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy at price")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL"))
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(150), "USD"))),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT account, price FROM #postings WHERE account = 'Assets:Brokerage'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][1] {
        Value::Amount(amt) => {
            assert_eq!(amt.number, dec!(150));
            assert_eq!(amt.currency.as_ref(), "USD");
        }
        other => panic!("Expected Amount for price, got {other:?}"),
    }
}

// ============================================================================
// Aggregate Function Dispatch Tests (short-circuit + evaluate_function_on_values)
// ============================================================================

#[test]
fn test_aggregate_context_non_aggregate_function_short_circuit() {
    // QUARTER(date) in GROUP BY — no aggregate args, should use evaluate_expr
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Q1")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 4, 15), "Q2")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(20), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-20), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT quarter(date) AS q, sum(number) FROM #postings WHERE account = 'Expenses:Food' GROUP BY q",
        &directives,
    );

    assert_eq!(result.len(), 2, "should have 2 quarters");
    // Verify quarter values are 1 and 2
    let quarters: Vec<_> = result.rows.iter().map(|r| &r[0]).collect();
    assert!(quarters.contains(&&Value::Integer(1)), "should contain Q1");
    assert!(quarters.contains(&&Value::Integer(2)), "should contain Q2");
}

#[test]
fn test_aggregate_context_function_wrapping_aggregate() {
    // YMONTH(MAX(date)) — arg contains aggregate, uses evaluate_function_on_values
    // Use the direct query path (not #postings table) since MAX on direct path
    // returns Value::Date correctly
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Jan")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 20), "Mar")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(20), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-20), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT ymonth(max(date)) WHERE account = 'Expenses:Food'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(result.rows[0][0], Value::String("2024-03".to_string()));
}

#[test]
fn test_aggregate_context_account_depth() {
    // ACCOUNT_DEPTH in GROUP BY — uses short-circuit (no aggregate args)
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food:Restaurant")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Transport")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Lunch")
                .with_posting(Posting::new(
                    "Expenses:Food:Restaurant",
                    Amount::new(dec!(25), "USD"),
                ))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-25), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT account_depth(account), count(*) GROUP BY account_depth(account)",
        &directives,
    );

    // Should work without UnknownFunction error
    assert!(!result.rows.is_empty());
}

#[test]
fn test_aggregate_context_weight_on_values() {
    // WEIGHT(sum(position)) — wraps aggregate, needs evaluate_function_on_values
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stock")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy")
                .with_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
        ),
    ];

    // Use direct path (not #postings table) for aggregate context
    let query =
        parse("SELECT account, weight(sum(position)) GROUP BY account").expect("should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query);
    assert!(
        result.is_ok(),
        "weight(sum(position)) should not error: {result:?}"
    );
}

// ============================================================================
// Postings Table: position column (#677)
// ============================================================================

#[test]
fn test_postings_table_position_column_simple() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT account, position FROM #postings WHERE account = 'Expenses:Food'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][1] {
        Value::Position(pos) => {
            assert_eq!(pos.units.number, dec!(50));
            assert_eq!(pos.units.currency.as_ref(), "USD");
            assert!(pos.cost.is_none());
        }
        other => panic!("Expected Position, got {other:?}"),
    }
}

#[test]
fn test_postings_table_position_column_with_cost() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy stock")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1500), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT account, position FROM #postings WHERE account = 'Assets:Brokerage'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][1] {
        Value::Position(pos) => {
            assert_eq!(pos.units.number, dec!(10));
            assert_eq!(pos.units.currency.as_ref(), "AAPL");
            let cost = pos.cost.as_ref().expect("should have cost");
            assert_eq!(cost.number, dec!(150));
            assert_eq!(cost.currency.as_ref(), "USD");
        }
        other => panic!("Expected Position, got {other:?}"),
    }
}

#[test]
fn test_postings_table_position_in_select_star() {
    let directives = make_postings_test_directives();
    let result = execute_query("SELECT * FROM #postings", &directives);

    assert!(
        result.columns.contains(&"position".to_string()),
        "position should be in SELECT * columns"
    );
}

// ============================================================================
// Postings Table New Columns Tests (issue #820)
// ============================================================================

#[test]
fn test_postings_table_type_and_id_columns() {
    let directives = make_postings_test_directives();
    let result = execute_query("SELECT type, id FROM #postings LIMIT 1", &directives);
    assert_eq!(result.rows[0][0], Value::String("transaction".to_string()));
    // id is an integer index
    assert!(matches!(result.rows[0][1], Value::Integer(_)));
}

#[test]
fn test_postings_table_date_parts() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT year, month, day FROM #postings WHERE narration = 'Groceries' LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::Integer(2024));
    assert_eq!(result.rows[0][1], Value::Integer(1));
    assert_eq!(result.rows[0][2], Value::Integer(15));
}

#[test]
fn test_postings_table_description_column() {
    let directives = make_postings_test_directives();
    // Transaction with payee: "Store | Groceries"
    let result = execute_query(
        "SELECT description FROM #postings WHERE payee = 'Store' LIMIT 1",
        &directives,
    );
    assert_eq!(
        result.rows[0][0],
        Value::String("Store | Groceries".to_string())
    );

    // Transaction without payee: just narration
    let result = execute_query(
        "SELECT description FROM #postings WHERE narration = 'More food' LIMIT 1",
        &directives,
    );
    assert_eq!(result.rows[0][0], Value::String("More food".to_string()));
}

#[test]
fn test_postings_table_posting_flag_column() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Test")
                .with_posting(
                    Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")).with_flag('!'),
                )
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
    ];
    let result = execute_query(
        "SELECT account, posting_flag FROM #postings ORDER BY account",
        &directives,
    );
    // Assets:Bank has no posting flag
    assert_eq!(result.rows[0][1], Value::Null);
    // Expenses:Food has '!' flag
    assert_eq!(result.rows[1][1], Value::String("!".to_string()));
}

#[test]
fn test_postings_table_other_accounts_column() {
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT account, other_accounts FROM #postings WHERE account = 'Expenses:Food' LIMIT 1",
        &directives,
    );
    assert_eq!(
        result.rows[0][1],
        Value::StringSet(vec!["Assets:Bank".to_string()])
    );
}

#[test]
fn test_postings_table_accounts_column() {
    let directives = make_postings_test_directives();
    let result = execute_query("SELECT accounts FROM #postings LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::StringSet(vec!["Assets:Bank".to_string(), "Expenses:Food".to_string(),])
    );
}

#[test]
fn test_postings_table_tags_links_columns() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Tagged")
                .with_tag("trip")
                .with_link("receipt-123")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"))),
        ),
    ];
    let result = execute_query("SELECT tags, links FROM #postings LIMIT 1", &directives);
    assert_eq!(
        result.rows[0][0],
        Value::StringSet(vec!["trip".to_string()])
    );
    assert_eq!(
        result.rows[0][1],
        Value::StringSet(vec!["receipt-123".to_string()])
    );
}

#[test]
fn test_postings_table_weight_column() {
    // Weight should be the cost-converted amount
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy stock")
                .with_posting(
                    Posting::new("Assets:Brokerage", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(150))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-1500), "USD"))),
        ),
    ];
    let result = execute_query(
        "SELECT account, weight FROM #postings WHERE account = 'Assets:Brokerage'",
        &directives,
    );
    // Weight for 10 AAPL @ 150 USD = 1500 USD
    assert_eq!(
        result.rows[0][1],
        Value::Amount(Amount::new(dec!(1500), "USD"))
    );
}

#[test]
fn test_postings_table_weight_no_cost() {
    // Without cost, weight = units
    let directives = make_postings_test_directives();
    let result = execute_query(
        "SELECT account, number, weight FROM #postings WHERE account = 'Expenses:Food' LIMIT 1",
        &directives,
    );
    assert_eq!(
        result.rows[0][2],
        Value::Amount(Amount::new(dec!(50), "USD"))
    );
}

#[test]
fn test_postings_table_weight_per_unit_price() {
    // Weight with @ per-unit price: units × price
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Foreign")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy euros")
                .with_posting(
                    Posting::new("Assets:Foreign", Amount::new(dec!(100), "EUR"))
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.10), "USD"))),
                )
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-110), "USD"))),
        ),
    ];
    let result = execute_query(
        "SELECT account, weight FROM #postings WHERE account = 'Assets:Foreign'",
        &directives,
    );
    // 100 EUR @ 1.10 USD → weight = 110 USD
    assert_eq!(
        result.rows[0][1],
        Value::Amount(Amount::new(dec!(110.00), "USD"))
    );
}

#[test]
fn test_postings_table_weight_total_price() {
    // Weight with @@ total price: the total price IS the weight
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Foreign")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy euros")
                .with_posting(
                    Posting::new("Assets:Foreign", Amount::new(dec!(100), "EUR"))
                        .with_price(PriceAnnotation::Total(Amount::new(dec!(110), "USD"))),
                )
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-110), "USD"))),
        ),
    ];
    let result = execute_query(
        "SELECT account, weight FROM #postings WHERE account = 'Assets:Foreign'",
        &directives,
    );
    // 100 EUR @@ 110 USD → weight = 110 USD (total, not 100 × 110)
    assert_eq!(
        result.rows[0][1],
        Value::Amount(Amount::new(dec!(110), "USD"))
    );
}

#[test]
fn test_weight_column_total_price_default_from() {
    // Verify weight via evaluate_column (default FROM) matches table builder
    // for @@ total price
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Foreign")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Buy euros")
                .with_posting(
                    Posting::new("Assets:Foreign", Amount::new(dec!(100), "EUR"))
                        .with_price(PriceAnnotation::Total(Amount::new(dec!(110), "USD"))),
                )
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-110), "USD"))),
        ),
    ];
    // Default FROM (uses evaluate_column)
    let result = execute_query(
        "SELECT weight WHERE account = 'Assets:Foreign'",
        &directives,
    );
    assert_eq!(
        result.rows[0][0],
        Value::Amount(Amount::new(dec!(110), "USD"))
    );
}

#[test]
fn test_postings_table_lineno_query() {
    // The original issue (#820) mentions SELECT lineno should work
    let directives = make_postings_test_directives();
    let result = execute_query("SELECT lineno FROM #postings LIMIT 1", &directives);
    assert_eq!(result.columns, vec!["lineno"]);
    // Without spanned directives, lineno will be Null, but the query should not error
    assert_eq!(result.rows.len(), 1);
}

#[test]
fn test_postings_table_all_beancount_columns() {
    // Verify all columns from Python beancount's postings table are present
    let directives = make_postings_test_directives();
    let result = execute_query("SELECT * FROM #postings LIMIT 1", &directives);
    let expected_columns = [
        "type",
        "id",
        "date",
        "year",
        "month",
        "day",
        "filename",
        "lineno",
        "location",
        "flag",
        "payee",
        "narration",
        "description",
        "tags",
        "links",
        "posting_flag",
        "account",
        "other_accounts",
        "number",
        "currency",
        "cost_number",
        "cost_currency",
        "cost_date",
        "cost_label",
        "position",
        "price",
        "weight",
        "balance",
        "meta",
        "accounts",
    ];
    for col in &expected_columns {
        assert!(
            result.columns.contains(&col.to_string()),
            "Missing column: {col}"
        );
    }
}

// ============================================================================
// System Table Error Message Tests
// ============================================================================

#[test]
fn test_unknown_system_table_error_lists_all_tables() {
    let directives: Vec<Directive> = vec![];
    let query = parse("SELECT * FROM #unknown").expect("query should parse");
    let mut executor = Executor::new(&directives);
    let result = executor.execute(&query);

    match result {
        Err(e) => {
            let msg = e.to_string();
            assert!(
                msg.contains("#unknown"),
                "Error should mention the table name"
            );
            // Check that all system tables are mentioned in the hint
            assert!(msg.contains("#accounts"), "Error should list #accounts");
            assert!(msg.contains("#balances"), "Error should list #balances");
            assert!(
                msg.contains("#commodities"),
                "Error should list #commodities"
            );
            assert!(msg.contains("#documents"), "Error should list #documents");
            assert!(msg.contains("#entries"), "Error should list #entries");
            assert!(msg.contains("#events"), "Error should list #events");
            assert!(msg.contains("#notes"), "Error should list #notes");
            assert!(msg.contains("#postings"), "Error should list #postings");
            assert!(msg.contains("#prices"), "Error should list #prices");
            assert!(
                msg.contains("#transactions"),
                "Error should list #transactions"
            );
        }
        Ok(_) => panic!("Expected error for unknown system table"),
    }
}

// ============================================================================
// CONVERT Function Tests
// ============================================================================

// Regression test for issue #565: convert(sum(position), 'EUR') fails with "unknown function"
// https://github.com/rustledger/rustledger/issues/565

/// Helper to create directives for CONVERT function tests.
fn make_convert_test_directives() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:CHF")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Other")),
        // Price: 1 CHF = 1.0647 EUR
        Directive::Price(Price::new(
            date(2025, 1, 10),
            "CHF",
            Amount::new(dec!(1.0647), "EUR"),
        )),
        // Incoming transfer of 3000 CHF
        Directive::Transaction(
            Transaction::new(date(2025, 7, 15), "Incoming transfer")
                .with_posting(Posting::new(
                    "Assets:Bank:CHF",
                    Amount::new(dec!(3000), "CHF"),
                ))
                .with_posting(Posting::new(
                    "Income:Other",
                    Amount::new(dec!(-3000), "CHF"),
                )),
        ),
    ]
}

#[test]
fn test_issue_565_convert_sum_position() {
    // Regression test for issue #565: convert(sum(position), 'EUR') fails with "unknown function"
    let directives = make_convert_test_directives();
    let result = execute_query(
        "SELECT account, convert(sum(position), 'EUR') WHERE account = 'Assets:Bank:CHF' GROUP BY account",
        &directives,
    );

    assert_eq!(result.len(), 1);
    assert_eq!(
        result.rows[0][0],
        Value::String("Assets:Bank:CHF".to_string())
    );

    // 3000 CHF × 1.0647 EUR/CHF = 3194.10 EUR
    match &result.rows[0][1] {
        Value::Amount(amt) => {
            assert_eq!(amt.currency.as_ref(), "EUR");
            assert_eq!(amt.number, dec!(3194.1)); // 3000 × 1.0647
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_convert_sum_position_already_target_currency() {
    // Test: convert when position is already in target currency
    let directives = make_convert_test_directives();
    let result = execute_query(
        "SELECT account, convert(sum(position), 'CHF') WHERE account = 'Assets:Bank:CHF' GROUP BY account",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][1] {
        Value::Amount(amt) => {
            assert_eq!(amt.currency.as_ref(), "CHF");
            assert_eq!(amt.number, dec!(3000)); // No conversion needed
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_convert_with_explicit_date() {
    // Test: convert(sum(position), 'EUR', date) with explicit date
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Other")),
        // Price at different dates
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "USD",
            Amount::new(dec!(0.90), "EUR"),
        )),
        Directive::Price(Price::new(
            date(2024, 6, 1),
            "USD",
            Amount::new(dec!(0.95), "EUR"),
        )),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 15), "Deposit")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(1000), "USD")))
                .with_posting(Posting::new(
                    "Income:Other",
                    Amount::new(dec!(-1000), "USD"),
                )),
        ),
    ];

    // Use earlier date price (0.90)
    let result = execute_query(
        "SELECT convert(sum(position), 'EUR', 2024-01-15) WHERE account = 'Assets:Bank' GROUP BY account",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][0] {
        Value::Amount(amt) => {
            assert_eq!(amt.currency.as_ref(), "EUR");
            assert_eq!(amt.number, dec!(900)); // 1000 × 0.90
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_convert_multiple_currencies_in_inventory() {
    // Test: convert an inventory with multiple currencies
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Other")),
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "USD",
            Amount::new(dec!(0.92), "EUR"),
        )),
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "GBP",
            Amount::new(dec!(1.17), "EUR"),
        )),
        // USD deposit
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "USD Deposit")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(1000), "USD")))
                .with_posting(Posting::new(
                    "Income:Other",
                    Amount::new(dec!(-1000), "USD"),
                )),
        ),
        // GBP deposit
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "GBP Deposit")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(500), "GBP")))
                .with_posting(Posting::new("Income:Other", Amount::new(dec!(-500), "GBP"))),
        ),
    ];

    let result = execute_query(
        "SELECT convert(sum(position), 'EUR') WHERE account = 'Assets:Bank' GROUP BY account",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][0] {
        Value::Amount(amt) => {
            assert_eq!(amt.currency.as_ref(), "EUR");
            // 1000 USD × 0.92 + 500 GBP × 1.17 = 920 + 585 = 1505 EUR
            assert_eq!(amt.number, dec!(1505));
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_convert_basic_amount() {
    // Test: convert a simple amount (non-aggregate context)
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "USD",
            Amount::new(dec!(0.92), "EUR"),
        )),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT convert(position, 'EUR') WHERE account = 'Expenses:Food'",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][0] {
        Value::Amount(amt) => {
            assert_eq!(amt.currency.as_ref(), "EUR");
            assert_eq!(amt.number, dec!(92)); // 100 × 0.92
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_convert_number_to_currency() {
    // Test: convert a plain number wraps it as amount with target currency
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-100), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT convert(sum(number(position)), 'EUR') WHERE account = 'Expenses:Food' GROUP BY account",
        &directives,
    );

    assert_eq!(result.len(), 1);
    match &result.rows[0][0] {
        Value::Amount(amt) => {
            assert_eq!(amt.currency.as_ref(), "EUR");
            assert_eq!(amt.number, dec!(100)); // Just wrapped as EUR
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

#[test]
fn test_convert_unconvertible_currency_kept_original() {
    // Test: when no price is available for conversion, keep original currency
    // (matches Python beancount behavior - returns original amount, not silent skip)
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:EUR")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:JPY")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:USD")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // EUR account - will be kept as-is (target currency)
        Directive::Transaction(
            Transaction::new(date(2024, 1, 1), "Opening EUR")
                .with_posting(Posting::new(
                    "Assets:Bank:EUR",
                    Amount::new(dec!(1000), "EUR"),
                ))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-1000), "EUR"),
                )),
        ),
        // JPY account - NO price defined, should be kept as JPY
        Directive::Transaction(
            Transaction::new(date(2024, 1, 1), "Opening JPY")
                .with_posting(Posting::new(
                    "Assets:Bank:JPY",
                    Amount::new(dec!(50000), "JPY"),
                ))
                .with_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-50000), "JPY"),
                )),
        ),
    ];

    // Query positions converting to EUR - JPY has no conversion rate
    let result = execute_query(
        "SELECT convert(sum(position), 'EUR') WHERE account ~ '^Assets:Bank' GROUP BY 1",
        &directives,
    );

    assert_eq!(result.len(), 1);
    // Should return an Inventory with both EUR and JPY (JPY kept as original)
    match &result.rows[0][0] {
        Value::Inventory(inv) => {
            let positions = inv.positions();
            assert_eq!(
                positions.len(),
                2,
                "Expected 2 positions (EUR + unconverted JPY)"
            );
            // Check both currencies are present
            let currencies: Vec<_> = positions
                .iter()
                .map(|p| p.units.currency.as_ref())
                .collect();
            assert!(currencies.contains(&"EUR"), "Should have EUR");
            assert!(currencies.contains(&"JPY"), "Should have JPY (unconverted)");
        }
        other => panic!("Expected Inventory with mixed currencies, got {other:?}"),
    }
}

// ============================================================================
// Issue #567 Regression Tests
// ============================================================================

/// Regression test for issue #567: `VALUE()` returns cost instead of market value.
/// <https://github.com/rustledger/rustledger/issues/567>
///
/// When a transaction has a @ price annotation, `VALUE()` should use that price
/// for market value calculation, not the cost price from the cost specification.
#[test]
fn test_issue_567_value_uses_implicit_price_from_annotation() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stocks")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        // Buy 5 ABC at cost 1.25 EUR each
        Directive::Transaction(
            Transaction::new(date(2024, 1, 10), "Buy stock")
                .with_posting(
                    Posting::new("Assets:Stocks", Amount::new(dec!(5), "ABC")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(1.25))
                            .with_currency("EUR")
                            .with_date(date(2024, 1, 10)),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-6.25), "EUR"))),
        ),
        // Sell with @ 1.40 EUR price annotation (creates implicit price)
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Sell stock")
                .with_posting(
                    Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                        .with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(1.25))
                                .with_currency("EUR")
                                .with_date(date(2024, 1, 10)),
                        )
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.40), "EUR"))),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(7.00), "EUR"))),
        ),
    ];

    // Query the buy transaction's position (the one with positive amount)
    let result = execute_query(
        "SELECT cost(position), value(position, 'EUR') WHERE account = 'Assets:Stocks' AND number > 0",
        &directives,
    );

    assert_eq!(result.len(), 1, "Should have 1 row for buy transaction");

    // Cost should be 5 * 1.25 = 6.25 EUR
    match &result.rows[0][0] {
        Value::Amount(cost) => {
            assert_eq!(
                cost.number,
                dec!(6.25),
                "Cost should be 5 * 1.25 = 6.25 EUR"
            );
            assert_eq!(cost.currency.as_ref(), "EUR");
        }
        other => panic!("Expected Amount for cost, got {other:?}"),
    }

    // VALUE should use market price 1.40 EUR (from @ annotation), NOT cost 1.25 EUR
    // 5 ABC * 1.40 EUR = 7.00 EUR
    match &result.rows[0][1] {
        Value::Amount(market_value) => {
            assert_eq!(
                market_value.number,
                dec!(7.00),
                "VALUE should use implicit price 1.40 from @ annotation, not cost 1.25. Got: {} EUR",
                market_value.number
            );
            assert_eq!(market_value.currency.as_ref(), "EUR");
        }
        other => panic!("Expected Amount for value, got {other:?}"),
    }
}

/// Test that `value(sum(position))` works with implicit prices from annotations.
#[test]
fn test_issue_567_value_sum_position_with_implicit_price() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Stocks")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        // Buy 10 XYZ at cost 50 USD each
        Directive::Transaction(
            Transaction::new(date(2024, 1, 10), "Buy XYZ")
                .with_posting(
                    Posting::new("Assets:Stocks", Amount::new(dec!(10), "XYZ")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(50))
                            .with_currency("USD"),
                    ),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-500), "USD"))),
        ),
        // Price goes up - sell some with @ 60 USD annotation
        Directive::Transaction(
            Transaction::new(date(2024, 2, 15), "Sell XYZ")
                .with_posting(
                    Posting::new("Assets:Stocks", Amount::new(dec!(-5), "XYZ"))
                        .with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(50))
                                .with_currency("USD"),
                        )
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(60), "USD"))),
                )
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(300), "USD"))),
        ),
    ];

    // Sum all positions and get value
    let result = execute_query(
        "SELECT value(sum(position), 'USD') WHERE account = 'Assets:Stocks' GROUP BY account",
        &directives,
    );

    assert_eq!(result.len(), 1);

    // Net position: 10 - 5 = 5 XYZ
    // Market value at latest price (60 USD from @ annotation): 5 * 60 = 300 USD
    match &result.rows[0][0] {
        Value::Amount(market_value) => {
            assert_eq!(
                market_value.number,
                dec!(300),
                "value(sum(position)) should use implicit price 60, giving 5 * 60 = 300 USD"
            );
            assert_eq!(market_value.currency.as_ref(), "USD");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }
}

// ============================================================================
// Issue #575: Implicit GROUP BY for aggregate queries
// ============================================================================

/// Regression test for issue #575: Query returns just one row
/// <https://github.com/rustledger/rustledger/issues/575>
///
/// When aggregate functions are mixed with non-aggregated columns and no explicit
/// GROUP BY is provided, Python beancount implicitly groups by the non-aggregated
/// columns. This test verifies that rustledger matches this behavior.
#[test]
fn test_issue_575_implicit_group_by() {
    let directives = make_issue_575_directives();
    let result = execute_query(
        r"SELECT sum(number), currency, account ORDER BY account",
        &directives,
    );

    // Should return 3 rows (one per unique account+currency combination)
    // Python beancount output:
    //   sum(num  cur       account
    //   -------  ---  -----------------
    //   -550.00  EUR  Assets:Bank
    //      5     ABC  Assets:Investment
    //    50.00  EUR  Expenses:Food
    assert_eq!(
        result.len(),
        3,
        "Should return 3 rows when implicitly grouping by currency and account"
    );

    // Check that we have the expected accounts (sorted by account name)
    let accounts: Vec<&str> = result
        .rows
        .iter()
        .map(|row| match &row[2] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for account name in column 2, got {other:?}"),
        })
        .collect();
    assert_eq!(
        accounts,
        vec!["Assets:Bank", "Assets:Investment", "Expenses:Food"]
    );

    // Check the sum for Assets:Bank (-50 - 500 = -550 EUR)
    if let Value::Number(n) = &result.rows[0][0] {
        assert_eq!(*n, dec!(-550), "Assets:Bank should have sum -550");
    } else {
        panic!("Expected Number for Assets:Bank sum");
    }

    // Check the sum for Assets:Investment (5 ABC)
    if let Value::Number(n) = &result.rows[1][0] {
        assert_eq!(*n, dec!(5), "Assets:Investment should have sum 5");
    } else {
        panic!("Expected Number for Assets:Investment sum");
    }

    // Check the sum for Expenses:Food (50 EUR)
    if let Value::Number(n) = &result.rows[2][0] {
        assert_eq!(*n, dec!(50), "Expenses:Food should have sum 50");
    } else {
        panic!("Expected Number for Expenses:Food sum");
    }
}

/// Test that pure aggregate queries without non-aggregate columns still work
#[test]
fn test_pure_aggregate_no_implicit_group_by() {
    let directives = make_issue_575_directives();
    let result = execute_query(r"SELECT count(*)", &directives);

    // Should return 1 row with the total count
    assert_eq!(result.len(), 1, "Pure aggregate should return 1 row");

    if let Value::Integer(n) = &result.rows[0][0] {
        // 4 postings total (2 from grocery, 2 from stock purchase)
        assert_eq!(*n, 4, "Should count all 4 postings");
    } else {
        panic!("Expected Integer for count(*)");
    }
}

/// Test explicit GROUP BY still works and takes precedence
#[test]
fn test_explicit_group_by_overrides_implicit() {
    let directives = make_issue_575_directives();
    let result = execute_query(
        r"SELECT sum(number), currency GROUP BY currency ORDER BY currency",
        &directives,
    );

    // Should return 2 rows (one per currency: ABC and EUR)
    assert_eq!(
        result.len(),
        2,
        "Explicit GROUP BY currency should return 2 rows"
    );

    // Check currencies
    let currencies: Vec<&str> = result
        .rows
        .iter()
        .map(|row| match &row[1] {
            Value::String(s) => s.as_str(),
            other => panic!("Expected String for currency in column 1, got {other:?}"),
        })
        .collect();
    assert_eq!(currencies, vec!["ABC", "EUR"]);
}

fn make_issue_575_directives() -> Vec<Directive> {
    // Recreate the exact ledger from issue #575
    vec![
        Directive::Open(Open::new(date(2026, 3, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2026, 3, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2026, 3, 1), "Assets:Investment")),
        Directive::Open(Open::new(date(2026, 3, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2026, 3, 1), "Income:Salary")),
        // Transaction 1: Groceries (50 EUR from bank to food)
        Directive::Transaction(
            Transaction::new(date(2026, 3, 26), "Grocery shopping")
                .with_payee("Grocery Store")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "EUR")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "EUR"))),
        ),
        // Transaction 2: Buy stock (5 ABC @ 100 EUR each = 500 EUR)
        Directive::Transaction(
            Transaction::new(date(2026, 3, 27), "Buy Stock")
                .with_posting(
                    Posting::new("Assets:Investment", Amount::new(dec!(5), "ABC")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(100))
                            .with_currency("EUR"),
                    ),
                )
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-500), "EUR"))),
        ),
    ]
}

// ============================================================================
// Regression Test: Issue #586 - CONVERT with NULL (empty sum)
// ============================================================================

/// Regression test for issue #586: `convert(sum(position), 'GBP')` fails on accounts with no balance
/// <https://github.com/rustledger/rustledger/issues/586>
///
/// When an account has transactions that net to zero, or when `sum(position)` returns an
/// empty inventory, `convert()` should return 0 in the target currency instead of failing.
/// This matches Python beancount's behavior.
#[test]
fn test_issue_586_convert_null_returns_zero() {
    // Set up accounts with different balance scenarios
    let directives = vec![
        Directive::Open(Open::new(
            date(2024, 1, 1),
            "Liabilities:CreditCards:WithBalance",
        )),
        Directive::Open(Open::new(
            date(2024, 1, 1),
            "Liabilities:CreditCards:ZeroBalance",
        )),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Refund")),
        // Price for conversion
        Directive::Price(Price::new(
            date(2024, 1, 1),
            "EUR",
            Amount::new(dec!(0.85), "GBP"),
        )),
        // Transaction on WithBalance account
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Groceries")
                .with_posting(Posting::new(
                    "Liabilities:CreditCards:WithBalance",
                    Amount::new(dec!(-100), "EUR"),
                ))
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "EUR"))),
        ),
        // Two transactions on ZeroBalance that cancel each other out
        Directive::Transaction(
            Transaction::new(date(2024, 1, 16), "Purchase")
                .with_posting(Posting::new(
                    "Liabilities:CreditCards:ZeroBalance",
                    Amount::new(dec!(-50), "EUR"),
                ))
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(50), "EUR"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 17), "Refund")
                .with_posting(Posting::new(
                    "Liabilities:CreditCards:ZeroBalance",
                    Amount::new(dec!(50), "EUR"),
                ))
                .with_posting(Posting::new("Income:Refund", Amount::new(dec!(-50), "EUR"))),
        ),
    ];

    // Query that groups by account
    let result = execute_query(
        r"SELECT account, units(sum(position)) as Balance, convert(sum(position), 'GBP') as Converted
           WHERE account ~ 'CreditCards'
           GROUP BY account
           ORDER BY account",
        &directives,
    );

    // Should have 2 rows (both accounts with postings)
    assert_eq!(
        result.rows.len(),
        2,
        "Should return both accounts with transactions"
    );
    assert_eq!(result.columns, vec!["account", "Balance", "Converted"]);

    // First row: WithBalance account (alphabetically comes before ZeroBalance)
    match &result.rows[0][2] {
        Value::Amount(a) => {
            // -100 EUR * 0.85 = -85 GBP
            assert_eq!(
                a.number,
                dec!(-85),
                "convert(sum(position), 'GBP') should convert EUR to GBP"
            );
            assert_eq!(a.currency.as_ref(), "GBP");
        }
        other => panic!("Expected Amount for WithBalance converted, got {other:?}"),
    }

    // Second row: ZeroBalance account (positions cancel out)
    // convert(empty_inventory, 'GBP') should return 0.00 GBP
    match &result.rows[1][2] {
        Value::Amount(a) => {
            assert_eq!(
                a.number,
                dec!(0),
                "convert() should return 0.00 GBP for account with zero balance"
            );
            assert_eq!(a.currency.as_ref(), "GBP");
        }
        other => panic!("Expected Amount for ZeroBalance converted, got {other:?}"),
    }
}

/// Test that `convert()` falls back to original value when no price exists
#[test]
fn test_convert_no_price_fallback() {
    // Test CONVERT when no conversion price is available
    // The fallback behavior is to return the original value unchanged
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Deposit")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")))
                .with_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(dec!(-100), "USD"),
                )),
        ),
    ];

    // No USD->GBP price exists, so convert should return original value
    let result = execute_query(
        r"SELECT account, convert(sum(position), 'GBP') as converted
           WHERE account = 'Assets:Bank'
           GROUP BY account",
        &directives,
    );

    assert_eq!(
        result.rows.len(),
        1,
        "Expected exactly one row for Assets:Bank"
    );

    // Without a USD->GBP price, convert returns the original inventory unchanged
    // (this matches Python beancount fallback behavior)
    match &result.rows[0][1] {
        Value::Inventory(inv) => {
            let positions = inv.positions();
            assert_eq!(positions.len(), 1);
            assert_eq!(positions[0].units.number, dec!(100));
            assert_eq!(positions[0].units.currency.as_ref(), "USD");
        }
        Value::Amount(a) => {
            // Could also return as Amount if single currency
            assert_eq!(a.number, dec!(100));
            assert_eq!(a.currency.as_ref(), "USD");
        }
        other => panic!("Expected Inventory or Amount with original USD, got {other:?}"),
    }
}

// ============================================================================
// Issue #593 Regression Tests
// ============================================================================

/// Regression test for issue #593: BQL `cost()` returns incorrect values.
/// <https://github.com/rustledger/rustledger/issues/593>
///
/// Bug: `cost()` was using `.abs()` on unit numbers, causing sell transactions
/// to contribute positive costs instead of negative costs. This led to incorrect
/// sums when mixing buys and sells.
///
/// Expected behavior: `cost()` should preserve signs so that:
/// - Buy 5 ABC @ 1.25 EUR = +6.25 EUR
/// - Sell 5 ABC @ 1.25 EUR = -6.25 EUR (negative because units are negative)
#[test]
fn test_issue_593_cost_preserves_sign_for_sells() {
    let directives = vec![
        Directive::Open(Open::new(date(2025, 1, 1), "Equity:Stocks")),
        Directive::Open(Open::new(date(2025, 1, 1), "Assets:Bank:Checking")),
        // Buy 5 ABC at cost 1.25 EUR
        Directive::Transaction(
            Transaction::new(date(2025, 4, 1), "Buy Stocks")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(5), "ABC")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(1.25))
                            .with_currency("EUR"),
                    ),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-6.25), "EUR"),
                )),
        ),
        // Buy 7 more ABC at cost 1.30 EUR
        Directive::Transaction(
            Transaction::new(date(2025, 4, 2), "Buy more stocks")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(7), "ABC")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(1.30))
                            .with_currency("EUR"),
                    ),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-9.10), "EUR"),
                )),
        ),
        // Sell 5 ABC (the first lot)
        Directive::Transaction(
            Transaction::new(date(2025, 9, 9), "Sell complete lot")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(-5), "ABC"))
                        .with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(1.25))
                                .with_currency("EUR")
                                .with_date(date(2025, 4, 1)),
                        )
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.35), "EUR"))),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(6.75), "EUR"),
                )),
        ),
        // Sell 3 ABC (partial from second lot)
        Directive::Transaction(
            Transaction::new(date(2025, 9, 10), "Sell some stock")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(-3), "ABC"))
                        .with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(1.30))
                                .with_currency("EUR")
                                .with_date(date(2025, 4, 2)),
                        )
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.40), "EUR"))),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(4.20), "EUR"),
                )),
        ),
    ];

    // Test individual cost() values preserve sign
    let result = execute_query(
        "SELECT date, cost(position) WHERE account = 'Equity:Stocks' ORDER BY date",
        &directives,
    );

    assert_eq!(result.rows.len(), 4, "Should have 4 posting rows");

    // Buy: +5 ABC * 1.25 = +6.25 EUR
    match &result.rows[0][1] {
        Value::Amount(a) => {
            assert_eq!(a.number, dec!(6.25), "Buy cost should be positive");
            assert_eq!(a.currency.as_ref(), "EUR");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }

    // Buy: +7 ABC * 1.30 = +9.10 EUR
    match &result.rows[1][1] {
        Value::Amount(a) => {
            assert_eq!(a.number, dec!(9.10), "Buy cost should be positive");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }

    // Sell: -5 ABC * 1.25 = -6.25 EUR (BUG FIX: was +6.25 due to .abs())
    match &result.rows[2][1] {
        Value::Amount(a) => {
            assert_eq!(
                a.number,
                dec!(-6.25),
                "Sell cost should be NEGATIVE (this was the bug - it was positive due to .abs())"
            );
        }
        other => panic!("Expected Amount, got {other:?}"),
    }

    // Sell: -3 ABC * 1.30 = -3.90 EUR
    match &result.rows[3][1] {
        Value::Amount(a) => {
            assert_eq!(a.number, dec!(-3.90), "Sell cost should be NEGATIVE");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }

    // Test SUM(cost(position)) reflects net cost basis
    // Net: 6.25 + 9.10 - 6.25 - 3.90 = 5.20 EUR (4 ABC remaining at 1.30 each)
    let sum_result = execute_query(
        "SELECT SUM(cost(position)) WHERE account = 'Equity:Stocks'",
        &directives,
    );

    assert_eq!(sum_result.rows.len(), 1);
    // SUM can return either Amount or Inventory with single position
    let sum_value = match &sum_result.rows[0][0] {
        Value::Amount(a) => a.number,
        Value::Inventory(inv) => {
            let positions = inv.positions();
            assert_eq!(positions.len(), 1, "Expected single position in inventory");
            assert_eq!(positions[0].units.currency.as_ref(), "EUR");
            positions[0].units.number
        }
        other => panic!("Expected Amount or Inventory, got {other:?}"),
    };
    assert_eq!(
        sum_value,
        dec!(5.20),
        "SUM(cost(position)) should be 5.20 EUR (net cost of remaining 4 ABC at 1.30)"
    );

    // Also test cost(SUM(position)) - the actual pattern from issue #593
    // This applies cost() to an aggregated inventory, which uses a different code path
    let cost_sum_result = execute_query(
        "SELECT cost(SUM(position)) WHERE account = 'Equity:Stocks'",
        &directives,
    );

    assert_eq!(cost_sum_result.rows.len(), 1);
    let cost_sum_value = match &cost_sum_result.rows[0][0] {
        Value::Amount(a) => a.number,
        Value::Inventory(inv) => {
            let positions = inv.positions();
            assert_eq!(positions.len(), 1, "Expected single position in inventory");
            assert_eq!(positions[0].units.currency.as_ref(), "EUR");
            positions[0].units.number
        }
        other => panic!("Expected Amount or Inventory, got {other:?}"),
    };
    assert_eq!(
        cost_sum_value,
        dec!(5.20),
        "cost(SUM(position)) should be 5.20 EUR - this is the issue #593 pattern"
    );
}

/// Test that `value()` uses the latest implicit price from @ annotations.
/// This is related to issue #593 where `value()` wasn't finding the latest price.
#[test]
fn test_issue_593_value_uses_latest_implicit_price() {
    let directives = vec![
        Directive::Open(Open::new(date(2025, 1, 1), "Equity:Stocks")),
        Directive::Open(Open::new(date(2025, 1, 1), "Assets:Bank:Checking")),
        // Buy 5 ABC at cost 1.25 EUR
        Directive::Transaction(
            Transaction::new(date(2025, 4, 1), "Buy Stocks")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(5), "ABC")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(1.25))
                            .with_currency("EUR"),
                    ),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-6.25), "EUR"),
                )),
        ),
        // Buy 7 more ABC at cost 1.30 EUR
        Directive::Transaction(
            Transaction::new(date(2025, 4, 2), "Buy more stocks")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(7), "ABC")).with_cost(
                        CostSpec::empty()
                            .with_number_per(dec!(1.30))
                            .with_currency("EUR"),
                    ),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(-9.10), "EUR"),
                )),
        ),
        // Sell with @ 1.35 EUR (creates implicit price for ABC)
        Directive::Transaction(
            Transaction::new(date(2025, 9, 9), "Sell at 1.35")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(-5), "ABC"))
                        .with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(1.25))
                                .with_currency("EUR")
                                .with_date(date(2025, 4, 1)),
                        )
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.35), "EUR"))),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(6.75), "EUR"),
                )),
        ),
        // Sell with @ 1.40 EUR (creates NEWER implicit price for ABC)
        Directive::Transaction(
            Transaction::new(date(2025, 9, 10), "Sell at 1.40")
                .with_posting(
                    Posting::new("Equity:Stocks", Amount::new(dec!(-3), "ABC"))
                        .with_cost(
                            CostSpec::empty()
                                .with_number_per(dec!(1.30))
                                .with_currency("EUR")
                                .with_date(date(2025, 4, 2)),
                        )
                        .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.40), "EUR"))),
                )
                .with_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec!(4.20), "EUR"),
                )),
        ),
    ];

    // Value of the sell positions should use the latest price (1.40)
    // For the sell postings (negative units), value should be:
    // -5 ABC * 1.40 = -7.00 EUR
    // -3 ABC * 1.40 = -4.20 EUR
    let result = execute_query(
        "SELECT date, value(position, 'EUR') WHERE account = 'Equity:Stocks' AND number < 0 ORDER BY date",
        &directives,
    );

    assert_eq!(result.rows.len(), 2, "Should have 2 sell transactions");

    // First sell: -5 ABC * 1.40 (latest price) = -7.00 EUR
    match &result.rows[0][1] {
        Value::Amount(a) => {
            assert_eq!(
                a.number,
                dec!(-7.00),
                "value(-5 ABC) should use latest price 1.40, giving -7.00 EUR"
            );
            assert_eq!(a.currency.as_ref(), "EUR");
        }
        other => panic!("Expected Amount, got {other:?}"),
    }

    // Second sell: -3 ABC * 1.40 = -4.20 EUR
    match &result.rows[1][1] {
        Value::Amount(a) => {
            assert_eq!(
                a.number,
                dec!(-4.20),
                "value(-3 ABC) should use latest price 1.40, giving -4.20 EUR"
            );
        }
        other => panic!("Expected Amount, got {other:?}"),
    }

    // Net value using SUM: all positions valued at latest price (1.40)
    // Buy transactions before prices exist - they should still be valued at latest
    // 5 ABC + 7 ABC - 5 ABC - 3 ABC = 4 ABC remaining
    // 4 ABC * 1.40 = 5.60 EUR
    let sum_result = execute_query(
        "SELECT SUM(value(position, 'EUR')) WHERE account = 'Equity:Stocks'",
        &directives,
    );

    assert_eq!(sum_result.rows.len(), 1);
    // SUM can return either Amount or Inventory with single position
    let sum_value = match &sum_result.rows[0][0] {
        Value::Amount(a) => a.number,
        Value::Inventory(inv) => {
            let positions = inv.positions();
            assert_eq!(positions.len(), 1, "Expected single position in inventory");
            assert_eq!(positions[0].units.currency.as_ref(), "EUR");
            positions[0].units.number
        }
        other => panic!("Expected Amount or Inventory, got {other:?}"),
    };
    assert_eq!(
        sum_value,
        dec!(5.60),
        "SUM(value(position)) should be 5.60 EUR (4 ABC * 1.40 latest price)"
    );
}

// ============================================================================
// Issue #632: Beancount-compatible table name aliases
// ============================================================================

// Regression test for issue #632: System tables should work without # prefix
// for Python beancount compatibility.
// https://github.com/rustledger/rustledger/issues/632

#[test]
fn test_issue_632_table_aliases_without_hash_prefix() {
    let directives = make_test_directives();

    // Test all system tables with and without # prefix
    let tables_to_test = [
        ("transactions", "#transactions"),
        ("entries", "#entries"),
        ("postings", "#postings"),
        ("prices", "#prices"),
        ("balances", "#balances"),
        ("accounts", "#accounts"),
        ("events", "#events"),
        ("notes", "#notes"),
        ("documents", "#documents"),
        ("commodities", "#commodities"),
    ];

    for (alias, canonical) in tables_to_test {
        // Compare schema and row counts between alias and canonical form
        let query_alias = format!("SELECT * FROM {alias}");
        let query_canonical = format!("SELECT * FROM {canonical}");

        let result_alias = execute_query(&query_alias, &directives);
        let result_canonical = execute_query(&query_canonical, &directives);

        assert_eq!(
            result_alias.columns, result_canonical.columns,
            "Columns should match for '{alias}' vs '{canonical}'"
        );
        assert_eq!(
            result_alias.rows.len(),
            result_canonical.rows.len(),
            "Row count should match for '{alias}' vs '{canonical}'"
        );
    }
}

#[test]
fn test_issue_632_user_table_takes_precedence_over_alias() {
    let directives = make_test_directives();
    let mut executor = Executor::new(&directives);

    // Create a user table named "balances" (same name as system table alias)
    let create_query = parse("CREATE TABLE balances (name, value)").expect("should parse");
    executor.execute(&create_query).expect("should execute");

    // Insert into user table
    let insert_query = parse("INSERT INTO balances VALUES ('test', 123)").expect("should parse");
    executor.execute(&insert_query).expect("should execute");

    // SELECT FROM balances should use the user table, not #balances system table
    let select_query = parse("SELECT * FROM balances").expect("should parse");
    let result = executor.execute(&select_query).expect("should execute");

    // User table has columns "name" and "value"
    assert_eq!(result.columns, vec!["name", "value"]);
    assert_eq!(result.rows.len(), 1);

    // System table #balances has different columns (date, account, ...)
    // This proves the user table took precedence
    if let Value::String(name) = &result.rows[0][0] {
        assert_eq!(name, "test");
    } else {
        panic!("Expected String value for name column");
    }
}

#[test]
fn test_order_by_expression_not_in_select() {
    // Issue #684: ORDER BY on an expression not in SELECT should work
    // by adding a hidden column for sorting, then stripping it from output.
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Lunch")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 20), "Pay")
                .with_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(dec!(-1000), "USD"),
                ))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(1000), "USD"))),
        ),
    ];

    // ORDER BY account_sortkey(account) — not in SELECT
    let result = execute_query(
        "SELECT account FROM #postings ORDER BY account_sortkey(account)",
        &directives,
    );

    // Should succeed without error
    assert!(!result.rows.is_empty(), "should return rows");

    // Result should only have 1 column (account), not the hidden sortkey
    assert_eq!(result.columns.len(), 1, "hidden column should be stripped");
    assert_eq!(result.columns[0], "account");

    // Accounts should be sorted by type: Assets(0) < Income(3) < Expenses(4)
    // account_sortkey produces "0-Assets:Cash", "3-Income:Salary", "4-Expenses:Food"
    let accounts: Vec<&str> = result
        .rows
        .iter()
        .filter_map(|r| match &r[0] {
            Value::String(s) => Some(s.as_str()),
            _ => None,
        })
        .collect();

    let first_assets = accounts
        .iter()
        .position(|a| a.starts_with("Assets"))
        .expect("expected an Assets account in query results");
    let first_expenses = accounts
        .iter()
        .position(|a| a.starts_with("Expenses"))
        .expect("expected an Expenses account in query results");
    let first_income = accounts
        .iter()
        .position(|a| a.starts_with("Income"))
        .expect("expected an Income account in query results");
    assert!(
        first_assets < first_income && first_income < first_expenses,
        "accounts should be sorted by type via account_sortkey: got {accounts:?}"
    );
}

#[test]
fn test_order_by_function_not_in_select_simple() {
    // Simpler case: ORDER BY length(account) — function not in SELECT
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:FoodAndDrink")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "t1")
                .with_posting(Posting::new(
                    "Expenses:FoodAndDrink",
                    Amount::new(dec!(10), "USD"),
                ))
                .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT account FROM #postings ORDER BY length(account)",
        &directives,
    );

    assert!(!result.rows.is_empty());
    assert_eq!(result.columns.len(), 1, "hidden column should be stripped");

    // Verify rows are actually sorted by length
    let accounts: Vec<&str> = result
        .rows
        .iter()
        .filter_map(|r| match &r[0] {
            Value::String(s) => Some(s.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        accounts
            .windows(2)
            .all(|pair| pair[0].len() <= pair[1].len()),
        "accounts should be sorted by ascending length: got {accounts:?}"
    );
}

#[test]
fn test_open_date_from_postings_table() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 2, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 15), "Lunch")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-10), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT DISTINCT account, open_date(account) FROM #postings ORDER BY account",
        &directives,
    );

    assert_eq!(result.rows.len(), 2);
    assert_eq!(result.rows[0][1], Value::Date(date(2024, 1, 1)));
    assert_eq!(result.rows[1][1], Value::Date(date(2024, 2, 1)));
}

#[test]
fn test_close_date_from_postings_table() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Old")),
        Directive::Close(Close::new(date(2024, 6, 30), "Assets:Old")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 15), "Lunch")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Old", Amount::new(dec!(-10), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT DISTINCT account, close_date(account) FROM #postings ORDER BY account",
        &directives,
    );

    assert_eq!(result.rows.len(), 2);
    assert_eq!(result.rows[0][1], Value::Date(date(2024, 6, 30)));
    assert_eq!(result.rows[1][1], Value::Null);
}

#[test]
fn test_grep_with_null_narration() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 15), "Salary Payment")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(1000), "USD")))
                .with_posting(Posting::auto("Income:Salary")),
        ),
    ];

    let result = execute_query(
        "SELECT type, narration FROM #entries WHERE grep('Salary', narration) IS NOT NULL",
        &directives,
    );

    assert_eq!(result.rows.len(), 1);
    if let Value::String(narration) = &result.rows[0][1] {
        assert!(narration.contains("Salary"));
    }
}

/// Regression for issue #738: `grep(pattern, text)` returns the matched
/// substring or NULL, and must be usable directly in a `WHERE` clause via
/// SQL/beanquery truthiness. Previously failed with "expected boolean".
#[test]
fn test_grep_in_where_clause_truthy() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Coffee")),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 15), "Salary Payment")
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(1000), "USD")))
                .with_posting(Posting::auto("Income:Salary")),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 16), "Coffee shop")
                .with_posting(Posting::new("Expenses:Coffee", Amount::new(dec!(5), "USD")))
                .with_posting(Posting::auto("Assets:Bank")),
        ),
    ];

    // The bare grep() call in WHERE must filter to the matching narration.
    let result = execute_query(
        "SELECT narration FROM #entries WHERE grep('Salary', narration)",
        &directives,
    );

    assert_eq!(
        result.rows.len(),
        1,
        "expected only the Salary transaction, got rows: {:?}",
        result.rows
    );
    if let Value::String(narration) = &result.rows[0][0] {
        assert!(narration.contains("Salary"), "got narration: {narration}");
    } else {
        panic!("expected String narration, got {:?}", result.rows[0][0]);
    }
}

#[test]
fn test_open_meta_from_postings_table() {
    let mut open = Open::new(date(2024, 1, 1), "Assets:Bank");
    open.meta.insert(
        "institution".to_string(),
        rustledger_core::MetaValue::String("Chase".to_string()),
    );

    let directives = vec![
        Directive::Open(open),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 3, 15), "Lunch")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-10), "USD"))),
        ),
    ];

    let result = execute_query(
        "SELECT DISTINCT account, open_meta(account, 'institution') FROM #postings ORDER BY account",
        &directives,
    );

    assert_eq!(result.rows.len(), 2);
    // Assets:Bank has institution metadata
    assert_eq!(result.rows[0][1], Value::String("Chase".to_string()));
    // Expenses:Food has no institution metadata
    assert_eq!(result.rows[1][1], Value::Null);
}

#[test]
fn test_entry_meta_from_postings_table() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction({
            let mut txn = Transaction::new(date(2024, 3, 15), "Lunch");
            txn.meta.insert(
                "category".to_string(),
                rustledger_core::MetaValue::String("dining".to_string()),
            );
            txn.postings = vec![
                Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")),
                Posting::new("Assets:Bank", Amount::new(dec!(-10), "USD")),
            ];
            txn
        }),
    ];

    let result = execute_query(
        "SELECT account, entry_meta('category') FROM #postings",
        &directives,
    );

    assert_eq!(result.rows.len(), 2);
    assert_eq!(result.rows[0][1], Value::String("dining".to_string()));
    assert_eq!(result.rows[1][1], Value::String("dining".to_string()));
}

#[test]
fn test_entry_meta_from_entries_table() {
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Transaction({
            let mut txn = Transaction::new(date(2024, 3, 15), "Paycheck");
            txn.meta.insert(
                "source".to_string(),
                rustledger_core::MetaValue::String("employer".to_string()),
            );
            txn.postings = vec![
                Posting::new("Assets:Bank", Amount::new(dec!(1000), "USD")),
                Posting::auto("Income:Salary"),
            ];
            txn
        }),
    ];

    let result = execute_query(
        "SELECT type, entry_meta('source') FROM #entries WHERE type = 'transaction'",
        &directives,
    );

    assert_eq!(result.rows.len(), 1);
    assert_eq!(result.rows[0][1], Value::String("employer".to_string()));
}

// ============================================================================
// Empty-group literal evaluation (issue #902)
// ============================================================================

#[test]
fn test_convert_sum_with_literal_currency_on_empty_where() {
    // Reporter's exact query. Before the fix, this errored with
    // `CONVERT: second argument must be a currency string` — because the
    // 'USD' literal was being replaced with Null when the group was empty.
    let result = execute_query(
        "SELECT convert(sum(position), 'USD') WHERE account ~ '^Income'",
        &[],
    );
    assert_eq!(result.len(), 1);
    // CONVERT on an empty/null sum returns zero in the target currency.
    match &result.rows[0][0] {
        Value::Amount(a) => {
            assert_eq!(a.number, dec!(0));
            assert_eq!(a.currency.as_ref(), "USD");
        }
        other => panic!("expected Amount(0 USD), got {other:?}"),
    }
}

#[test]
fn test_value_sum_with_literal_date_on_empty_where() {
    // Parallel to the CONVERT test: `VALUE(sum(position), DATE)` on an
    // empty group must not silently replace the DATE literal with Null.
    // Before the fix, the same bug would make VALUE's dispatch reject the
    // 2nd argument with a misleading error about "date or currency string".
    let result = execute_query(
        "SELECT value(sum(position), 2020-06-01) WHERE account ~ '^Nothing'",
        &[],
    );
    assert_eq!(result.len(), 1);
    // With no postings to sum, the result should be Null (inventory couldn't
    // produce an amount) — NOT an error about the second argument.
    assert!(
        matches!(
            &result.rows[0][0],
            Value::Null | Value::Amount(_) | Value::Inventory(_)
        ),
        "expected Null or empty Amount/Inventory, got {:?}",
        result.rows[0][0]
    );
}

#[test]
fn test_convert_with_null_second_arg_has_helpful_error_message() {
    // Even with our aggregation fix, it is still possible to write a query
    // where the second argument legitimately evaluates to Null at runtime
    // (e.g. via a metadata lookup with no matching key). In that case the
    // error message should mention NULL explicitly instead of claiming the
    // user's input wasn't a string.
    let directives = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 15), "Lunch")
                .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-10), "USD"))),
        ),
    ];
    let query = parse("SELECT convert(position, meta('nonexistent_key'))").expect("should parse");
    let mut executor = Executor::new(&directives);
    let err = executor
        .execute(&query)
        .expect_err("CONVERT with NULL second arg should error");
    let msg = format!("{err}");
    assert!(
        msg.contains("NULL") && msg.contains("currency string"),
        "error should explicitly mention NULL + what was expected, got: {msg}"
    );
}
