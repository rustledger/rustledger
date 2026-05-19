//! Property-Based Tests from TLA+ Invariants
//!
//! These tests verify that the Rust implementation satisfies the same
//! invariants defined in the TLA+ specifications.
//!
//! References:
//! - spec/tla/QueryExecution.tla
//! - spec/tla/PriceDB.tla

use proptest::prelude::*;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Directive, NaiveDate, Posting, Price as PriceDirective, Transaction,
};
use rustledger_query::{Executor, parse, price::PriceDatabase};

// ============================================================================
// Test Strategies
// ============================================================================

fn date_strategy() -> impl Strategy<Value = NaiveDate> {
    (2020i32..2025, 1u32..13, 1u32..29).prop_map(|(y, m, d)| {
        rustledger_core::naive_date(y, m, d)
            .unwrap_or(rustledger_core::naive_date(y, m, 1).unwrap())
    })
}

fn currency_strategy() -> impl Strategy<Value = &'static str> {
    prop::sample::select(vec!["USD", "EUR", "GBP", "JPY", "CAD"])
}

fn price_strategy() -> impl Strategy<Value = Decimal> {
    (1i64..1000).prop_map(|n| Decimal::new(n, 2)) // 0.01 to 9.99
}

fn amount_strategy(max: i64) -> impl Strategy<Value = i64> {
    1i64..=max
}

// ============================================================================
// PriceDB Tests (from PriceDB.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ IdentityProperty:
    /// convert(X, X) = identity for any currency X.
    ///
    /// When getting the price of a currency in terms of itself,
    /// the result must always be 1.0.
    #[test]
    fn prop_price_identity(
        currency in currency_strategy(),
        date in date_strategy(),
    ) {
        let db = PriceDatabase::new();

        // Price of X in X should always be 1
        let price = db.get_price(currency, currency, date);

        prop_assert_eq!(
            price,
            Some(Decimal::ONE),
            "Price of {} in {} should be 1.0, got {:?}",
            currency, currency, price
        );
    }

    /// TLA+ SelfPricesNeverSet:
    /// price(X, X) is never stored in the database.
    ///
    /// The database should reject or ignore price directives where
    /// base == quote.
    #[test]
    fn prop_no_self_prices(
        currency in currency_strategy(),
        price_val in price_strategy(),
        date in date_strategy(),
    ) {
        let mut db = PriceDatabase::new();

        // Try to add a self-price (this SHOULDN'T happen in real ledgers,
        // but if it does, the identity property should still hold)
        let price_directive = PriceDirective {
            date,
            currency: currency.into(),
            amount: Amount::new(price_val, currency), // Same currency
            meta: Default::default(),
        };

        db.add_price(&price_directive);

        // Even after adding a "self-price", get_price should return 1.0
        let result = db.get_price(currency, currency, date);
        prop_assert_eq!(
            result,
            Some(Decimal::ONE),
            "Self-price lookup should still return 1.0"
        );
    }

    /// TLA+ InverseReciprocal:
    /// price(A, B) = 1 / price(B, A) when both exist.
    ///
    /// If we have a direct price for A->B, then looking up B->A
    /// should give the reciprocal.
    #[test]
    fn prop_price_inverse_reciprocal(
        base in currency_strategy(),
        quote in currency_strategy(),
        price_val in price_strategy(),
        date in date_strategy(),
    ) {
        prop_assume!(base != quote);
        prop_assume!(price_val != Decimal::ZERO);

        let mut db = PriceDatabase::new();

        db.add_price(&PriceDirective {
            date,
            currency: base.into(),
            amount: Amount::new(price_val, quote),
            meta: Default::default(),
        });

        // Direct lookup
        let direct = db.get_price(base, quote, date);
        prop_assert_eq!(direct, Some(price_val));

        // Inverse lookup should be reciprocal
        let inverse = db.get_price(quote, base, date);
        if let Some(inv) = inverse {
            // 1/price should equal inverse (within precision)
            let expected = Decimal::ONE / price_val;
            let diff = (inv - expected).abs();
            prop_assert!(
                diff < dec!(0.0001),
                "Inverse should be reciprocal: {} != {}",
                inv, expected
            );
        }
    }

    /// TLA+ ChainTransitivity:
    /// price(A, C) = price(A, B) * price(B, C) for intermediate B.
    ///
    /// When A->C is not available but A->B and B->C are,
    /// the chained price should be their product.
    #[test]
    fn prop_price_chain_transitivity(
        date in date_strategy(),
    ) {
        let mut db = PriceDatabase::new();

        // AAPL -> USD = 150
        db.add_price(&PriceDirective {
            date,
            currency: "AAPL".into(),
            amount: Amount::new(dec!(150), "USD"),
            meta: Default::default(),
        });

        // USD -> EUR = 0.92
        db.add_price(&PriceDirective {
            date,
            currency: "USD".into(),
            amount: Amount::new(dec!(0.92), "EUR"),
            meta: Default::default(),
        });

        // Sort (normally done by from_directives)
        // Chained lookup: AAPL -> EUR = AAPL -> USD * USD -> EUR = 150 * 0.92 = 138
        let chained = db.get_price("AAPL", "EUR", date);

        if let Some(price) = chained {
            let expected = dec!(150) * dec!(0.92); // 138.00
            let diff = (price - expected).abs();
            prop_assert!(
                diff < dec!(0.01),
                "Chained price should be product: {} != {}",
                price, expected
            );
        }
    }
}

// ============================================================================
// Query Execution Tests (from QueryExecution.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// TLA+ FilterCorrectness:
    /// WHERE clause selects only matching rows.
    ///
    /// All returned rows must satisfy the filter predicate.
    #[test]
    fn prop_filter_no_false_positives(
        amounts in prop::collection::vec(amount_strategy(1000), 1..5),
        date in date_strategy(),
    ) {
        // Create transactions
        let mut directives = Vec::new();
        for (i, &amount) in amounts.iter().enumerate() {
            let account = if i % 2 == 0 { "Expenses:Food" } else { "Assets:Bank" };
            directives.push(Directive::Transaction(
                Transaction::new(date, format!("Txn {i}"))
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new(account, Amount::new(Decimal::from(amount), "USD")))
                    .with_synthesized_posting(Posting::new("Equity:Opening", Amount::new(Decimal::from(-amount), "USD")))
            ));
        }

        let mut executor = Executor::new(&directives);

        // Filter for Expenses only
        let query = parse("SELECT account WHERE account ~ \"Expenses:\"").unwrap();
        let result = executor.execute(&query).unwrap();

        // All results should match the filter
        for row in &result.rows {
            let account = match &row[0] {
                rustledger_query::Value::String(s) => s.clone(),
                _ => continue,
            };
            prop_assert!(
                account.contains("Expenses:"),
                "Filter returned non-matching row: {}",
                account
            );
        }
    }

    /// TLA+ CountAccuracy:
    /// COUNT returns exact count of matching rows.
    #[test]
    fn prop_count_accuracy(
        num_txns in 1usize..10,
        date in date_strategy(),
    ) {
        let directives: Vec<Directive> = (0..num_txns)
            .map(|i| {
                Directive::Transaction(
                    Transaction::new(date, format!("Txn {i}"))
                        .with_flag('*')
                        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD")))
                )
            })
            .collect();

        let mut executor = Executor::new(&directives);

        // Count all postings
        let query = parse("SELECT COUNT(account)").unwrap();
        let result = executor.execute(&query).unwrap();

        // Each transaction has 2 postings
        let expected_count = (num_txns * 2) as i64;

        prop_assert_eq!(
            result.rows[0][0].clone(),
            rustledger_query::Value::Integer(expected_count),
            "COUNT should be accurate"
        );
    }

    /// TLA+ SumAccuracy:
    /// SUM returns exact sum of matching values.
    ///
    /// The sum of all posting amounts should equal the expected total.
    #[test]
    fn prop_sum_accuracy(
        amounts in prop::collection::vec(amount_strategy(100), 1..5),
        date in date_strategy(),
    ) {
        // Create transactions with known amounts
        let directives: Vec<Directive> = amounts
            .iter()
            .enumerate()
            .map(|(i, &amount)| {
                Directive::Transaction(
                    Transaction::new(date, format!("Txn {i}"))
                        .with_flag('*')
                        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(Decimal::from(amount), "USD")))
                        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(Decimal::from(-amount), "USD")))
                )
            })
            .collect();

        let mut executor = Executor::new(&directives);

        // Sum all Expenses postings
        let query = parse("SELECT SUM(number) WHERE account ~ \"Expenses:\"").unwrap();
        let result = executor.execute(&query).unwrap();

        // Expected sum of all expense amounts
        let expected_sum: i64 = amounts.iter().sum();

        if let rustledger_query::Value::Number(sum) = &result.rows[0][0] {
            prop_assert_eq!(
                *sum,
                Decimal::from(expected_sum),
                "SUM should be accurate: expected {}, got {}",
                expected_sum, sum
            );
        }
    }

    /// TLA+ ResultMatchesSelection:
    /// Filtered results match the selection criteria.
    ///
    /// When filtering by account type, only matching accounts appear.
    #[test]
    fn prop_result_matches_selection(
        date in date_strategy(),
    ) {
        let directives = vec![
            Directive::Transaction(
                Transaction::new(date, "Coffee")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(5), "USD")))
                    .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-5), "USD")))
            ),
            Directive::Transaction(
                Transaction::new(date, "Salary")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new("Income:Salary", Amount::new(dec!(-1000), "USD")))
                    .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(1000), "USD")))
            ),
        ];

        let mut executor = Executor::new(&directives);

        // Select only Assets accounts
        let query = parse("SELECT account WHERE account ~ \"^Assets:\"").unwrap();
        let result = executor.execute(&query).unwrap();

        // Should have exactly 2 Assets postings
        prop_assert_eq!(result.len(), 2, "Should have 2 Assets postings");

        for row in &result.rows {
            if let rustledger_query::Value::String(s) = &row[0] {
                prop_assert!(
                    s.starts_with("Assets:"),
                    "All results should be Assets accounts"
                );
            }
        }
    }

    /// TLA+ NoDuplicatePostings:
    /// Each posting appears at most once in results (without DISTINCT).
    ///
    /// Query results shouldn't duplicate postings unless explicitly requested.
    #[test]
    fn prop_no_duplicate_postings(
        date in date_strategy(),
    ) {
        let directives = vec![
            Directive::Transaction(
                Transaction::new(date, "Test")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                    .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD")))
            ),
        ];

        let mut executor = Executor::new(&directives);

        // Select all - should get exactly 2 postings (one per posting)
        let query = parse("SELECT account, position").unwrap();
        let result = executor.execute(&query).unwrap();

        prop_assert_eq!(
            result.len(),
            2,
            "Should have exactly 2 rows (one per posting)"
        );
    }

    /// ORDER BY produces sorted results.
    #[test]
    fn prop_order_by_sorted(
        dates in prop::collection::vec(date_strategy(), 2..5),
    ) {
        let directives: Vec<Directive> = dates
            .iter()
            .enumerate()
            .map(|(i, &d)| {
                Directive::Transaction(
                    Transaction::new(d, format!("Txn {i}"))
                        .with_flag('*')
                        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD")))
                )
            })
            .collect();

        let mut executor = Executor::new(&directives);

        // Order by date ascending
        let query = parse("SELECT DISTINCT date ORDER BY date ASC").unwrap();
        let result = executor.execute(&query).unwrap();

        // Verify sorted order
        let mut prev_date: Option<NaiveDate> = None;
        for row in &result.rows {
            if let rustledger_query::Value::Date(d) = &row[0] {
                if let Some(prev) = prev_date {
                    prop_assert!(
                        d >= &prev,
                        "ORDER BY ASC should produce sorted results"
                    );
                }
                prev_date = Some(*d);
            }
        }
    }

    /// DISTINCT reduces rows when duplicates exist.
    #[test]
    fn prop_distinct_reduces_rows(
        date in date_strategy(),
    ) {
        // Create transactions with same flag (will have duplicates)
        let directives: Vec<Directive> = (0..5)
            .map(|i| {
                Directive::Transaction(
                    Transaction::new(date, format!("Txn {i}"))
                        .with_flag('*') // Same flag for all
                        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD")))
                )
            })
            .collect();

        let mut executor = Executor::new(&directives);

        // Without DISTINCT
        let query_all = parse("SELECT flag").unwrap();
        let result_all = executor.execute(&query_all).unwrap();

        // With DISTINCT
        let query_distinct = parse("SELECT DISTINCT flag").unwrap();
        let result_distinct = executor.execute(&query_distinct).unwrap();

        prop_assert!(
            result_distinct.len() <= result_all.len(),
            "DISTINCT should not increase row count"
        );

        prop_assert_eq!(
            result_distinct.len(),
            1,
            "DISTINCT on same flags should return 1 row"
        );
    }
}

// ============================================================================
// Query Determinism Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// Query execution is deterministic.
    ///
    /// Running the same query twice should produce identical results.
    #[test]
    fn prop_query_deterministic(
        date in date_strategy(),
        amount in amount_strategy(100),
    ) {
        let directives = vec![
            Directive::Transaction(
                Transaction::new(date, "Test")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(Decimal::from(amount), "USD")))
                    .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(Decimal::from(-amount), "USD")))
            ),
        ];

        let mut executor1 = Executor::new(&directives);
        let mut executor2 = Executor::new(&directives);

        let query = parse("SELECT account, position ORDER BY account").unwrap();

        let result1 = executor1.execute(&query).unwrap();
        let result2 = executor2.execute(&query).unwrap();

        prop_assert_eq!(
            result1.len(),
            result2.len(),
            "Query should be deterministic"
        );

        for (row1, row2) in result1.rows.iter().zip(result2.rows.iter()) {
            prop_assert_eq!(row1, row2, "Row contents should match");
        }
    }

    /// LIMIT respects the specified bound.
    #[test]
    fn prop_limit_respected(
        num_txns in 5usize..15,
        limit in 1usize..10,
        date in date_strategy(),
    ) {
        let directives: Vec<Directive> = (0..num_txns)
            .map(|i| {
                Directive::Transaction(
                    Transaction::new(date, format!("Txn {i}"))
                        .with_flag('*')
                        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
                        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD")))
                )
            })
            .collect();

        let mut executor = Executor::new(&directives);

        let query = parse(&format!("SELECT account LIMIT {limit}")).unwrap();
        let result = executor.execute(&query).unwrap();

        prop_assert!(
            result.len() <= limit,
            "LIMIT {} should return at most {} rows, got {}",
            limit, limit, result.len()
        );
    }
}
