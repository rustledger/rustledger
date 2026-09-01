//! Regression: a comparison with a NULL operand yields NULL, not FALSE (#2213).
//!
//! The two are not interchangeable. `COUNT(expr)` skips NULLs but counts every
//! FALSE, so `count(payee != '')` over payee-less rows answered 4 where
//! bean-query answers 0. Measured against beanquery 0.2.0 / beancount 3.2.3.
//!
//! The target is Python's rule, not strict SQL three-valued logic: beanquery
//! evaluates `NOT (NULL)` as `TRUE` (Python's `not None`), where SQL would say
//! NULL. `not_coerces_a_null_operand` pins that deliberately, so a later
//! "make it proper 3VL" change has to meet the decision rather than assume the
//! current answer is an oversight.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// Two postings with a payee, two without.
fn mixed_payees() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "with payee")
                .with_payee("Cafe")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-5), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(5), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 3), "no payee")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-7), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(7), "USD"),
                )),
        ),
    ]
}

fn column(query_str: &str, directives: &[Directive]) -> Vec<Value> {
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(directives);
    let result = executor.execute(&query).expect("query should execute");
    result
        .rows
        .iter()
        .map(|row| row.first().cloned().expect("one column"))
        .collect()
}

/// Every comparison operator, on the same NULL operand. Checking one of them
/// would leave the other five free to regress independently -- the bug was
/// uniform across all six precisely because they share a single guard.
#[test]
fn every_comparison_with_a_null_operand_is_null() {
    let dirs = mixed_payees();
    for op in ["=", "!=", "<", "<=", ">", ">="] {
        let values = column(&format!("SELECT payee {op} 'Cafe'"), &dirs);
        assert_eq!(values.len(), 4, "all four postings are returned");

        let nulls = values.iter().filter(|v| **v == Value::Null).count();
        assert_eq!(
            nulls, 2,
            "`payee {op} 'Cafe'` must be NULL on the two payee-less postings, \
             got {values:?}",
        );
        // The other two rows have a payee, so they must still be plain
        // booleans -- returning NULL unconditionally would satisfy the count
        // above on its own.
        let booleans = values
            .iter()
            .filter(|v| matches!(v, Value::Boolean(_)))
            .count();
        assert_eq!(
            booleans, 2,
            "`payee {op} 'Cafe'` must stay boolean where the payee is present, \
             got {values:?}",
        );
    }
}

/// The reason the distinction matters: `COUNT` skips NULL and counts FALSE.
#[test]
fn count_over_a_null_comparison_skips_the_null_rows() {
    let dirs = mixed_payees();
    let counted = column("SELECT count(payee != 'Nobody')", &dirs);
    assert_eq!(
        counted,
        vec![Value::Integer(2)],
        "only the two postings with a payee produce a non-NULL comparison",
    );
}

/// A NULL comparison is falsy, so `WHERE` still drops the row. This is what
/// made the FALSE answer survive so long: filtering looked correct, and only
/// projecting or counting the comparison exposed it.
#[test]
fn where_still_drops_rows_whose_comparison_is_null() {
    let dirs = mixed_payees();
    let kept = column("SELECT account WHERE payee != 'Nobody'", &dirs);
    assert_eq!(
        kept.len(),
        2,
        "payee-less postings are filtered out: {kept:?}"
    );
}

/// The ordinary case must be untouched: with both operands present, a
/// comparison is still a plain boolean. Without this, returning NULL
/// unconditionally would pass every other test in this file.
#[test]
fn a_comparison_between_two_present_values_is_unchanged() {
    let dirs = mixed_payees();
    let values = column("SELECT payee = 'Cafe' WHERE payee IS NOT NULL", &dirs);
    assert_eq!(
        values,
        vec![Value::Boolean(true), Value::Boolean(true)],
        "a comparison with no NULL operand is still TRUE/FALSE",
    );

    let negative = column("SELECT payee = 'Other' WHERE payee IS NOT NULL", &dirs);
    assert_eq!(
        negative,
        vec![Value::Boolean(false), Value::Boolean(false)],
        "and FALSE is still reachable",
    );
}

/// `NOT` coerces its operand, so `NOT (NULL)` is TRUE -- Python's rule, which
/// is what beanquery implements. Deliberate, not an oversight: see the module
/// comment. `IS NULL` is likewise unaffected, being a null test rather than a
/// comparison.
#[test]
fn not_coerces_a_null_operand() {
    let dirs = mixed_payees();
    let notted = column("SELECT NOT (payee = 'Cafe') WHERE payee IS NULL", &dirs);
    assert_eq!(
        notted,
        vec![Value::Boolean(true), Value::Boolean(true)],
        "NOT (NULL) is TRUE, matching bean-query",
    );

    let is_null = column("SELECT payee IS NULL", &dirs);
    assert_eq!(
        is_null
            .iter()
            .filter(|v| **v == Value::Boolean(true))
            .count(),
        2,
        "IS NULL is a null test, not a comparison: {is_null:?}",
    );
}
