//! Long operator chains get the same "nesting too deep" parse error as deeply
//! nested brackets, instead of building a tree too deep to walk.
//!
//! A chain of N binary operators (`a AND b AND ...`, `1 + 1 + ...`) or N
//! stacked `NOT`s is an expression tree N levels deep, and planning,
//! evaluating, naming and dropping it each recurse once per level. The parser
//! refuses a query whose operators and brackets could nest more than 1,000
//! levels (`MAX_EXPR_DEPTH` in `parser.rs`). These tests straddle that limit
//! for each shape, run the queries at the limit to completion, and check that
//! a chain hundreds of times past it is refused on a small stack.
//!
//! The runs at the limit use an 8 MiB thread, the main thread's usual stack:
//! this crate's tests build unoptimized, where each level of the tree takes
//! about 3.5 KiB of stack (a 2 MiB thread holds 500 to 600 levels), several
//! times what an optimized build takes. See `MAX_EXPR_DEPTH` for the
//! optimized measurements the limit is sized by.

use rustledger_core::Directive;
use rustledger_query::{Executor, QueryResult, parse};

/// The limit `parser.rs` enforces, as the counting rule there describes it.
const LIMIT: usize = 1000;

const LEDGER: &str = "
2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
";

fn directives() -> Vec<Directive> {
    rustledger_parser::parse(LEDGER)
        .directives
        .iter()
        .map(|d| (**d).clone())
        .collect()
}

/// Run `f` on a thread with `stack` bytes of stack, so a test means the
/// same on every machine (the main and test threads' stacks differ).
fn on_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(stack)
            .spawn_scoped(scope, f)
            .expect("spawn test thread")
            .join()
            .expect("test thread panicked")
    })
}

/// Parse and run `bql` on an 8 MiB thread.
fn run(bql: &str) -> QueryResult {
    on_stack(8 * 1024 * 1024, || {
        let directives = directives();
        let query = parse(bql).unwrap_or_else(|e| panic!("{e}"));
        Executor::new(&directives)
            .execute(&query)
            .unwrap_or_else(|e| panic!("{e}"))
    })
}

fn assert_too_deep(bql: &str) {
    let err = parse(bql).expect_err("a chain past the limit must be refused");
    assert!(
        err.to_string().contains("nesting too deep"),
        "expected the nesting error, got: {err}"
    );
}

/// Each shape, by the length that brings it exactly to the limit, and the
/// query of a given length. The counts follow `scan_delimiters`: one per
/// operator token, so a comparison joined by `AND` costs two.
fn shapes() -> Vec<(&'static str, usize, fn(usize) -> String)> {
    vec![
        ("+", LIMIT, |n| format!("SELECT 1{}", " + 1".repeat(n))),
        ("AND", LIMIT, |n| {
            format!("SELECT TRUE{}", " AND TRUE".repeat(n))
        }),
        ("OR", LIMIT, |n| {
            format!("SELECT FALSE{}", " OR FALSE".repeat(n))
        }),
        ("NOT", LIMIT, |n| format!("SELECT {}TRUE", "NOT ".repeat(n))),
        ("mixed * and -", LIMIT / 2, |n| {
            format!("SELECT 1{}", " * 2 - 1".repeat(n))
        }),
        // One `=` plus `AND 1 = 1` at two apiece: 1 + 2n.
        ("= joined by AND", (LIMIT - 1) / 2, |n| {
            format!("SELECT 1 = 1{}", " AND 1 = 1".repeat(n))
        }),
        // A decimal's `.` is part of its literal, no attribute access, and
        // costs nothing.
        ("+ of decimals", LIMIT, |n| {
            format!("SELECT 1.5{}", " + 2.5".repeat(n))
        }),
        // `!=` is one operator, not `!` and `=`.
        ("!= joined by AND", (LIMIT - 1) / 2, |n| {
            format!("SELECT 1 != 2{}", " AND 1 != 2".repeat(n))
        }),
        // The generated-query shape: one `~` plus `OR account ~ ...` at two
        // apiece.
        ("~ joined by OR", (LIMIT - 1) / 2, |n| {
            format!(
                "SELECT account WHERE account ~ 'Bank'{}",
                " OR account ~ 'Nope'".repeat(n)
            )
        }),
        // A bracket holding 500 operators, then a chain after it: the
        // bracket's depth carries into the chain around it, 500 + 1 + n.
        ("bracket then chain", LIMIT - 501, |n| {
            format!("SELECT (1{}){}", " + 1".repeat(500), " + 1".repeat(n))
        }),
    ]
}

#[test]
fn test_parse_operator_chains_straddle_the_depth_limit() {
    for (name, at_limit, query) in shapes() {
        let ok = query(at_limit);
        assert!(parse(&ok).is_ok(), "{name}: {at_limit} should parse");
        assert_too_deep(&query(at_limit + 1));
    }
}

/// At the limit, every shape runs to completion, not just parses: the
/// recursive passes after the parse fit the thread at this depth.
#[test]
fn test_execute_operator_chains_at_the_depth_limit() {
    for (name, at_limit, query) in shapes() {
        let result = run(&format!("{} LIMIT 1", query(at_limit)));
        assert_eq!(result.rows.len(), 1, "{name}: {:?}", result.rows);
    }
}

#[test]
fn test_parse_attribute_chain_straddles_the_depth_limit() {
    let chain = |n: usize| format!("SELECT entry{}", ".meta".repeat(n));
    assert!(parse(&chain(LIMIT)).is_ok());
    assert_too_deep(&chain(LIMIT + 1));
}

/// The error is at the operator that passes the limit.
#[test]
fn test_parse_depth_error_names_the_operator_past_the_limit() {
    let err = parse(&format!("SELECT 1{}", " + 1".repeat(LIMIT + 5))).expect_err("too deep");
    // `SELECT 1` is 8 bytes, each ` + 1` is 4, and the `+` is the 2nd of them.
    assert_eq!(err.position, 8 + 4 * LIMIT + 1, "{err}");
    assert_eq!(
        err.to_string().matches("exceeds maximum of 1000").count(),
        1,
        "{err}"
    );
}

/// Commas separate sibling expressions, which add no depth to each other:
/// long target, argument and `IN` lists are not chains.
#[test]
fn test_parse_long_lists_are_not_chains() {
    let items = (0..5000).map(|i| i.to_string()).collect::<Vec<_>>();
    let result = run(&format!("SELECT 1 IN ({}) LIMIT 1", items.join(", ")));
    assert_eq!(result.rows.len(), 1);
    let chain = format!("1{}", " + 1".repeat(900));
    let targets = std::iter::repeat_n(chain.as_str(), 5).collect::<Vec<_>>();
    let result = run(&format!("SELECT {} LIMIT 1", targets.join(", ")));
    assert_eq!(result.columns.len(), 5);
}

/// A generated filter of a few hundred alternatives runs.
#[test]
fn test_execute_generated_or_filter_of_300_terms() {
    let terms = (0..300)
        .map(|i| format!("account ~ 'Assets:Bank{i}'"))
        .chain(["account ~ 'Assets:Bank'".to_string()])
        .collect::<Vec<_>>();
    let result = run(&format!(
        "SELECT account WHERE {} ORDER BY account",
        terms.join(" OR ")
    ));
    assert_eq!(result.rows.len(), 1, "{:?}", result.rows);
}

/// Chains hundreds of times past the limit are refused on a 256 KiB stack:
/// the check reads the text in a loop and refuses the query before any tree
/// is built, so there is nothing deep to walk or drop.
#[test]
fn test_parse_very_long_chains_refused_on_a_small_stack() {
    for query in [
        format!("SELECT 1{}", " + 1".repeat(200_000)),
        format!("SELECT TRUE{}", " AND TRUE".repeat(200_000)),
        format!("SELECT {}TRUE", "NOT ".repeat(200_000)),
        format!(
            "SELECT account WHERE account ~ 'x'{}",
            " OR account ~ 'x'".repeat(200_000)
        ),
    ] {
        let refused = on_stack(256 * 1024, || {
            parse(&query).map(|_| ()).map_err(|e| e.to_string())
        });
        let err = refused.expect_err("a 200,000-term chain must be refused");
        assert!(err.contains("nesting too deep"), "{err}");
    }
}
