//! Long operator chains get the same "nesting too deep" parse error as deeply
//! nested brackets, instead of building a tree too deep to walk.
//!
//! A chain of N binary operators (`a AND b AND ...`, `1 + 1 + ...`) or N
//! stacked `NOT`s is an expression tree N levels deep, and planning,
//! evaluating, naming and dropping it each recurse once per level. The parser
//! refuses a query whose operators and brackets could nest deeper than 720
//! levels, each bracket counting 12 (`MAX_EXPR_DEPTH` and `BRACKET_WEIGHT`
//! in `parser.rs`), or that nests more than 60 brackets
//! (`MAX_NESTING_DEPTH`). These tests straddle those limits for each shape
//! and each counted operator, run the queries at the limit to completion,
//! and check that a chain hundreds of times past it is refused on a small
//! stack.
//!
//! The runs at the limit use a 64 MiB thread. This crate's tests build
//! unoptimized, where a level of the tree takes many times the stack an
//! optimized build takes (over 11 KiB per level of an aggregate chain, so
//! the deepest one allowed overflows even 8 MiB). The limits are sized by
//! optimized builds, measured as `MAX_EXPR_DEPTH` describes.

use rustledger_core::Directive;
use rustledger_query::{Executor, QueryError, QueryResult, parse};

/// The depth budget `parser.rs` enforces, as the counting rule there
/// describes it.
const LIMIT: usize = 720;
/// What one bracket costs in that budget.
const BRACKET: usize = 12;
/// The most brackets that may nest.
const BRACKETS: usize = 60;

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

/// Parse and run `bql` on a 64 MiB thread, returning the executor's answer.
fn try_run(bql: &str) -> Result<QueryResult, QueryError> {
    on_stack(64 * 1024 * 1024, || {
        let directives = directives();
        let query = parse(bql).unwrap_or_else(|e| panic!("{e}"));
        Executor::new(&directives).execute(&query)
    })
}

/// Parse and run `bql` on a 64 MiB thread.
fn run(bql: &str) -> QueryResult {
    try_run(bql).unwrap_or_else(|e| panic!("{e}"))
}

fn assert_too_deep(bql: &str) {
    let err = parse(bql).expect_err("a query past the limit must be refused");
    assert!(
        err.to_string().contains("nesting too deep"),
        "expected the nesting error, got: {err}"
    );
}

/// A shape: its name, the length that brings it exactly to the limit, and
/// the query of a given length.
type Shape = (&'static str, usize, Box<dyn Fn(usize) -> String>);

/// `term`, then `n` more joined by `AND`.
fn joined(term: &'static str) -> Box<dyn Fn(usize) -> String> {
    Box::new(move |n| format!("SELECT {term}{}", format!(" AND {term}").repeat(n)))
}

/// Each shape that runs, by the length that brings it exactly to the limit.
/// The counts follow `scan_delimiters`: one per operator token and
/// `BRACKET` per bracket, so a comparison joined by `AND` costs two, and a
/// chain after `sum(number)` starts from that call's bracket.
fn shapes() -> Vec<Shape> {
    vec![
        (
            "+",
            LIMIT,
            Box::new(|n| format!("SELECT 1{}", " + 1".repeat(n))),
        ),
        (
            "AND",
            LIMIT,
            Box::new(|n| format!("SELECT TRUE{}", " AND TRUE".repeat(n))),
        ),
        (
            "OR",
            LIMIT,
            Box::new(|n| format!("SELECT FALSE{}", " OR FALSE".repeat(n))),
        ),
        (
            "NOT",
            LIMIT,
            Box::new(|n| format!("SELECT {}TRUE", "NOT ".repeat(n))),
        ),
        (
            "mixed * and -",
            LIMIT / 2,
            Box::new(|n| format!("SELECT 1{}", " * 2 - 1".repeat(n))),
        ),
        // One `=` plus `AND 1 = 1` at two apiece: 1 + 2n.
        ("= joined by AND", (LIMIT - 1) / 2, joined("1 = 1")),
        // A decimal's `.` is part of its literal, no attribute access, and
        // costs nothing.
        (
            "+ of decimals",
            LIMIT,
            Box::new(|n| format!("SELECT 1.5{}", " + 2.5".repeat(n))),
        ),
        // The generated-query shape: one `~` plus `OR account ~ ...` at two
        // apiece.
        (
            "~ joined by OR",
            (LIMIT - 1) / 2,
            Box::new(|n| {
                format!(
                    "SELECT account WHERE account ~ 'Bank'{}",
                    " OR account ~ 'Nope'".repeat(n)
                )
            }),
        ),
        // A bracket holding 500 operators, then a chain after it: the
        // bracket's depth carries into the chain around it, 12 + 500 + n.
        (
            "bracket then chain",
            LIMIT - BRACKET - 500,
            Box::new(|n| format!("SELECT (1{}){}", " + 1".repeat(500), " + 1".repeat(n))),
        ),
        // The costliest chains per level: in an aggregate query's target,
        // HAVING and ORDER BY. `sum(` is a bracket.
        (
            "aggregate target",
            LIMIT - BRACKET,
            Box::new(|n| {
                format!(
                    "SELECT account, sum(number){} GROUP BY account",
                    " + 1".repeat(n)
                )
            }),
        ),
        (
            "aggregate HAVING",
            LIMIT - BRACKET - 1,
            Box::new(|n| {
                format!(
                    "SELECT account, sum(number) GROUP BY account HAVING sum(number){} > 0",
                    " + 1".repeat(n)
                )
            }),
        ),
        (
            "aggregate ORDER BY",
            LIMIT - BRACKET,
            Box::new(|n| {
                format!(
                    "SELECT account, sum(number) GROUP BY account ORDER BY sum(number){}",
                    " + 1".repeat(n)
                )
            }),
        ),
        // `>` plus `AND sum(number) > 0` at two apiece, after one bracket.
        (
            "aggregate comparisons joined by AND",
            (LIMIT - BRACKET - 1) / 2,
            Box::new(|n| {
                format!(
                    "SELECT account, sum(number) > 0{} GROUP BY account",
                    " AND sum(number) > 0".repeat(n)
                )
            }),
        ),
        // 30 brackets around an aggregate chain: 30 * 12 + 12 + n.
        (
            "brackets around an aggregate chain",
            LIMIT - 31 * BRACKET,
            Box::new(|n| {
                format!(
                    "SELECT account, {}sum(number){}{} GROUP BY account",
                    "(".repeat(30),
                    " + 1".repeat(n),
                    ")".repeat(30)
                )
            }),
        ),
        // Brackets alone reach the 60-bracket limit and the budget together.
        (
            "parentheses",
            BRACKETS,
            Box::new(|n| format!("SELECT {}1{}", "(".repeat(n), ")".repeat(n))),
        ),
        (
            "nested calls",
            BRACKETS,
            Box::new(|n| format!("SELECT {}1{}", "abs(".repeat(n), ")".repeat(n))),
        ),
        // `sum(` is one more bracket.
        (
            "nested calls around an aggregate",
            BRACKETS - 1,
            Box::new(|n| {
                format!(
                    "SELECT account, {}sum(number){} GROUP BY account",
                    "abs(".repeat(n),
                    ")".repeat(n)
                )
            }),
        ),
        (
            "nested subqueries",
            BRACKETS,
            Box::new(|n| {
                format!(
                    "SELECT account FROM {}postings{}",
                    "(SELECT account FROM ".repeat(n),
                    ")".repeat(n)
                )
            }),
        ),
    ]
}

#[test]
fn test_parse_shapes_straddle_the_depth_limit() {
    for (name, at_limit, query) in shapes() {
        let ok = query(at_limit);
        assert!(parse(&ok).is_ok(), "{name}: {at_limit} should parse");
        assert_too_deep(&query(at_limit + 1));
    }
}

/// At the limit, every shape runs to completion, not just parses: the
/// recursive passes after the parse fit the thread at this depth.
#[test]
fn test_execute_shapes_at_the_depth_limit() {
    for (name, at_limit, query) in shapes() {
        let result = run(&format!("{} LIMIT 1", query(at_limit)));
        assert_eq!(result.rows.len(), 1, "{name}: {:?}", result.rows);
    }
}

/// Every counted operator, chained to exactly the limit and one past it, so
/// dropping any of them from the count fails here. A comparison cannot chain
/// on its own, so each term after the first costs its operator plus the
/// `AND` that joins it.
#[test]
fn test_parse_each_counted_operator_straddles_the_depth_limit() {
    let cases: Vec<Shape> = vec![
        (
            "%",
            LIMIT,
            Box::new(|n| format!("SELECT 7{}", " % 5".repeat(n))),
        ),
        (
            "/",
            LIMIT,
            Box::new(|n| format!("SELECT 1{}", " / 1".repeat(n))),
        ),
        (
            "*",
            LIMIT,
            Box::new(|n| format!("SELECT 1{}", " * 1".repeat(n))),
        ),
        (
            "-",
            LIMIT,
            Box::new(|n| format!("SELECT 1{}", " - 1".repeat(n))),
        ),
        // One comparison, then two apiece.
        ("<", (LIMIT - 1) / 2, joined("1 < 2")),
        ("<=", (LIMIT - 1) / 2, joined("1 <= 2")),
        (">", (LIMIT - 1) / 2, joined("2 > 1")),
        (">=", (LIMIT - 1) / 2, joined("2 >= 1")),
        ("!=", (LIMIT - 1) / 2, joined("1 != 2")),
        ("!~", (LIMIT - 1) / 2, joined("'a' !~ 'b'")),
        ("~", (LIMIT - 1) / 2, joined("'a' ~ 'a'")),
        ("IN", (LIMIT - 1) / 2, joined("'x' IN tags")),
        ("IS NULL", (LIMIT - 1) / 2, joined("payee IS NULL")),
        // `BETWEEN` and its own `AND`, then three apiece.
        (
            "BETWEEN ... AND",
            (LIMIT - 2) / 3,
            joined("1 BETWEEN 0 AND 2"),
        ),
        // One `[` per subscript.
        (
            "['k']",
            LIMIT - 1,
            Box::new(|n| format!("SELECT x['k']{}", "['k']".repeat(n))),
        ),
        (
            ".",
            LIMIT,
            Box::new(|n| format!("SELECT entry{}", ".meta".repeat(n))),
        ),
    ];
    for (name, at_limit, query) in cases {
        let ok = query(at_limit);
        assert!(parse(&ok).is_ok(), "{name}: {at_limit} should parse");
        assert_too_deep(&query(at_limit + 1));
    }
}

/// An attribute chain at the limit is planned and run as well as parsed: it
/// may be refused as a query error, but it must not overflow.
#[test]
fn test_execute_attribute_chain_at_the_depth_limit() {
    let chain = |n: usize| format!("SELECT entry{} LIMIT 1", ".meta".repeat(n));
    assert_too_deep(&chain(LIMIT + 1));
    match try_run(&chain(LIMIT)) {
        Ok(result) => assert_eq!(result.rows.len(), 1, "{:?}", result.rows),
        Err(e) => assert!(!e.to_string().is_empty()),
    }
}

/// The error is at the operator that passes the limit.
#[test]
fn test_parse_depth_error_names_the_operator_past_the_limit() {
    let err = parse(&format!("SELECT 1{}", " + 1".repeat(LIMIT + 5))).expect_err("too deep");
    // `SELECT 1` is 8 bytes, each ` + 1` is 4, and the `+` is the 2nd of them.
    assert_eq!(err.position, 8 + 4 * LIMIT + 1, "{err}");
    assert_eq!(
        err.to_string().matches("exceeds maximum of 720").count(),
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
    let chain = format!("1{}", " + 1".repeat(600));
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
