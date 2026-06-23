//! Differential parity harness for the two BQL function-evaluation paths.
//!
//! BQL function semantics are currently implemented **twice**: the lazy
//! per-row dispatcher `Executor::evaluate_function` (operates on `Expr` args +
//! a `PostingContext`) and the eager value dispatcher
//! `Executor::evaluate_function_on_values` (operates on pre-evaluated
//! `&[Value]`, used by `#postings` / aggregates / subqueries). The two have
//! drifted (extended-date functions, a `ROOT` negative-depth bug, `GETITEM`
//! on `NULL`, arity wording). The roadmap collapses them onto one registry.
//!
//! This module is the safety net for that collapse and a **permanent**
//! regression guard afterward: for every function whose arguments are
//! literal-constructible it asserts the two paths agree, and it pins the known
//! divergences so the reconciliation steps flip them deliberately, not
//! silently. Once the paths are unified these stay green by construction — and
//! re-divergence becomes a test failure here.

use super::Executor;
use super::types::{PostingContext, Value};
use crate::ast::{Expr, FunctionCall, Literal};
use crate::error::QueryError;
use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, Posting, Transaction, naive_date};

/// A throwaway transaction for the lazy path's `PostingContext`. The pure
/// functions under test evaluate their (literal) arguments without reading the
/// context, so its contents only need to be valid, not meaningful.
fn scratch_txn() -> Transaction {
    Transaction::new(naive_date(2024, 1, 15).unwrap(), "scratch")
        .with_flag('*')
        .with_synthesized_posting(Posting::new(
            "Assets:Bank:Checking",
            Amount::new(dec!(-5.00), "USD"),
        ))
}

/// Re-express a `Value` as an `Expr` that `evaluate_expr` maps back to that
/// same `Value`, so the lazy path receives exactly the eager path's arguments.
/// Returns `None` for variants with no literal form (Amount/Position/Inventory/
/// …) — those functions are out of scope for this literal-driven harness.
fn value_as_literal(v: &Value) -> Option<Expr> {
    Some(match v {
        Value::String(s) => Expr::Literal(Literal::String(s.clone())),
        Value::Number(n) => Expr::Literal(Literal::Number(*n)),
        Value::Integer(i) => Expr::Literal(Literal::Integer(*i)),
        Value::Date(d) => Expr::Literal(Literal::Date(*d)),
        Value::Boolean(b) => Expr::Literal(Literal::Boolean(*b)),
        Value::Null => Expr::Literal(Literal::Null),
        _ => return None,
    })
}

/// Run `name(args)` through both dispatchers. The lazy result is `None` only
/// when an argument has no literal form (case skipped, not a failure).
fn run_both(
    name: &str,
    args: &[Value],
) -> (Result<Value, QueryError>, Option<Result<Value, QueryError>>) {
    let directives: Vec<Directive> = Vec::new();
    let executor = Executor::new(&directives);

    let eager = executor.evaluate_function_on_values(name, args);

    let lazy = args
        .iter()
        .map(value_as_literal)
        .collect::<Option<Vec<Expr>>>()
        .map(|lit_args| {
            let txn = scratch_txn();
            let ctx = PostingContext {
                transaction: &txn,
                posting_index: 0,
                balance: None,
                account_balance: None,
                directive_index: None,
            };
            let call = FunctionCall {
                name: name.to_string(),
                args: lit_args,
            };
            executor.evaluate_function(&call, &ctx)
        });

    (eager, lazy)
}

/// Assert the two paths AGREE: equal `Ok` values, or both `Err` (error *wording*
/// may still differ pre-reconciliation — that is cosmetic and handled in the
/// reconciliation step; what matters is that neither path uniquely errors or
/// uniquely succeeds).
#[track_caller]
fn assert_parity(name: &str, args: &[Value]) {
    let (eager, lazy) = run_both(name, args);
    let Some(lazy) = lazy else { return };
    match (&lazy, &eager) {
        (Ok(l), Ok(e)) => assert_eq!(
            l, e,
            "value mismatch for {name}({args:?}): lazy={l:?} eager={e:?}"
        ),
        (Err(_), Err(_)) => {}
        _ => panic!("path divergence for {name}({args:?}): lazy={lazy:?} eager={eager:?}"),
    }
}

fn s(x: &str) -> Value {
    Value::String(x.to_string())
}

/// The shared pure functions that the two paths must already agree on. Every
/// case here is expected to pass today; the collapse must keep them passing.
#[test]
fn shared_pure_functions_agree_across_both_paths() {
    let acct = "Assets:Bank:Checking";
    let cases: &[(&str, Vec<Value>)] = &[
        // string
        ("UPPER", vec![s("hello")]),
        ("LOWER", vec![s("HELLO")]),
        ("LENGTH", vec![s("hello")]),
        (
            "SUBSTR",
            vec![s("hello world"), Value::Integer(0), Value::Integer(5)],
        ),
        ("TRIM", vec![s("  hi  ")]),
        ("STARTSWITH", vec![s("hello"), s("he")]),
        ("ENDSWITH", vec![s("hello"), s("lo")]),
        // account
        ("PARENT", vec![s(acct)]),
        ("LEAF", vec![s(acct)]),
        ("ROOT", vec![s(acct)]),
        ("ROOT", vec![s(acct), Value::Integer(2)]),
        ("ACCOUNT_DEPTH", vec![s(acct)]),
        // math
        ("ABS", vec![Value::Number(dec!(-3.5))]),
        ("NEG", vec![Value::Number(dec!(3.5))]),
        (
            "ROUND",
            vec![Value::Number(dec!(3.14159)), Value::Integer(2)],
        ),
        (
            "SAFEDIV",
            vec![Value::Number(dec!(10)), Value::Number(dec!(0))],
        ),
        // cast
        ("INT", vec![Value::Number(dec!(3.9))]),
        ("DECIMAL", vec![s("3.5")]),
        ("STR", vec![Value::Integer(42)]),
        ("BOOL", vec![Value::Integer(1)]),
    ];
    for (name, args) in cases {
        assert_parity(name, args);
    }
}

// ---------------------------------------------------------------------------
// Drift pins — these assert the CURRENT divergence between the paths. The
// reconciliation steps will flip each (and update the corresponding pin),
// proving the change is deliberate rather than an accidental behavior shift.
// ---------------------------------------------------------------------------

/// `ROOT(account, n)` with a negative depth: the lazy path correctly errors,
/// the eager path has a `*i as usize` bug that turns `-1` into `usize::MAX` and
/// silently returns the whole account. Reconciliation ports the lazy guard.
#[test]
fn drift_root_negative_depth() {
    let (eager, lazy) = run_both("ROOT", &[s("Assets:Bank:Checking"), Value::Integer(-1)]);
    assert!(
        lazy.unwrap().is_err(),
        "lazy ROOT(acct,-1) should error (depth guard)"
    );
    // The `*i as usize` cast turns -1 into usize::MAX, so `n >= parts.len()`
    // and eager returns the WHOLE account verbatim. Assert that exact value so
    // the pin can't be satisfied by some other accidental Ok result.
    assert!(
        matches!(&eager, Ok(Value::String(a)) if a == "Assets:Bank:Checking"),
        "eager ROOT(acct,-1) currently returns the whole account (the `*i as usize` bug), \
         got {eager:?} — flip this pin when the lazy guard is ported into the eager arm"
    );
}

/// `GETITEM(NULL, key)`: the eager path returns `NULL`, the lazy path falls
/// into a catch-all and errors. Reconciliation adds the `NULL` arm to lazy.
#[test]
fn drift_getitem_on_null() {
    let (eager, lazy) = run_both("GETITEM", &[Value::Null, s("k")]);
    assert!(
        matches!(eager, Ok(Value::Null)),
        "eager GETITEM(NULL,k) returns NULL, got {eager:?}"
    );
    assert!(
        lazy.unwrap().is_err(),
        "lazy GETITEM(NULL,k) currently errors — flip this pin when the NULL arm \
         is added to the lazy path"
    );
}

/// The 7 extended-date functions work in the lazy path but error
/// `UnknownFunction` in the eager path. Reconciliation registers them in eager.
#[test]
fn drift_extended_date_functions_missing_from_eager() {
    let directives: Vec<Directive> = Vec::new();
    let executor = Executor::new(&directives);
    let d = |y, m, day| Value::Date(naive_date(y, m, day).unwrap());
    // Per-function args that would be VALID once the function is registered, so
    // the only reason to error is that the name is unknown. Asserting the error
    // is specifically `UnknownFunction` (not just any error) means a partial
    // registration that errors on arity/type instead flips this pin red.
    let cases: &[(&str, Vec<Value>)] = &[
        ("DATE", vec![s("2024-01-15")]),
        ("DATE_ADD", vec![d(2024, 1, 15), Value::Integer(5)]),
        ("DATE_TRUNC", vec![d(2024, 1, 15), s("month")]),
        ("DATE_PART", vec![s("year"), d(2024, 1, 15)]),
        ("PARSE_DATE", vec![s("2024-01-15")]),
        (
            "DATE_BIN",
            vec![Value::Integer(1), d(2024, 1, 15), d(2024, 1, 1)],
        ),
        ("INTERVAL", vec![Value::Integer(1), s("day")]),
    ];
    for (name, args) in cases {
        let r = executor.evaluate_function_on_values(name, args);
        assert!(
            matches!(r, Err(QueryError::UnknownFunction(_))),
            "eager {name} currently errors with UnknownFunction, got {r:?} — flip this pin \
             when {name} is registered in the eager dispatcher"
        );
    }
}

/// `TODAY` takes no arguments; the lazy path rejects extra args, the eager path
/// ignores them. Reconciliation tightens the eager arm to match lazy.
#[test]
fn drift_today_extra_arg() {
    let (eager, lazy) = run_both("TODAY", &[Value::Integer(1)]);
    assert!(
        lazy.unwrap().is_err(),
        "lazy TODAY(x) should reject the extra arg"
    );
    assert!(
        eager.is_ok(),
        "eager TODAY(x) currently ignores the extra arg — flip this pin when the \
         eager arm gains the zero-arg guard"
    );
}
