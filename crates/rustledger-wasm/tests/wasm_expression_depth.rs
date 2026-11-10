//! Long operator chains in a query come back as a query error, and later
//! queries keep running.
//!
//! A chain of thousands of `AND`s or stacked `NOT`s used to build an
//! expression tree too deep for the wasm stack. The parser now refuses such a
//! query with the same "nesting too deep" error it gives deeply nested
//! brackets. Each test runs the long chain, checks that the call returns that
//! error, and then runs an ordinary query on a new ledger in the same module.

#![cfg(target_arch = "wasm32")]

use rustledger_wasm::ParsedLedger;
use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

const LEDGER: &str = "2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
";

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// The messages of `result`'s errors.
fn errors(result: &JsValue) -> Vec<String> {
    js_sys::Array::from(&get_field(result, "errors"))
        .iter()
        .map(|e| get_field(&e, "message").as_string().unwrap_or_default())
        .collect()
}

/// Run `long` on one ledger, expecting the nesting error, then an ordinary
/// query on a new ledger.
fn check_refused_then_query(long: &str) {
    let result = ParsedLedger::new(LEDGER)
        .query(long)
        .expect("query returns");
    let messages = errors(&result);
    assert!(
        messages.iter().any(|m| m.contains("nesting too deep")),
        "expected the nesting error, got {messages:?}"
    );

    let result = ParsedLedger::new(LEDGER)
        .query("SELECT account, number WHERE account = 'Assets:Bank'")
        .expect("later query returns");
    assert!(errors(&result).is_empty(), "{:?}", errors(&result));
    let rows = js_sys::Array::from(&get_field(&result, "rows"));
    assert_eq!(rows.length(), 1, "the later query must still give its row");
}

#[wasm_bindgen_test]
fn and_chain_of_4000_terms_is_refused_then_queries_run() {
    check_refused_then_query(&format!(
        "SELECT account WHERE 1 = 1{}",
        " AND 1 = 1".repeat(4000)
    ));
}

#[wasm_bindgen_test]
fn not_chain_of_5000_is_refused_then_queries_run() {
    check_refused_then_query(&format!("SELECT account WHERE {}TRUE", "NOT ".repeat(5000)));
}

#[wasm_bindgen_test]
fn plus_and_or_chains_of_20000_are_refused_then_queries_run() {
    check_refused_then_query(&format!("SELECT 1{}", " + 1".repeat(20_000)));
    check_refused_then_query(&format!(
        "SELECT account WHERE account ~ 'x'{}",
        " OR account ~ 'x'".repeat(20_000)
    ));
}

/// A generated filter of 200 alternatives still runs. (The chains at the
/// limit itself are run natively, in `rustledger-query`'s
/// `expression_depth_test.rs`: this unoptimized test build takes several
/// times the stack per level that the optimized module does.)
#[wasm_bindgen_test]
fn generated_or_filter_of_200_terms_runs() {
    let terms = (0..200)
        .map(|i| format!("account ~ 'Assets:Bank{i}'"))
        .chain(["account ~ 'Assets:Bank'".to_string()])
        .collect::<Vec<_>>();
    let result = ParsedLedger::new(LEDGER)
        .query(&format!("SELECT account WHERE {}", terms.join(" OR ")))
        .expect("query returns");
    assert!(errors(&result).is_empty(), "{:?}", errors(&result));
    let rows = js_sys::Array::from(&get_field(&result, "rows"));
    assert_eq!(rows.length(), 1);
}
