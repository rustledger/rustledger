#![no_main]
//! Fuzz target for the BQL query **executor**.
//!
//! Parses arbitrary input as a BQL query and, when it parses, *executes* it
//! against a small fixed ledger. The executor must never panic on any query
//! the parser accepts. This guards the panic bug class found repeatedly by
//! hand — e.g. a divide-by-zero in `DATE_BIN`, an out-of-range integer cast,
//! an unchecked slice index in a function argument. It complements
//! `fuzz_query_parse`, which exercises only the parser.

use std::sync::LazyLock;

use libfuzzer_sys::fuzz_target;
use rustledger_core::Directive;
use rustledger_query::{parse, Executor};

/// A small but varied ledger so fuzzed queries reach every system table
/// (`#postings`, `#balances`, `#prices`, `#events`, `#notes`, …) and exercise
/// functions over real amounts, costs, accounts, dates, and metadata.
const LEDGER: &str = "\
2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Expenses:Food
2024-01-01 open Income:Salary
2024-01-01 commodity USD
  name: \"US Dollar\"
2024-01-15 * \"Coffee Shop\" \"Coffee\"
  category: \"food\"
  Expenses:Food         5.00 USD
  Assets:Bank:Checking  -5.00 USD
2024-01-16 price USD 1.10 EUR
2024-01-18 * \"Acme\" \"Salary\"
  Assets:Bank:Checking  1000.00 USD
  Income:Salary        -1000.00 USD
2024-01-20 balance Assets:Bank:Checking  995.00 USD
2024-01-21 note Assets:Bank:Checking \"a note\"
2024-01-22 event \"location\" \"office\"
";

/// Parse the fixed ledger once; every fuzz iteration borrows these directives.
static DIRECTIVES: LazyLock<Vec<Directive>> = LazyLock::new(|| {
    let (spanned, errors) = rustledger_parser::parse_directives(LEDGER);
    // Fail fast if the baseline fixture ever stops parsing cleanly — otherwise
    // the fuzzer would silently run against a partial/empty ledger and quietly
    // lose most of its coverage.
    assert!(
        errors.is_empty(),
        "fuzz_query_execute baseline LEDGER failed to parse: {errors:?}"
    );
    let directives: Vec<Directive> = spanned.into_iter().map(|s| s.value).collect();
    assert!(
        !directives.is_empty(),
        "fuzz_query_execute baseline LEDGER parsed to zero directives"
    );
    directives
});

fuzz_target!(|data: &[u8]| {
    if let Ok(input) = std::str::from_utf8(data) {
        // Any input the parser accepts must execute without panicking. Parse
        // errors are expected and ignored — the parser robustness is covered
        // by `fuzz_query_parse`.
        if let Ok(query) = parse(input) {
            let mut executor = Executor::new(&DIRECTIVES);
            let _ = executor.execute(&query);
        }
    }
});
