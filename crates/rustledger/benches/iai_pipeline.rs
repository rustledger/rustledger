//! Deterministic instruction-count benchmarks via iai-callgrind (Valgrind /
//! Callgrind).
//!
//! Unlike the criterion wall-clock benches (`pipeline_bench`), these report
//! **instruction counts** — identical run-to-run regardless of machine load, so
//! they're diffable night-over-night and immune to CI-runner noise. The nightly
//! `profile.yml` workflow runs them (it installs Valgrind + the
//! `iai-callgrind-runner`); they are intentionally **not** wired into PR CI.
//!
//! Run locally with Valgrind installed:
//! ```text
//! cargo install iai-callgrind-runner --version 0.16.1
//! cargo bench -p rustledger --bench iai_pipeline
//! ```

use std::hint::black_box;

use iai_callgrind::{library_benchmark, library_benchmark_group, main};

/// Generate a deterministic ledger of `n` balanced 2-posting transactions.
fn generate_ledger(n: usize) -> String {
    let mut s = String::from("option \"operating_currency\" \"USD\"\n");
    for account in [
        "Assets:Bank",
        "Expenses:Food",
        "Income:Salary",
        "Liabilities:Card",
    ] {
        s.push_str("2020-01-01 open ");
        s.push_str(account);
        s.push_str(" USD\n");
    }
    for i in 0..n {
        let month = (i / 28) % 12 + 1;
        let day = i % 28 + 1;
        let amt = i % 500 + 1;
        s.push_str(&format!(
            "2021-{month:02}-{day:02} * \"Payee {i}\" \"memo\"\n  \
             Expenses:Food  {amt}.00 USD\n  Assets:Bank  -{amt}.00 USD\n"
        ));
    }
    s
}

// Parser instruction count at two ledger sizes. The `generate_ledger` setup in
// each `#[bench]` runs *outside* the measured region — only the parse is counted.
// (A `///` doc comment here is rejected by the `#[library_benchmark]` macro.)
#[library_benchmark]
#[bench::txns_1k(generate_ledger(1_000))]
#[bench::txns_10k(generate_ledger(10_000))]
fn parse_ledger(source: String) -> rustledger_parser::ParseResult {
    black_box(rustledger_parser::parse(black_box(&source)))
}

library_benchmark_group!(name = pipeline; benchmarks = parse_ledger);
main!(library_benchmark_groups = pipeline);
