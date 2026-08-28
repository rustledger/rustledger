//! Deterministic cachegrind harness for the BQL query executor.
//!
//! Generates N transactions, then runs four representative query shapes
//! (projection, WHERE filter, GROUP BY aggregation, ORDER BY sort) in a loop so
//! cachegrind has enough signal:
//!
//! ```text
//! cargo build -p rustledger-query --profile profiling --example profile_query
//! valgrind --tool=cachegrind ./target/profiling/examples/profile_query 20000 5
//! ```

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_query::{Executor, parse as parse_query};

fn generate(n: usize) -> Vec<Directive> {
    let cats = ["Food", "Coffee", "Groceries", "Transport", "Rent", "Salary"];
    let payees = ["Store A", "Store B", "Cafe", "Gas", "Market", "Corp"];
    let mut out = Vec::with_capacity(n);
    let (mut y, mut m, mut d) = (2020i32, 1u32, 1u32);
    for i in 0..n {
        let amount = dec!(10.00) + rust_decimal::Decimal::from((i % 500) as i32);
        let date = rustledger_core::naive_date(y, m, d).unwrap();
        let txn = Transaction::new(date, format!("Txn {i}"))
            .with_payee(payees[i % payees.len()])
            .with_synthesized_posting(Posting::new(
                format!("Expenses:{}", cats[i % cats.len()]),
                Amount::new(amount, "USD"),
            ))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(-amount, "USD")));
        out.push(Directive::Transaction(txn));
        d += 1;
        if d > 28 {
            d = 1;
            m += 1;
            if m > 12 {
                m = 1;
                y += 1;
            }
        }
    }
    out
}

fn main() {
    let mut args = std::env::args().skip(1);
    let n: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(20_000);
    let iters: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(5);

    let directives = generate(n);
    let queries: Vec<_> = [
        "SELECT date, account, position",
        "SELECT account, position WHERE account ~ \"Expenses\"",
        "SELECT account, sum(position) GROUP BY account",
        "SELECT date, account, position ORDER BY date DESC",
        // The `#postings` SYSTEM TABLE, not the default source. These are
        // separate paths -- `build_postings_table` versus `collect_postings`
        // -- and only the default one was profiled here, which is how a 7x
        // gap went unnoticed: `SELECT count(account) FROM #postings` took
        // 681ms against 93ms for the same query without the FROM (#2169).
        "SELECT account FROM #postings",
        "SELECT count(account) FROM #postings",
    ]
    .iter()
    .map(|q| parse_query(q).expect("parse query"))
    .collect();

    let mut sink = 0usize;
    for _ in 0..iters {
        for q in &queries {
            let mut ex = Executor::new(std::hint::black_box(&directives));
            match ex.execute(std::hint::black_box(q)) {
                Ok(r) => sink = sink.wrapping_add(r.rows.len()),
                Err(e) => eprintln!("query error: {e}"),
            }
        }
    }
    eprintln!(
        "query profile: {n} directives x {iters} iters x {} queries; total rows={sink}",
        queries.len()
    );
}
