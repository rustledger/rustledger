//! Deterministic cachegrind harness for the formatter (`format_directives`):
//! a varied ledger (transactions with costs/prices, opens, balances) formatted
//! to text in a loop, isolating the pretty-printer from parsing.
//!
//! ```text
//! cargo build -p rustledger-core --profile profiling --example profile_format
//! valgrind --tool=cachegrind ./target/profiling/examples/profile_format 20000 5
//! ```

use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Balance, CostNumber, CostSpec, Directive, FormatConfig, Open, Posting, PriceAnnotation,
    Transaction, format_directives,
};

fn d(y: i32, m: u32, day: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(y, m, day).unwrap()
}

fn generate(n: usize) -> Vec<Directive> {
    let mut out = Vec::with_capacity(n + 40);
    for k in 0..16 {
        out.push(Directive::Open(Open::new(
            d(2024, 1, 1),
            format!("Assets:Acct{k}"),
        )));
    }
    out.push(Directive::Open(Open::new(d(2024, 1, 1), "Income:Salary")));
    out.push(Directive::Open(Open::new(d(2024, 1, 1), "Assets:Stock")));
    for i in 0..n {
        let month = (i % 12 + 1) as u32;
        let day = (i % 28 + 1) as u32;
        let amt = dec!(10.00) + rust_decimal::Decimal::from((i % 9000) as i64);
        let txn = if i % 3 == 0 {
            // cost + price posting (exercises format_cost_spec / format_price)
            Transaction::new(d(2024, month, day), format!("Buy lot {i}"))
                .with_flag('*')
                .with_synthesized_posting(
                    Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number(CostNumber::PerUnit { value: amt })
                            .with_currency("USD"),
                    ),
                )
                .with_synthesized_posting(
                    Posting::new("Assets:Acct0", Amount::new(-amt * dec!(10), "USD"))
                        .with_price(PriceAnnotation::unit(Amount::new(amt, "USD"))),
                )
        } else {
            Transaction::new(d(2024, month, day), format!("Payment {i}"))
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    format!("Assets:Acct{}", i % 16),
                    Amount::new(amt, "USD"),
                ))
                .with_synthesized_posting(Posting::new("Income:Salary", Amount::new(-amt, "USD")))
        };
        out.push(Directive::Transaction(txn));
        if i % 50 == 49 {
            out.push(Directive::Balance(Balance::new(
                d(2024, month, day),
                format!("Assets:Acct{}", i % 16),
                Amount::new(amt, "USD"),
            )));
        }
    }
    out
}

fn main() {
    let mut a = std::env::args().skip(1);
    let n: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(20_000);
    let iters: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(5);

    let directives = generate(n);
    let config = FormatConfig::default();
    let mut sink = 0usize;
    for _ in 0..iters {
        let s = format_directives(std::hint::black_box(&directives), &config);
        sink = sink.wrapping_add(s.len());
    }
    eprintln!(
        "format profile: {n} txns x {iters} iters; dirs={} out_chars/iter={}",
        directives.len(),
        sink / iters.max(1)
    );
}
