//! Deterministic cachegrind harness for the booking engine on a cost-heavy
//! workload: per account, N buys build up a deep lot inventory, then N
//! empty-cost (`{}`) sells force FIFO lot-matching + capital-gains computation.
//! Parallel to `rustledger/examples/profile_pipeline` and
//! `rustledger-query/examples/profile_query`.
//!
//! ```text
//! cargo build -p rustledger-booking --profile profiling --example profile_booking
//! valgrind --tool=cachegrind ./target/profiling/examples/profile_booking 30 100 3
//! ```
//!
//! Args: `<accounts> <lots-per-account> <iterations>` (defaults `30 100 5`).
//! Most of the cost lands in `imbl::Vector` traversal of the lot inventory — a
//! deliberate space/time trade documented on `rustledger_core::Inventory`
//! (issue #1086: O(1) snapshots for BQL JOURNAL at the cost of O(log N) lot ops).

use rust_decimal_macros::dec;
use rustledger_booking::book;
use rustledger_core::{
    Amount, BookingMethod, CostNumber, CostSpec, Directive, Posting, PriceAnnotation, Transaction,
};

fn generate(accounts: usize, lots: usize) -> Vec<Directive> {
    let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
    let mut d = Vec::with_capacity(accounts * lots * 2);
    for k in 0..accounts {
        let stock = format!("Assets:Stock{k}");
        // Acquisitions: one distinct-price lot per buy.
        for i in 0..lots {
            let price = dec!(100) + rust_decimal::Decimal::from(i as i64);
            let buy = Transaction::new(date, "buy")
                .with_synthesized_posting(
                    Posting::new(stock.clone(), Amount::new(dec!(1), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number(CostNumber::PerUnit { value: price })
                            .with_currency("USD"),
                    ),
                )
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(-price, "USD")));
            d.push(Directive::Transaction(buy));
        }
        // Reductions: empty cost `{}` -> FIFO match against the held lots.
        for i in 0..lots {
            let price = dec!(150) + rust_decimal::Decimal::from(i as i64);
            let sell = Transaction::new(date, "sell")
                .with_synthesized_posting(
                    Posting::new(stock.clone(), Amount::new(dec!(-1), "AAPL"))
                        .with_cost(CostSpec::empty())
                        .with_price(PriceAnnotation::unit(Amount::new(price, "USD"))),
                )
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(price, "USD")))
                .with_synthesized_posting(Posting::auto("Income:Gains"));
            d.push(Directive::Transaction(sell));
        }
    }
    d
}

fn main() {
    let mut a = std::env::args().skip(1);
    let accounts: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(30);
    let lots: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(100);
    let iters: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(5);

    let directives = generate(accounts, lots);
    let mut sink = 0usize;
    let mut failed = 0usize;
    for _ in 0..iters {
        let r = book(std::hint::black_box(&directives), BookingMethod::Fifo);
        sink = sink.wrapping_add(r.booked.len());
        failed = r.failed.len();
    }
    eprintln!(
        "booking profile: {accounts} accts x {lots} lots (buys+sells) x {iters} iters; \
         dirs={} booked_sink={sink} failed/iter={failed}",
        directives.len()
    );
    // A non-zero failure count shifts the profile toward error-handling paths
    // and makes the numbers misleading — surface it loudly rather than silently.
    assert_eq!(
        failed, 0,
        "{failed} bookings failed for these args; the profile would not reflect \
         the steady-state booking path — adjust accounts/lots so all bookings succeed"
    );
}
