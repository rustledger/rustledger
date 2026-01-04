//! Parser performance benchmarks.
//!
//! Run with: cargo bench -p rustledger-parser

#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use rustledger_parser::parse;

/// Generate a synthetic ledger with N transactions.
#[allow(clippy::vec_init_then_push)]
fn generate_ledger(num_transactions: usize) -> String {
    let mut lines = Vec::new();

    // Add opening directives
    lines.push("2024-01-01 open Assets:Bank:Checking USD".to_string());
    lines.push("2024-01-01 open Expenses:Food USD".to_string());
    lines.push("2024-01-01 open Expenses:Coffee USD".to_string());
    lines.push("2024-01-01 open Expenses:Groceries USD".to_string());
    lines.push("2024-01-01 open Expenses:Transport USD".to_string());
    lines.push(String::new());

    // Generate transactions
    let categories = ["Food", "Coffee", "Groceries", "Transport"];
    let payees = ["Store A", "Store B", "Cafe", "Gas Station", "Supermarket"];
    let mut day = 1;
    let mut month = 1;
    let mut year = 2024;

    for i in 0..num_transactions {
        let category = categories[i % categories.len()];
        let payee = payees[i % payees.len()];
        let amount = format!("{:.2}", 10.0 + (i % 100) as f64);

        lines.push(format!(
            "{year:04}-{month:02}-{day:02} * \"{payee}\" \"Transaction {i}\""
        ));
        lines.push(format!("  Expenses:{category}  {amount} USD"));
        lines.push(format!("  Assets:Bank:Checking  -{amount} USD"));
        lines.push(String::new());

        // Advance date
        day += 1;
        if day > 28 {
            day = 1;
            month += 1;
            if month > 12 {
                month = 1;
                year += 1;
            }
        }
    }

    lines.join("\n")
}

fn bench_parse_small(c: &mut Criterion) {
    let ledger = generate_ledger(10);
    let bytes = ledger.len();

    let mut group = c.benchmark_group("parse_small");
    group.throughput(Throughput::Bytes(bytes as u64));

    group.bench_function("10_transactions", |b| {
        b.iter(|| parse(black_box(&ledger)));
    });

    group.finish();
}

fn bench_parse_medium(c: &mut Criterion) {
    let ledger = generate_ledger(100);
    let bytes = ledger.len();

    let mut group = c.benchmark_group("parse_medium");
    group.throughput(Throughput::Bytes(bytes as u64));

    group.bench_function("100_transactions", |b| {
        b.iter(|| parse(black_box(&ledger)));
    });

    group.finish();
}

fn bench_parse_large(c: &mut Criterion) {
    let ledger = generate_ledger(1000);
    let bytes = ledger.len();

    let mut group = c.benchmark_group("parse_large");
    group.throughput(Throughput::Bytes(bytes as u64));

    group.bench_function("1000_transactions", |b| {
        b.iter(|| parse(black_box(&ledger)));
    });

    group.finish();
}

fn bench_parse_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_scaling");

    for size in [10, 50, 100, 500, 1000] {
        let ledger = generate_ledger(size);
        group.throughput(Throughput::Bytes(ledger.len() as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), &ledger, |b, ledger| {
            b.iter(|| parse(black_box(ledger)));
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_parse_small,
    bench_parse_medium,
    bench_parse_large,
    bench_parse_scaling
);
criterion_main!(benches);
