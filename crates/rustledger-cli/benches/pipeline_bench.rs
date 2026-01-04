//! Full pipeline benchmarks (parse -> load -> validate).
//!
//! These benchmarks measure end-to-end performance of the rustledger
//! processing pipeline.
//!
//! Run with: cargo bench -p beancount-cli

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use rustledger_booking::interpolate;
use rustledger_core::Directive;
use rustledger_parser::parse;
use rustledger_validate::validate;

/// Generate a realistic ledger with N transactions.
#[allow(clippy::vec_init_then_push)]
fn generate_ledger(num_transactions: usize) -> String {
    let mut lines = Vec::new();

    // Options
    lines.push("option \"title\" \"Benchmark Ledger\"".to_string());
    lines.push("option \"operating_currency\" \"USD\"".to_string());
    lines.push(String::new());

    // Add opening directives
    lines.push("2020-01-01 open Assets:Bank:Checking USD".to_string());
    lines.push("2020-01-01 open Assets:Bank:Savings USD".to_string());
    lines.push("2020-01-01 open Assets:Investment STOCK,USD".to_string());
    lines.push("2020-01-01 open Expenses:Food USD".to_string());
    lines.push("2020-01-01 open Expenses:Coffee USD".to_string());
    lines.push("2020-01-01 open Expenses:Groceries USD".to_string());
    lines.push("2020-01-01 open Expenses:Transport USD".to_string());
    lines.push("2020-01-01 open Expenses:Utilities USD".to_string());
    lines.push("2020-01-01 open Income:Salary USD".to_string());
    lines.push("2020-01-01 open Income:Interest USD".to_string());
    lines.push("2020-01-01 open Equity:Opening USD".to_string());
    lines.push(String::new());

    // Commodities
    lines.push("2020-01-01 commodity USD".to_string());
    lines.push("2020-01-01 commodity STOCK".to_string());
    lines.push(String::new());

    // Opening balance
    lines.push("2020-01-01 * \"Opening balance\"".to_string());
    lines.push("  Assets:Bank:Checking  10000.00 USD".to_string());
    lines.push("  Equity:Opening".to_string());
    lines.push(String::new());

    // Generate transactions
    let categories = ["Food", "Coffee", "Groceries", "Transport", "Utilities"];
    let payees = ["Store A", "Store B", "Cafe", "Gas Station", "Supermarket"];
    let mut day = 2;
    let mut month = 1;
    let mut year = 2020;

    for i in 0..num_transactions {
        let category = categories[i % categories.len()];
        let payee = payees[i % payees.len()];
        let amount = format!("{:.2}", 10.0 + (i % 100) as f64);

        lines.push(format!(
            "{year:04}-{month:02}-{day:02} * \"{payee}\" \"Transaction {i}\" #tag{i}"
        ));
        lines.push(format!("  Expenses:{category}  {amount} USD"));
        lines.push("  Assets:Bank:Checking".to_string());
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

    // Add some balance assertions
    lines.push(format!("{year:04}-{month:02}-{day:02} balance Assets:Bank:Checking 0 USD"));

    lines.join("\n")
}

fn bench_parse_only(c: &mut Criterion) {
    let mut group = c.benchmark_group("pipeline_parse");

    for size in [100, 500, 1000, 5000] {
        let ledger = generate_ledger(size);
        group.throughput(Throughput::Bytes(ledger.len() as u64));

        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{size}_txns")),
            &ledger,
            |b, ledger| {
                b.iter(|| parse(black_box(ledger)));
            },
        );
    }

    group.finish();
}

fn bench_parse_and_validate(c: &mut Criterion) {
    let mut group = c.benchmark_group("pipeline_parse_validate");

    for size in [100, 500, 1000] {
        let ledger = generate_ledger(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{size}_txns")),
            &ledger,
            |b, ledger| {
                b.iter(|| {
                    let result = parse(ledger);
                    let directives: Vec<_> = result.directives.iter().map(|s| s.value.clone()).collect();
                    let errors = validate(&directives);
                    black_box((directives, errors))
                });
            },
        );
    }

    group.finish();
}

fn bench_full_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("pipeline_full");

    for size in [100, 500, 1000] {
        let ledger = generate_ledger(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{size}_txns")),
            &ledger,
            |b, ledger| {
                b.iter(|| {
                    // Parse
                    let result = parse(ledger);

                    // Extract directives
                    let mut directives: Vec<_> = result.directives.iter().map(|s| s.value.clone()).collect();

                    // Interpolate transactions
                    for directive in &mut directives {
                        if let Directive::Transaction(txn) = directive {
                            let _ = interpolate(txn);
                        }
                    }

                    // Validate
                    let errors = validate(&directives);

                    black_box((directives, errors))
                });
            },
        );
    }

    group.finish();
}

fn bench_transaction_throughput(c: &mut Criterion) {
    // Measure raw transactions-per-second capacity
    let mut group = c.benchmark_group("throughput");
    group.throughput(Throughput::Elements(10000));

    let ledger = generate_ledger(10000);

    group.bench_function("10k_transactions", |b| {
        b.iter(|| {
            let result = parse(black_box(&ledger));
            black_box(result.directives.len())
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_parse_only,
    bench_parse_and_validate,
    bench_full_pipeline,
    bench_transaction_throughput,
);
criterion_main!(benches);
