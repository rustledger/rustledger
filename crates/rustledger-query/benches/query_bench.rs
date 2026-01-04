//! Query executor performance benchmarks.
//!
//! Run with: cargo bench -p beancount-query

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_query::{parse as parse_query, Executor};
use chrono::NaiveDate;
use rust_decimal_macros::dec;

/// Generate sample directives for benchmarking.
fn generate_directives(num_transactions: usize) -> Vec<Directive> {
    let mut directives = Vec::with_capacity(num_transactions);

    let categories = ["Food", "Coffee", "Groceries", "Transport"];
    let payees = ["Store A", "Store B", "Cafe", "Gas Station", "Supermarket"];

    let mut day = 1u32;
    let mut month = 1u32;
    let mut year = 2024i32;

    for i in 0..num_transactions {
        let category = categories[i % categories.len()];
        let payee = payees[i % payees.len()];
        let amount = dec!(10.00) + rust_decimal::Decimal::from(i as i32 % 100);

        let date = NaiveDate::from_ymd_opt(year, month, day).unwrap();

        let txn = Transaction::new(date, format!("Transaction {i}"))
            .with_flag('*')
            .with_payee(payee)
            .with_posting(Posting::new(
                format!("Expenses:{category}"),
                Amount::new(amount, "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Bank:Checking",
                Amount::new(-amount, "USD"),
            ));

        directives.push(Directive::Transaction(txn));

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

    directives
}

fn bench_simple_select(c: &mut Criterion) {
    let directives = generate_directives(1000);

    let mut group = c.benchmark_group("query_simple_select");
    group.throughput(Throughput::Elements(1000));

    group.bench_function("select_all_columns", |b| {
        let query = parse_query("SELECT date, account, position").unwrap();
        b.iter(|| {
            let mut executor = Executor::new(black_box(&directives));
            executor.execute(black_box(&query))
        });
    });

    group.finish();
}

fn bench_where_clause(c: &mut Criterion) {
    let directives = generate_directives(1000);

    let mut group = c.benchmark_group("query_where");
    group.throughput(Throughput::Elements(1000));

    group.bench_function("where_account_contains", |b| {
        let query = parse_query("SELECT account WHERE account ~ \"Expenses:\"").unwrap();
        b.iter(|| {
            let mut executor = Executor::new(black_box(&directives));
            executor.execute(black_box(&query))
        });
    });

    group.finish();
}

fn bench_group_by(c: &mut Criterion) {
    let directives = generate_directives(1000);

    let mut group = c.benchmark_group("query_group_by");
    group.throughput(Throughput::Elements(1000));

    group.bench_function("group_by_account_sum", |b| {
        let query = parse_query("SELECT account, SUM(position) GROUP BY account").unwrap();
        b.iter(|| {
            let mut executor = Executor::new(black_box(&directives));
            executor.execute(black_box(&query))
        });
    });

    group.finish();
}

fn bench_balances(c: &mut Criterion) {
    let directives = generate_directives(1000);

    let mut group = c.benchmark_group("query_balances");
    group.throughput(Throughput::Elements(1000));

    group.bench_function("balances", |b| {
        let query = parse_query("BALANCES").unwrap();
        b.iter(|| {
            let mut executor = Executor::new(black_box(&directives));
            executor.execute(black_box(&query))
        });
    });

    group.finish();
}

fn bench_query_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("query_scaling");

    for size in [100, 500, 1000, 5000] {
        let directives = generate_directives(size);
        let query = parse_query("SELECT account, SUM(position) GROUP BY account").unwrap();

        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &directives,
            |b, directives| {
                b.iter(|| {
                    let mut executor = Executor::new(black_box(directives));
                    executor.execute(black_box(&query))
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_simple_select,
    bench_where_clause,
    bench_group_by,
    bench_balances,
    bench_query_scaling
);
criterion_main!(benches);
