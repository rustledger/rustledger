//! Inventory and booking performance benchmarks.
//!
//! Run with: cargo bench -p rustledger-core

#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use chrono::NaiveDate;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{Amount, BookingMethod, Cost, CostSpec, Inventory, Position};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, day).unwrap()
}

/// Generate an inventory with N positions.
fn generate_inventory(num_positions: usize) -> Inventory {
    let mut inv = Inventory::new();

    for i in 0..num_positions {
        let cost = Cost::new(dec!(100.00) + Decimal::from(i as i32), "USD").with_date(date(
            2024,
            1,
            1 + (i % 28) as u32,
        ));

        inv.add(Position::with_cost(Amount::new(dec!(10), "STOCK"), cost));
    }

    inv
}

fn bench_inventory_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("inventory_add");

    for size in [10, 100, 1000] {
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter(|| {
                let mut inv = Inventory::new();
                for i in 0..size {
                    let cost = Cost::new(dec!(100.00) + Decimal::from(i), "USD");
                    inv.add(Position::with_cost(Amount::new(dec!(10), "STOCK"), cost));
                }
                black_box(inv)
            });
        });
    }

    group.finish();
}

fn bench_inventory_units(c: &mut Criterion) {
    let mut group = c.benchmark_group("inventory_units");

    for size in [10, 100, 1000] {
        let inv = generate_inventory(size);

        group.bench_with_input(BenchmarkId::from_parameter(size), &inv, |b, inv| {
            b.iter(|| black_box(inv.units("STOCK")));
        });
    }

    group.finish();
}

fn bench_inventory_book_value(c: &mut Criterion) {
    let mut group = c.benchmark_group("inventory_book_value");

    for size in [10, 100, 1000] {
        let inv = generate_inventory(size);

        group.bench_with_input(BenchmarkId::from_parameter(size), &inv, |b, inv| {
            b.iter(|| black_box(inv.book_value("STOCK")));
        });
    }

    group.finish();
}

fn bench_inventory_at_cost(c: &mut Criterion) {
    let mut group = c.benchmark_group("inventory_at_cost");

    for size in [10, 100, 1000] {
        let inv = generate_inventory(size);

        group.bench_with_input(BenchmarkId::from_parameter(size), &inv, |b, inv| {
            b.iter(|| black_box(inv.at_cost()));
        });
    }

    group.finish();
}

fn bench_reduce_fifo(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_fifo");

    for size in [10, 100, 500] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || generate_inventory(size),
                |mut inv| {
                    // Reduce half the positions
                    for _ in 0..size / 2 {
                        let _ =
                            inv.reduce(&Amount::new(dec!(-10), "STOCK"), None, BookingMethod::Fifo);
                    }
                    black_box(inv)
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_reduce_lifo(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_lifo");

    for size in [10, 100, 500] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || generate_inventory(size),
                |mut inv| {
                    // Reduce half the positions
                    for _ in 0..size / 2 {
                        let _ =
                            inv.reduce(&Amount::new(dec!(-10), "STOCK"), None, BookingMethod::Lifo);
                    }
                    black_box(inv)
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_reduce_strict(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_strict");

    for size in [10, 100, 500] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || generate_inventory(size),
                |mut inv| {
                    // Reduce with specific cost spec
                    let spec = CostSpec::empty().with_date(date(2024, 1, 1));
                    let _ = inv.reduce(
                        &Amount::new(dec!(-10), "STOCK"),
                        Some(&spec),
                        BookingMethod::Strict,
                    );
                    black_box(inv)
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_inventory_merge(c: &mut Criterion) {
    let mut group = c.benchmark_group("inventory_merge");

    for size in [10, 100, 500] {
        let inv1 = generate_inventory(size);
        let inv2 = generate_inventory(size);

        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &(inv1, inv2),
            |b, (inv1, inv2)| {
                b.iter_batched(
                    || inv1.clone(),
                    |mut inv| {
                        inv.merge(inv2);
                        black_box(inv)
                    },
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_inventory_add,
    bench_inventory_units,
    bench_inventory_book_value,
    bench_inventory_at_cost,
    bench_reduce_fifo,
    bench_reduce_lifo,
    bench_reduce_strict,
    bench_inventory_merge,
);
criterion_main!(benches);
