//! Validation performance benchmarks.
//!
//! Run with: cargo bench -p rustledger-validate

#![allow(missing_docs)]

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

use rust_decimal_macros::dec;
use rustledger_core::NaiveDate;
use rustledger_core::{Amount, Balance, Directive, Open, Posting, Transaction};
use rustledger_validate::{ValidationError, ValidationOptions, ValidationSession};

/// Bench helper mirroring the deleted public `validate()`. Chains
/// Early + Late + finalize through a single session.
fn validate(directives: &[Directive]) -> Vec<ValidationError> {
    let today = rustledger_core::naive_date(2030, 1, 1).unwrap();
    let session = ValidationSession::new(ValidationOptions::default());
    let (session, mut errors) = session.run_early(directives, today);
    let (session, late_errs) = session.run_late(directives, today);
    errors.extend(late_errs);
    errors.extend(session.finalize());
    errors
}

#[allow(clippy::missing_const_for_fn)]
fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// Generate a valid ledger with account opens, transactions, and balance assertions.
fn generate_valid_ledger(num_transactions: usize) -> Vec<Directive> {
    let mut directives = Vec::new();

    // Open accounts
    let accounts = vec![
        "Assets:Bank:Checking",
        "Assets:Bank:Savings",
        "Expenses:Food",
        "Expenses:Transport",
        "Expenses:Utilities",
        "Income:Salary",
    ];

    for account in accounts {
        directives.push(Directive::Open(Open::new(date(2024, 1, 1), account)));
    }

    // Generate transactions
    let expense_accounts = ["Expenses:Food", "Expenses:Transport", "Expenses:Utilities"];
    let mut day = 1u32;
    let mut month = 1u32;

    for i in 0..num_transactions {
        let expense = expense_accounts[i % expense_accounts.len()];
        let amount = dec!(10.00) + rust_decimal::Decimal::from(i as i32 % 50);

        let txn = Transaction::new(date(2024, month, day), format!("Transaction {i}"))
            .with_flag('*')
            .with_synthesized_posting(Posting::new(expense, Amount::new(amount, "USD")))
            .with_synthesized_posting(Posting::new(
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
                break;
            }
        }
    }

    directives
}

/// Generate a ledger with some validation errors.
fn generate_ledger_with_errors(num_transactions: usize) -> Vec<Directive> {
    let mut directives = Vec::new();

    // Only open some accounts
    directives.push(Directive::Open(Open::new(
        date(2024, 1, 1),
        "Assets:Bank:Checking",
    )));

    // Generate transactions (some will have unopened accounts)
    for i in 0..num_transactions {
        let expense = if i % 2 == 0 {
            "Expenses:Food" // Not opened - will error
        } else {
            "Assets:Bank:Checking"
        };

        let txn = Transaction::new(date(2024, 1, 15), format!("Transaction {i}"))
            .with_flag('*')
            .with_synthesized_posting(Posting::new(expense, Amount::new(dec!(50.00), "USD")))
            .with_synthesized_posting(Posting::new(
                "Assets:Bank:Checking",
                Amount::new(dec!(-50.00), "USD"),
            ));

        directives.push(Directive::Transaction(txn));
    }

    directives
}

fn bench_validate_valid(c: &mut Criterion) {
    let mut group = c.benchmark_group("validate_valid");

    for size in [100, 500, 1000, 5000] {
        let directives = generate_valid_ledger(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &directives,
            |b, directives| {
                b.iter(|| std::hint::black_box(validate(std::hint::black_box(directives))));
            },
        );
    }

    group.finish();
}

fn bench_validate_with_errors(c: &mut Criterion) {
    let mut group = c.benchmark_group("validate_with_errors");

    for size in [100, 500, 1000] {
        let directives = generate_ledger_with_errors(size);
        group.throughput(Throughput::Elements(size as u64));

        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &directives,
            |b, directives| {
                b.iter(|| std::hint::black_box(validate(std::hint::black_box(directives))));
            },
        );
    }

    group.finish();
}

fn bench_validate_balance_assertions(c: &mut Criterion) {
    let mut group = c.benchmark_group("validate_balance_assertions");

    for size in [10u32, 50, 100] {
        let mut directives = Vec::new();

        // Open accounts
        directives.push(Directive::Open(Open::new(
            date(2024, 1, 1),
            "Assets:Bank:Checking",
        )));
        directives.push(Directive::Open(Open::new(
            date(2024, 1, 1),
            "Income:Salary",
        )));

        // Add transactions
        let mut running_total = rust_decimal::Decimal::ZERO;
        for i in 0..size {
            let amount = dec!(100.00);
            running_total += amount;

            // Calculate day, ensuring it stays within valid range
            let day = 2 + (i % 27);

            let txn = Transaction::new(date(2024, 1, day), format!("Deposit {i}"))
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(amount, "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Income:Salary",
                    Amount::new(-amount, "USD"),
                ));

            directives.push(Directive::Transaction(txn));
        }

        // Add balance assertion
        directives.push(Directive::Balance(Balance::new(
            date(2024, 12, 31),
            "Assets:Bank:Checking",
            Amount::new(running_total, "USD"),
        )));

        group.throughput(Throughput::Elements(u64::from(size)));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &directives,
            |b, directives| {
                b.iter(|| std::hint::black_box(validate(std::hint::black_box(directives))));
            },
        );
    }

    group.finish();
}

/// Scale the (accounts × balance-assertions) product that
/// `bench_validate_balance_assertions` fixes at 2×1. A parent balance assertion
/// sums the whole subtree, so this is the dimension a quadratic
/// `sum_account_and_subaccounts` regression would surface in — and the one the
/// prefix index removes. Each `accounts` value runs `assertions` parent
/// assertions, each summing every sub-account.
fn bench_validate_subaccount_balance_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("validate_subaccount_balance_scaling");

    let assertions = 50u32;
    for accounts in [32u32, 64, 128] {
        let mut directives = Vec::new();
        directives.push(Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")));
        directives.push(Directive::Open(Open::new(
            date(2024, 1, 1),
            "Income:Salary",
        )));
        for a in 0..accounts {
            directives.push(Directive::Open(Open::new(
                date(2024, 1, 1),
                format!("Assets:Bank:Sub{a}"),
            )));
        }

        // Fund each sub-account once.
        let per = dec!(10.00);
        for a in 0..accounts {
            let txn = Transaction::new(date(2024, 1, 2), format!("fund {a}"))
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    format!("Assets:Bank:Sub{a}"),
                    Amount::new(per, "USD"),
                ))
                .with_synthesized_posting(Posting::new("Income:Salary", Amount::new(-per, "USD")));
            directives.push(Directive::Transaction(txn));
        }

        // Many assertions on the PARENT — each sums all `accounts` sub-accounts.
        let total = per * rust_decimal::Decimal::from(accounts);
        for i in 0..assertions {
            let day = 3 + (i % 27);
            directives.push(Directive::Balance(Balance::new(
                date(2024, 1, day),
                "Assets:Bank",
                Amount::new(total, "USD"),
            )));
        }

        group.throughput(Throughput::Elements(
            u64::from(accounts) * u64::from(assertions),
        ));
        group.bench_with_input(
            BenchmarkId::from_parameter(accounts),
            &directives,
            |b, directives| {
                b.iter(|| std::hint::black_box(validate(std::hint::black_box(directives))));
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_validate_valid,
    bench_validate_with_errors,
    bench_validate_balance_assertions,
    bench_validate_subaccount_balance_scaling,
);
criterion_main!(benches);
