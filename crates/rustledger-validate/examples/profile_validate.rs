//! Deterministic cachegrind harness for the validation engine: many accounts,
//! many transactions, and periodic balance assertions — stressing account
//! open/close tracking + the per-transaction residual/tolerance + running-balance
//! machinery validation runs. Parallel to the `profile_pipeline` /
//! `profile_query` / `profile_booking` examples.
//!
//! ```text
//! cargo build -p rustledger-validate --profile profiling --example profile_validate
//! valgrind --tool=cachegrind ./target/profiling/examples/profile_validate 64 20000 3
//! ```
//!
//! Args: `<subaccounts> <transactions> <iterations>` (defaults `64 20000 5`).

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Balance, Directive, Open, Posting, Transaction};
use rustledger_validate::{ValidationOptions, ValidationSession};

fn date(y: i32, m: u32, d: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

fn generate(subaccounts: usize, txns: usize) -> Vec<Directive> {
    let mut d = Vec::new();
    d.push(Directive::Open(Open::new(
        date(2024, 1, 1),
        "Income:Salary",
    )));
    let accts: Vec<String> = (0..subaccounts)
        .map(|k| format!("Assets:Bank:Sub{k}"))
        .collect();
    for a in &accts {
        d.push(Directive::Open(Open::new(date(2024, 1, 1), a.clone())));
    }
    let mut totals = vec![rust_decimal::Decimal::ZERO; subaccounts];
    for i in 0..txns {
        let k = i % subaccounts;
        let amount = dec!(10.00) + rust_decimal::Decimal::from((i % 50) as i64);
        let month = (i % 12 + 1) as u32;
        let day = (i % 28 + 1) as u32;
        let txn = Transaction::new(date(2024, month, day), format!("Deposit {i}"))
            .with_flag('*')
            .with_synthesized_posting(Posting::new(accts[k].clone(), Amount::new(amount, "USD")))
            .with_synthesized_posting(Posting::new("Income:Salary", Amount::new(-amount, "USD")));
        d.push(Directive::Transaction(txn));
        totals[k] += amount;
        // Periodic balance assertion on the touched subaccount (exercises the
        // balance machinery; date ordering means not all will match, which is
        // fine — the residual/balance computation runs either way).
        if i % 100 == 99 {
            d.push(Directive::Balance(Balance::new(
                date(2024, month, day),
                accts[k].clone(),
                Amount::new(totals[k], "USD"),
            )));
        }
    }
    d
}

fn validate(directives: &[Directive]) -> usize {
    let today = rustledger_core::naive_date(2030, 1, 1).unwrap();
    let session = ValidationSession::new(ValidationOptions::default());
    let (session, mut errors) = session.run_early(directives, today);
    let (session, late) = session.run_late(directives, today);
    errors.extend(late);
    errors.extend(session.finalize());
    errors.len()
}

fn main() {
    let mut a = std::env::args().skip(1);
    let subaccounts: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(64);
    let txns: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(20_000);
    let iters: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(5);
    if subaccounts == 0 {
        eprintln!("error: <subaccounts> must be > 0");
        std::process::exit(2);
    }

    let directives = generate(subaccounts, txns);
    let mut sink = 0usize;
    for _ in 0..iters {
        sink = sink.wrapping_add(validate(std::hint::black_box(&directives)));
    }
    eprintln!(
        "validate profile: {subaccounts} subaccts x {txns} txns x {iters} iters; dirs={} err_sink={sink}",
        directives.len()
    );
}
