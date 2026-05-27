//! Baseline benchmarks for the v0.16.0 perf-sensitive paths.
//!
//! Targets the `load_raw + process` pipeline with the native-plugin pass
//! enabled. This is the path that the v0.16.0 `DirectiveWrapper` redesign
//! will optimize: the N×M wrapper-rebuild loop in `run_plugins` dominates
//! at scale.
//!
//! Each timed iteration calls `load_raw(path) + process(raw, opts)` —
//! `LoadResult` is not `Clone`, so hoisting `load_raw` out of the closure
//! would require a non-trivial public-API change. Parse cost is included
//! in every measurement as a constant, so the *delta* before/after the
//! refactor still reflects the wrapper-rebuild speedup correctly.
//!
//! The matrix is (size: 1k, 10k, 100k) × (plugin count: 0, 1, 5).
//!
//! The 100k row is intentionally heavier than the standard `pipeline_bench`
//! — the N×M cost is invisible below ~10k directives. This bench is NOT
//! wired into PR CI (it would blow the 15-minute budget); run it locally
//! before and after structural changes:
//!
//! ```sh
//! cargo bench --bench v016_baseline -- --save-baseline pre
//! # ... apply structural change ...
//! cargo bench --bench v016_baseline -- --baseline pre
//! ```
//!
//! The exit criterion for v0.16.0 Wave 3 is ≥3x speedup on
//! `v016_load_process/100k_5plugins`.

#![allow(missing_docs)]

use std::io::Write;
use std::time::Duration;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

use rustledger_loader::{LoadOptions, load_raw, process};

/// Five pure-validation native plugins. Chosen because they don't synthesize
/// directives (so the bench measures wrapper-conversion cost, not the synth
/// pipeline) and don't share state across calls (so each plugin's pass is
/// independent work).
const PLUGINS_5: &[&str] = &[
    "check_commodity",
    "nounused",
    "onecommodity",
    "noduplicates",
    "check_closing",
];

/// Generate a USD-only ledger with `num_transactions` transactions. Each
/// transaction is one of 5 expense categories, signed against the single
/// `Assets:Bank:Checking` account. Single currency keeps the booking step
/// simple and the plugin validators focused on the wrapper cost rather
/// than on currency interactions. Every opened account is referenced —
/// the `nounused` plugin is in the active set, and stale opens would
/// throw a warning on every iteration.
fn generate_ledger(num_transactions: usize) -> String {
    let mut s = String::with_capacity(num_transactions * 120);

    s.push_str("option \"title\" \"v0.16 baseline\"\n");
    s.push_str("option \"operating_currency\" \"USD\"\n\n");

    for acct in [
        "Assets:Bank:Checking",
        "Expenses:Food",
        "Expenses:Coffee",
        "Expenses:Groceries",
        "Expenses:Transport",
        "Expenses:Utilities",
        "Equity:Opening",
    ] {
        s.push_str(&format!("2020-01-01 open {acct} USD\n"));
    }
    s.push_str("2020-01-01 commodity USD\n\n");

    s.push_str("2020-01-01 * \"Opening balance\"\n");
    s.push_str("  Assets:Bank:Checking  1000000.00 USD\n");
    s.push_str("  Equity:Opening\n\n");

    let categories = ["Food", "Coffee", "Groceries", "Transport", "Utilities"];
    let payees = ["Store A", "Store B", "Cafe", "Gas Station", "Supermarket"];
    let (mut day, mut month, mut year) = (2u32, 1u32, 2020u32);

    for i in 0..num_transactions {
        let category = categories[i % categories.len()];
        let payee = payees[i % payees.len()];
        let amount = 10.0 + (i % 100) as f64;

        s.push_str(&format!(
            "{year:04}-{month:02}-{day:02} * \"{payee}\" \"Transaction {i}\"\n"
        ));
        s.push_str(&format!("  Expenses:{category}  {amount:.2} USD\n"));
        s.push_str("  Assets:Bank:Checking\n\n");

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

    s
}

/// Write `content` to a tempfile and return both the dir (kept alive) and the
/// path. Drop the dir to clean up.
fn write_tempfile(content: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("ledger.beancount");
    let mut f = std::fs::File::create(&path).expect("create tempfile");
    f.write_all(content.as_bytes()).expect("write tempfile");
    (dir, path)
}

fn run_process(path: &std::path::Path, plugin_names: &[&str]) {
    let raw = load_raw(path).expect("load_raw");
    let opts = LoadOptions {
        extra_plugins: plugin_names
            .iter()
            .map(|s| rustledger_loader::ExtraPlugin {
                name: (*s).to_string(),
                config: None,
            })
            .collect(),
        ..LoadOptions::default()
    };
    let ledger = process(raw, &opts).expect("process");
    std::hint::black_box(ledger);
}

fn bench_process_matrix(c: &mut Criterion) {
    let mut group = c.benchmark_group("v016_load_process");

    // (label, size, sample_size, measurement_secs)
    let sizes: &[(&str, usize, usize, u64)] = &[
        ("1k", 1_000, 50, 10),
        ("10k", 10_000, 20, 30),
        ("100k", 100_000, 10, 90),
    ];

    let plugin_configs: &[(&str, &[&str])] = &[
        ("0plugins", &[]),
        ("1plugin", &PLUGINS_5[..1]),
        ("5plugins", PLUGINS_5),
    ];

    for (size_label, n, sample_size, measure_s) in sizes {
        let ledger = generate_ledger(*n);
        let (_dir, path) = write_tempfile(&ledger);

        group.sample_size(*sample_size);
        group.measurement_time(Duration::from_secs(*measure_s));
        group.throughput(Throughput::Elements(*n as u64));

        for (plugin_label, plugins) in plugin_configs {
            let id = BenchmarkId::from_parameter(format!("{size_label}_{plugin_label}"));
            group.bench_with_input(id, &path, |b, p| {
                b.iter(|| run_process(p, plugins));
            });
        }
    }

    group.finish();
}

criterion_group!(benches, bench_process_matrix);
criterion_main!(benches);
