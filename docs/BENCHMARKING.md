# Benchmarking Guide

This document describes rustledger's benchmarking infrastructure, how to run benchmarks, and how to interpret results.

## Overview

rustledger uses multiple benchmarking systems for different purposes:

| System | Purpose | When to Use |
|--------|---------|-------------|
| **Criterion** | Micro-benchmarks for components | Local development, PR validation |
| **CI Comparison** | Compare against beancount/ledger/hledger | Nightly tracking, release validation |
| **Local Script** | Quick full-tool comparison | Before submitting performance PRs |

## Quick Start

### Micro-benchmarks (Criterion)

Run benchmarks for a specific crate:

```bash
# Core inventory operations
cargo bench -p rustledger-core

# Parser performance
cargo bench -p rustledger-parser

# BQL query engine
cargo bench -p rustledger-query

# Validation engine
cargo bench -p rustledger-validate

# Full pipeline (parse → validate → interpolate)
cargo bench -p rustledger
```

Run a specific benchmark:

```bash
cargo bench -p rustledger-parser -- parse_large
cargo bench -p rustledger-core -- inventory_merge
```

Results are saved to `target/criterion/` with HTML reports.

### Full Tool Comparison (Local)

Compare rustledger against beancount, ledger, and hledger:

```bash
# Enter benchmark environment (downloads comparison tools)
nix develop .#bench

# Run comparison benchmark (default: 10,000 transactions)
./scripts/bench.sh

# Custom transaction count
./scripts/bench.sh 50000
```

## Benchmark Systems in Detail

### 1. Criterion Micro-benchmarks

Located in `crates/*/benches/`. Each crate has focused benchmarks:

#### rustledger-core (`inventory_bench.rs`)
- `inventory_add` - Adding positions to inventory
- `inventory_merge` - Merging two inventories
- `reduce_fifo/lifo/strict` - Cost basis reduction methods
- `inventory_units/book_value/at_cost` - Query operations

#### rustledger-parser (`parser_bench.rs`)
- `parse_small/medium/large` - Parsing different file sizes
- `parse_scaling` - Scaling behavior (10→1000 transactions)
- `tokenize_*` - Lexer-only performance
- `tokenize_vs_parse` - Lexer vs full parser comparison

#### rustledger-query (`query_bench.rs`)
- `query_simple_select` - Basic SELECT queries
- `query_where` - WHERE clause with regex
- `query_group_by` - Aggregation queries
- `query_balances` - Built-in BALANCES query
- `query_scaling` - Query scaling (100→5000 directives)

#### rustledger-validate (`validate_bench.rs`)
- `validate_valid` - Valid ledgers without errors
- `validate_with_errors` - Ledgers with validation errors
- `validate_balance_assertions` - Balance assertion checking

#### rustledger (`pipeline_bench.rs`)
- `pipeline_parse` - Parse-only baseline
- `pipeline_parse_validate` - Parse + validate
- `pipeline_full` - Full pipeline including interpolation
- `throughput` - Raw transaction throughput (10K transactions)

### 2. CI Comparison Benchmarks

**Workflow:** `.github/workflows/bench.yml`

**Triggers:**
- Nightly at 2 AM UTC
- On release publication
- Manual via `workflow_dispatch`

**What it measures:**
1. **Validation benchmark** - Parse + check a ledger
2. **Balance benchmark** - Parse + compute balances

**Tools compared:**
- rustledger (Rust)
- beancount (Python)
- ledger (C++)
- hledger (Haskell)

**Test data:** 10,000 synthetic transactions generated deterministically (seed=42)

**Results location:**
- Branch: `benchmarks`
- History: `.github/badges/validation-history.json`, `.github/badges/balance-history.json`
- Charts: `.github/badges/*.svg`

### 3. Local Comparison Script

**Script:** `scripts/bench.sh`

Mirrors the CI workflow for local development. Requires the benchmark nix shell:

```bash
nix develop .#bench
./scripts/bench.sh [transaction_count]
```

The script:
1. Generates test ledgers (`.beancount` and `.ledger` formats)
2. Runs hyperfine with 10 iterations, 3 warmups
3. Outputs JSON and formatted summary

## Input Size Guidelines

When adding benchmarks, use sizes appropriate to the operation's complexity:

### Standard Transaction/Directive Sizes

| Category | Size | Use Case |
|----------|------|----------|
| tiny | 100 | Quick iteration during development |
| small | 1,000 | Default for CI and local testing |
| medium | 5,000 | Scaling behavior verification |
| large | 10,000 | Match CI comparison benchmark |
| xlarge | 50,000 | Stress testing and scaling limits |

### Domain-Specific Sizes

Different components have different complexity characteristics:

| Component | Recommended Sizes | Reasoning |
|-----------|-------------------|-----------|
| **Inventory** | [10, 100, 500, 1000] | Operations can be O(n²) in worst case |
| **Parser** | [10, 100, 500, 1000] | O(n) with lexer overhead |
| **Query** | [100, 500, 1000, 5000] | O(n) with aggregation |
| **Validate** | [100, 500, 1000, 5000] | O(n) per validation pass |
| **Pipeline** | [100, 500, 1000] + 10K throughput | End-to-end measurement |

Use the `_scaling` benchmark pattern for algorithmic complexity analysis:

```rust
fn bench_operation_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("operation_scaling");

    // Use sizes appropriate to the operation's complexity
    for size in [100, 500, 1000, 5000] {
        let data = generate_test_data(size);
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &data,
            |b, data| b.iter(|| operation(data)),
        );
    }

    group.finish();
}
```

## Adding New Benchmarks

### Criterion Benchmark

1. Add to the appropriate `benches/*.rs` file
2. Use `BenchmarkGroup` for related benchmarks
3. Include throughput metrics where applicable
4. Test multiple input sizes

```rust
fn bench_my_feature(c: &mut Criterion) {
    let mut group = c.benchmark_group("my_feature");

    for size in [100, 1000, 5000, 10000] {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(
            BenchmarkId::new("operation", size),
            &size,
            |b, &size| {
                let data = generate_test_data(size);
                b.iter(|| my_operation(&data))
            },
        );
    }

    group.finish();
}
```

### CI Comparison Benchmark

For changes to the CI benchmark workflow, modify `.github/workflows/bench.yml`.
Consider adding new benchmarks only if they provide meaningful cross-tool comparison.

## Interpreting Results

### Criterion Output

```
my_benchmark/1000       time:   [1.2345 ms 1.2456 ms 1.2567 ms]
                        thrpt:  [795.74 Kelem/s 802.82 Kelem/s 810.05 Kelem/s]
                        change: [-2.5% -1.2% +0.1%] (p = 0.12 > 0.05)
                        No change in performance detected.
```

- **time**: [lower bound, estimate, upper bound] with 95% confidence
- **thrpt**: Throughput (elements per second)
- **change**: Comparison to previous run
- **p-value**: Statistical significance (< 0.05 = significant)

### CI Benchmark Results

View the benchmark charts on the `benchmarks` branch:
- `validation-chart.svg` - Validation performance comparison
- `balance-chart.svg` - Balance computation comparison
- `validation-chart.vega.json` - Vega spec (editable)
- `balance-chart.vega.json` - Vega spec (editable)

**Local chart generation:**
```bash
# Generate Vega specs from history
./scripts/generate-bench-charts.py

# Generate with custom values
./scripts/generate-bench-charts.py --rustledger 32 --ledger 65 --hledger 540 --beancount 880

# Render to SVG (requires: npm install -g vega vega-cli)
./scripts/generate-bench-charts.py --render
```

## Performance Regression Detection

The CI benchmark workflow includes automatic regression detection:

- **Threshold:** 15% regression triggers a warning
- **Baseline:** Compared against the previous nightly run
- **Scope:** Only rustledger is checked (comparison tools vary independently)

To investigate a regression:
1. Check the benchmark history charts
2. Run local Criterion benchmarks to isolate the component
3. Use `cargo flamegraph` for profiling (requires nightly shell)

## Nix Development Shells

### Default Shell (`nix develop`)
Standard development with Rust toolchain and pre-commit hooks.

### Benchmark Shell (`nix develop .#bench`)
Includes:
- All comparison tools (beancount, ledger, hledger)
- hyperfine for timing
- Python with matplotlib for charts
- Build dependencies for ledger

### Nightly Shell (`nix develop .#nightly`)
For fuzzing and nightly-only features:
- cargo-fuzz
- Nightly Rust toolchain

## Troubleshooting

### Criterion results vary too much

Ensure a stable environment:
```bash
# Disable CPU frequency scaling (Linux)
sudo cpupower frequency-set -g performance

# Close other applications
# Run multiple times to verify consistency
```

### CI benchmark shows regression but local doesn't

CI runners have different characteristics than local machines:
- Shared resources may cause variance
- Check if other tools also show variance
- Look at the trend over multiple days, not single runs

### Missing comparison tools in bench shell

The benchmark shell auto-downloads tools on first use:
```bash
# Force re-download
rm -rf .bench-tools
nix develop .#bench
```

## See Also

- [TESTING.md](TESTING.md) - Test organization and fixtures
- [CONTRIBUTING.md](../CONTRIBUTING.md) - Development workflow
- [Criterion Documentation](https://bheisler.github.io/criterion.rs/book/)
