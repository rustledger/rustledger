# CI/CD Testing Strategy

This document describes the testing strategy and CI/CD pipeline for rustledger.

## Test Categories

### 1. Unit Tests

Location: `crates/*/src/**/*.rs` (inline `#[test]`)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_amount_addition() {
        let a = Amount::new(dec!(100), "USD");
        let b = Amount::new(dec!(50), "USD");
        assert_eq!(a + b, Amount::new(dec!(150), "USD"));
    }
}
```

**Run**: `cargo test --lib`

### 2. Integration Tests

Location: `crates/*/tests/*.rs`

```rust
// crates/beancount-parser/tests/parse_fixtures.rs
#[test]
fn test_parse_syntax_edge_cases() {
    let content = include_str!("../../spec/fixtures/syntax-edge-cases.beancount");
    let result = parse(content);
    assert!(result.errors.is_empty());
}
```

**Run**: `cargo test --test '*'`

### 3. Golden Tests (Fixture-Based)

Location: `spec/fixtures/`

Compare parser output against expected results:

```rust
#[test]
fn test_lima_fixtures() {
    for entry in glob("spec/fixtures/lima-tests/*.beancount").unwrap() {
        let path = entry.unwrap();
        let expected = read_expected(&path);  // .txtpb file
        let actual = parse_file(&path);
        assert_eq!(actual, expected, "Failed: {:?}", path);
    }
}
```

**Run**: `cargo test --test fixtures`

### 4. Property Tests

Location: `crates/*/tests/prop_*.rs`

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_parse_roundtrip(ledger in arb_ledger()) {
        let printed = print(&ledger);
        let reparsed = parse(&printed).unwrap();
        prop_assert_eq!(ledger, reparsed);
    }
}
```

**Run**: `cargo test --features proptest`

### 5. Compatibility Tests

Compare output with Python beancount:

```bash
#!/bin/bash
# tests/compat/run.sh

for file in spec/fixtures/examples/*.beancount; do
    python_out=$(python -m beancount.scripts.check "$file" 2>&1)
    rust_out=$(cargo run --release -- check "$file" 2>&1)

    if ! diff <(echo "$python_out") <(echo "$rust_out"); then
        echo "FAIL: $file"
        exit 1
    fi
done
```

**Run**: `./tests/compat/run.sh`

### 6. Benchmark Tests

Location: `benches/*.rs`

```rust
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_parse(c: &mut Criterion) {
    let source = include_str!("../spec/fixtures/examples/example.beancount");
    c.bench_function("parse_example", |b| {
        b.iter(|| parse(source))
    });
}

criterion_group!(benches, bench_parse);
criterion_main!(benches);
```

**Run**: `cargo bench`

### 7. Fuzz Tests

Location: `fuzz/fuzz_targets/*.rs`

```rust
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = beancount_parser::parse(s);
    }
});
```

**Run**: `cargo +nightly fuzz run fuzz_parser`

## CI Pipeline

### GitHub Actions Workflow

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

env:
  CARGO_TERM_COLOR: always
  RUSTFLAGS: -Dwarnings

jobs:
  check:
    name: Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo check --all-targets --all-features

  test:
    name: Test
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo test --all-features

  test-proptest:
    name: Property Tests
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo test --features proptest
        env:
          PROPTEST_CASES: 1000

  clippy:
    name: Clippy
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: clippy
      - uses: Swatinem/rust-cache@v2
      - run: cargo clippy --all-targets --all-features

  fmt:
    name: Format
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt
      - run: cargo fmt --all -- --check

  docs:
    name: Docs
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo doc --no-deps --all-features
        env:
          RUSTDOCFLAGS: -Dwarnings

  compat:
    name: Compatibility
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - uses: actions/setup-python@v5
        with:
          python-version: '3.11'
      - run: pip install beancount
      - run: cargo build --release
      - run: ./tests/compat/run.sh

  wasm:
    name: WASM Build
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          targets: wasm32-unknown-unknown
      - uses: Swatinem/rust-cache@v2
      - run: cargo build --target wasm32-unknown-unknown --release -p beancount-wasm

  bench:
    name: Benchmarks
    runs-on: ubuntu-latest
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo bench -- --save-baseline main
      - uses: actions/upload-artifact@v4
        with:
          name: bench-results
          path: target/criterion

  coverage:
    name: Coverage
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: llvm-tools-preview
      - uses: Swatinem/rust-cache@v2
      - uses: taiki-e/install-action@cargo-llvm-cov
      - run: cargo llvm-cov --all-features --lcov --output-path lcov.info
      - uses: codecov/codecov-action@v4
        with:
          files: lcov.info
```

## Test Organization

```
rustledger/
├── crates/
│   ├── beancount-core/
│   │   ├── src/
│   │   │   ├── lib.rs          # Unit tests inline
│   │   │   └── ...
│   │   └── tests/
│   │       └── integration.rs  # Integration tests
│   ├── beancount-parser/
│   │   ├── src/
│   │   └── tests/
│   │       ├── fixtures.rs     # Golden tests
│   │       └── prop_parse.rs   # Property tests
│   └── ...
├── tests/
│   ├── compat/
│   │   ├── run.sh              # Compatibility test runner
│   │   └── compare.py          # Output comparison
│   └── e2e/
│       └── cli.rs              # End-to-end CLI tests
├── benches/
│   ├── parse.rs
│   ├── booking.rs
│   └── query.rs
├── fuzz/
│   ├── Cargo.toml
│   └── fuzz_targets/
│       ├── fuzz_parser.rs
│       └── fuzz_query.rs
└── spec/
    └── fixtures/               # Test data
```

## Running Tests Locally

### All Tests

```bash
# Quick check
cargo test

# With property tests (more iterations)
PROPTEST_CASES=10000 cargo test --features proptest

# With coverage
cargo llvm-cov --html
open target/llvm-cov/html/index.html
```

### Specific Tests

```bash
# Single crate
cargo test -p beancount-parser

# Single test
cargo test test_parse_transaction

# With output
cargo test -- --nocapture

# Ignored tests (slow)
cargo test -- --ignored
```

### Benchmarks

```bash
# Run all benchmarks
cargo bench

# Specific benchmark
cargo bench parse

# Compare with baseline
cargo bench -- --baseline main
```

### Fuzzing

```bash
# Install cargo-fuzz
cargo install cargo-fuzz

# Run fuzzer
cd fuzz
cargo +nightly fuzz run fuzz_parser

# With corpus
cargo +nightly fuzz run fuzz_parser -- -max_len=10000
```

## Test Data Management

### Fixture Downloads

```bash
# Download test vectors
./scripts/fetch-test-vectors.sh

# Verify fixtures
cargo test --test fixtures
```

### Corpus Management

```bash
# Export fuzzing corpus
cargo +nightly fuzz cmin fuzz_parser

# Import regression tests from corpus
cp fuzz/corpus/fuzz_parser/* spec/fixtures/fuzz-regressions/
```

## Quality Gates

### Pre-Merge Requirements

- [ ] All tests pass
- [ ] No clippy warnings
- [ ] Code formatted
- [ ] Documentation builds
- [ ] Coverage doesn't decrease
- [ ] Benchmarks don't regress >10%

### Release Requirements

- [ ] All pre-merge requirements
- [ ] Compatibility tests pass
- [ ] WASM builds successfully
- [ ] Fuzzing finds no new issues (1 hour run)
- [ ] Changelog updated
