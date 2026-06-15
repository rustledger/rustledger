# Testing Guide

This document describes rustledger's testing infrastructure, how to run tests, and how to add new tests.

## Overview

rustledger uses multiple testing systems for different purposes:

| System | Purpose | When to Use |
|--------|---------|-------------|
| **Unit Tests** | Test individual functions/modules | During development |
| **Integration Tests** | Test crate-level behavior | Before PRs |
| **Property Tests** | Verify invariants with random inputs | Algorithm changes |
| **TLA+ Specs** | Formal verification of critical algorithms | Booking/inventory changes |
| **Compatibility Tests** | Compare against Python beancount | Nightly, major changes |

## Quick Start

### Run All Tests

```bash
# All tests (default features)
cargo test

# All tests with all features
cargo test --all-features

# Specific crate
cargo test -p rustledger-core
cargo test -p rustledger-parser
cargo test -p rustledger-query
```

### Run Specific Test Types

```bash
# Unit tests only (skip integration)
cargo test --lib

# Integration tests only
cargo test --test '*'

# Property tests (longer running)
cargo test --all-features proptest

# Run tests matching a pattern
cargo test inventory
cargo test parse_transaction
```

## Test Organization

### Directory Structure

```
rustledger/
├── crates/
│   ├── rustledger-core/
│   │   ├── src/
│   │   │   └── inventory.rs        # Unit tests in #[cfg(test)] modules
│   │   └── tests/
│   │       ├── property_tests.rs   # Proptest-based tests
│   │       ├── tla_proptest.rs     # TLA+ invariant verification
│   │       └── tla_fifo_bug_test.rs
│   ├── rustledger-parser/
│   │   └── tests/
│   │       └── parser_integration_test.rs
│   ├── rustledger-query/
│   │   └── tests/
│   │       └── bql_integration_test.rs
│   ├── rustledger-validate/
│   │   └── tests/
│   │       ├── validation_integration_test.rs
│   │       └── tla_proptest.rs
│   ├── rustledger-loader/
│   │   └── tests/
│   │       ├── loader_test.rs
│   │       └── fixtures/           # Per-crate fixtures
│   ├── rustledger-plugin/
│   │   └── tests/
│   │       └── native_plugins_test.rs
│   └── rustledger/
│       └── tests/
│           ├── integration_test.rs
│           └── fixture_tests.rs
├── tests/
│   ├── fixtures/                   # Parser and example fixtures
│   │   ├── booking-scenarios.beancount
│   │   ├── validation-errors.beancount
│   │   ├── syntax-edge-cases.beancount
│   │   ├── examples/
│   │   ├── lima-tests/
│   │   └── python-plugins/
│   ├── compatibility/
│   │   ├── files/                  # ~800 files (gitignored, fetched on demand;
│   │   │                           #   only files/plugins/ is committed)
│   │   ├── README.md
│   │   ├── sources.toml
│   │   ├── bql-queries.toml
│   │   └── exclusions.toml
│   ├── baselines/
│   └── regressions/
├── spec/
│   └── tla/                        # TLA+ specifications (19 specs)
│       ├── FIFOCorrect.tla
│       ├── Conservation.tla
│       └── ...
└── scripts/
    ├── compat-bql-test.py          # BQL compatibility tests
    └── fetch-compat-test-files.sh  # Download full test suite
```

### Test Types by Crate

| Crate | Unit | Integration | Property | TLA+ |
|-------|:----:|:-----------:|:--------:|:----:|
| rustledger-core | Yes | - | Yes | Yes |
| rustledger-parser | Yes | Yes | Yes | - |
| rustledger-query | Yes | Yes | Yes | Yes |
| rustledger-validate | Yes | Yes | Yes | Yes |
| rustledger-loader | Yes | Yes | - | - |
| rustledger-plugin | Yes | Yes | Yes | Yes |
| rustledger-booking | Yes | Yes | Yes | Yes |
| rustledger | Yes | Yes | - | - |

## Test Systems in Detail

### 1. Unit Tests

Located in `#[cfg(test)]` modules within source files. Test individual functions and edge cases.

```rust
// In src/inventory.rs
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_position() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));
        assert_eq!(inv.len(), 1);
    }
}
```

**Run:**

```bash
cargo test -p rustledger-core inventory
```

### 2. Integration Tests

Located in `crates/*/tests/`. Test crate-level functionality with realistic inputs.

**Key integration tests:**

- `parser_integration_test.rs` - Parser with snapshot testing (insta)
- `bql_integration_test.rs` - BQL query execution
- `validation_integration_test.rs` - Full validation pipeline
- `loader_test.rs` - File loading and includes
- `native_plugins_test.rs` - Plugin registration and execution

**Run:**

```bash
cargo test -p rustledger-parser --test parser_integration_test
cargo test -p rustledger-query --test bql_integration_test
```

### 3. Property Tests (Proptest)

Use random inputs to verify invariants hold across many cases.

Located in:

- `crates/rustledger-core/tests/property_tests.rs`
- `crates/rustledger-core/tests/tla_proptest.rs`
- `crates/rustledger-validate/tests/tla_proptest.rs`
- `crates/*/tests/pipeline_invariants.rs` — pipeline invariant property suites
  (parser, query, validate, booking, plugin)
- `crates/{rustledger-query,rustledger-plugin,rustledger-booking}/tests/tla_proptest.rs`

**Example:**

```rust
proptest! {
    #[test]
    fn inventory_units_always_non_negative(
        amounts in prop::collection::vec(1i64..100, 1..10)
    ) {
        let mut inv = Inventory::new();
        for a in amounts {
            inv.add(Position::simple(Amount::new(Decimal::from(a), "USD")));
        }
        // Invariant: all positions have positive units
        for pos in inv.iter() {
            prop_assert!(pos.units().number() > Decimal::ZERO);
        }
    }
}
```

**Run:**

```bash
cargo test -p rustledger-core proptest
cargo test -p rustledger-validate proptest
```

### 4. TLA+ Model Checking

Formal specifications in `spec/tla/` verify critical algorithms:

| Spec | Purpose |
|------|---------|
| `Conservation.tla` | Value conservation in transactions |
| `DoubleEntry.tla` | Double-entry bookkeeping invariant |
| `FIFOCorrect.tla` | FIFO booking method correctness |
| `LIFOCorrect.tla` | LIFO booking method correctness |
| `AVERAGECorrect.tla` | Average cost booking |
| `Interpolation.tla` | Missing amount interpolation |
| `ValidationCorrect.tla` | Validation rules |

**Run locally (requires Java):**

```bash
# In nix develop
java -jar ~/tla2tools.jar -config spec/tla/Conservation.cfg spec/tla/Conservation.tla
```

**CI:** Runs on changes to `spec/tla/`, `inventory.rs`, or booking code.

**Proptest integration:** TLA+ invariants are also verified via proptest:

```bash
cargo test -p rustledger-core tla_proptest
```

### 5. Compatibility Tests

Compare rustledger against Python beancount to ensure identical behavior.

**Test corpus (~800 files):** Most files are downloaded on demand; only
`tests/compatibility/files/plugins/` is committed in-tree.

```bash
# Inside nix develop — download the corpus first
./scripts/fetch-compat-test-files.sh
```

The compat suite itself is driven by the `compat.yml` workflow, which builds
`rledger` and compares its output against Python beancount over the fetched
corpus.

**BQL compatibility:**

```bash
python3 scripts/compat-bql-test.py \
  --corpus tests/compatibility/bql-queries.toml \
  --rledger ./target/release/rledger
```

**CI:** Runs nightly at 3 AM UTC via `.github/workflows/compat.yml`

## Test Fixtures

### Parser Fixtures (`tests/fixtures/`)

| File | Purpose |
|------|---------|
| `booking-scenarios.beancount` | Cost basis booking edge cases |
| `validation-errors.beancount` | All validation error types |
| `syntax-edge-cases.beancount` | Parser edge cases |
| `examples/` | Complete example ledgers |
| `lima-tests/` | beancount-parser-lima test cases |
| `python-plugins/` | Python plugin compatibility fixtures |

### Crate Fixtures (`crates/*/tests/fixtures/`)

Per-crate test data:

- `rustledger-loader/tests/fixtures/` - Include paths, cycles, errors
- `rustledger/tests/fixtures/` - CLI integration test files

### Compatibility Fixtures (`tests/compatibility/files/`)

Most of the corpus is downloaded on demand and gitignored. The only category
committed in-tree is:

- `plugins/` - Plugin configuration fixtures

The downloaded corpus (~800 files) is organized by upstream source under
`files/` (e.g. `beancount-v2/`, `beancount-v3/`, `fava/`).

## CI Workflows

| Workflow | Trigger | Tests Run |
|----------|---------|-----------|
| `ci.yml` | Push, PR | `cargo nextest run --all-features` (plus `cargo test --doc`) |
| `compat.yml` | Nightly (3 AM UTC) | Full compatibility suite |
| `tla.yml` | Changes to TLA+/`inventory.rs`/booking | TLA+ model checking |
| `mutation.yml` | Monthly / PR to verified modules | Mutation testing (`cargo-mutants`) |
| `fuzz.yml` | Nightly / PR to parser, query, booking | Fuzzing |
| `miri.yml` | Weekly | Miri (undefined-behavior checks) |
| `kani.yml` | Weekly / PR to core, booking | Kani model checking |

## Adding New Tests

### Unit Test

Add to the `#[cfg(test)]` module in the source file:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_feature() {
        // ...
    }
}
```

### Integration Test

Create or add to `crates/<crate>/tests/<name>_test.rs`:

```rust
use rustledger_core::*;

#[test]
fn test_integration_scenario() {
    // ...
}
```

### Property Test

Add to `crates/<crate>/tests/property_tests.rs`:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn my_invariant_holds(input in any::<u32>()) {
        // ... property assertions
    }
}
```

### Fixture File

1. Determine the appropriate location:

   - Parser/syntax: `tests/fixtures/`
   - Committed compatibility plugin fixtures: `tests/compatibility/files/plugins/`
   - Crate-specific: `crates/<crate>/tests/fixtures/`

1. Create a minimal `.beancount` file that reproduces the case

1. Update `tests/compatibility/sources.toml` if adding compatibility files

### TLA+ Specification

1. Create `spec/tla/MySpec.tla` with the specification
1. Create `spec/tla/MySpec.cfg` with model configuration
1. Add model check step to `.github/workflows/tla.yml`
1. Optionally add proptest integration in `tla_proptest.rs`

## Snapshot Testing

Parser tests use `insta` for snapshot testing:

```rust
#[test]
fn test_parse_transaction() {
    let result = parse("2024-01-01 * \"Test\"\n  Assets:Cash 100 USD");
    insta::assert_debug_snapshot!(result);
}
```

**Update snapshots:**

```bash
cargo insta review
```

## Test Coverage

Generate coverage report:

```bash
# Using cargo-llvm-cov
cargo llvm-cov --all-features --html
open target/llvm-cov/html/index.html
```

## Troubleshooting

### Tests timeout or run slowly

Property tests can take longer. Set a shorter case count:

```bash
PROPTEST_CASES=10 cargo test proptest
```

### Compatibility tests fail to find beancount

Run inside the nix development shell:

```bash
nix develop
./scripts/compat-test.sh
```

### TLA+ model checking fails

Ensure Java 17+ is installed:

```bash
java -version  # Should be 17+
```

### Snapshot tests fail after expected changes

Review and update snapshots:

```bash
cargo insta test
cargo insta review
```

## See Also

- [Benchmarking](benchmarking.md) - Performance benchmarks
