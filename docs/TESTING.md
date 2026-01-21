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
│   ├── compat/
│   │   ├── files/                  # 93 curated compatibility files
│   │   ├── README.md
│   │   └── sources.toml
│   ├── compat-full/                # ~800 files (gitignored, fetched on demand)
│   └── compat-results/             # Test results (gitignored)
├── spec/
│   ├── fixtures/                   # Parser and example fixtures
│   │   ├── booking-scenarios.beancount
│   │   ├── validation-errors.beancount
│   │   ├── examples/
│   │   └── lima-tests/
│   └── tla/                        # TLA+ specifications (19 specs)
│       ├── FIFOCorrect.tla
│       ├── Conservation.tla
│       └── ...
└── scripts/
    ├── compat-test.sh              # Run compatibility tests
    ├── compat-bql-test.sh          # BQL compatibility tests
    └── fetch-compat-test-files.sh  # Download full test suite
```

### Test Types by Crate

| Crate | Unit | Integration | Property | TLA+ |
|-------|:----:|:-----------:|:--------:|:----:|
| rustledger-core | Yes | - | Yes | Yes |
| rustledger-parser | Yes | Yes | - | - |
| rustledger-query | Yes | Yes | - | - |
| rustledger-validate | Yes | Yes | Yes | Yes |
| rustledger-loader | Yes | Yes | - | - |
| rustledger-plugin | Yes | Yes | - | - |
| rustledger-booking | Yes | - | - | - |
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

**Curated files (93 files):** Committed to `tests/compat/files/`
```bash
./scripts/compat-test.sh tests/compat/files
```

**Full suite (~800 files):** Downloaded on demand
```bash
# Inside nix develop
./scripts/fetch-compat-test-files.sh
./scripts/compat-test.sh
```

**BQL compatibility:**
```bash
./scripts/compat-bql-test.sh
```

**CI:** Runs nightly at 3 AM UTC via `.github/workflows/compat.yml`

## Test Fixtures

### Parser Fixtures (`spec/fixtures/`)

| File | Purpose |
|------|---------|
| `booking-scenarios.beancount` | Cost basis booking edge cases |
| `validation-errors.beancount` | All validation error types |
| `syntax-edge-cases.beancount` | Parser edge cases |
| `examples/` | Complete example ledgers |
| `lima-tests/` | beancount-parser-lima test cases |

### Crate Fixtures (`crates/*/tests/fixtures/`)

Per-crate test data:
- `rustledger-loader/tests/fixtures/` - Include paths, cycles, errors
- `rustledger/tests/fixtures/` - CLI integration test files

### Compatibility Fixtures (`tests/compat/files/`)

Organized by category:
- `parser/` - Parser edge cases (~25 files)
- `validation/` - Validation scenarios (~20 files)
- `plugins/` - Plugin configurations (~5 files)
- `real-world/` - Community examples (~35 files)
- `edge-cases/` - Known differences (~10 files)

## CI Workflows

| Workflow | Trigger | Tests Run |
|----------|---------|-----------|
| `ci.yml` | Push, PR | `cargo test --all-features` |
| `compat.yml` | Nightly | Full compatibility suite |
| `tla.yml` | Changes to TLA+/inventory/booking | TLA+ model checking |

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
   - Parser/syntax: `spec/fixtures/`
   - Compatibility: `tests/compat/files/<category>/`
   - Crate-specific: `crates/<crate>/tests/fixtures/`

2. Create a minimal `.beancount` file that reproduces the case

3. Update `tests/compat/sources.toml` if adding compatibility files

### TLA+ Specification

1. Create `spec/tla/MySpec.tla` with the specification
2. Create `spec/tla/MySpec.cfg` with model configuration
3. Add model check step to `.github/workflows/tla.yml`
4. Optionally add proptest integration in `tla_proptest.rs`

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

- [BENCHMARKING.md](BENCHMARKING.md) - Performance benchmarks
- [CONTRIBUTING.md](../CONTRIBUTING.md) - Development workflow
- [spec/README.md](../spec/README.md) - Specification documents
- [tests/compat/README.md](../tests/compat/README.md) - Compatibility test details
