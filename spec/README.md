# Beancount Specification

This directory contains the specification documents for implementing rustledger, a pure Rust implementation of Beancount.

## Documents

### Core Specifications

| File | Description |
|------|-------------|
| [syntax.md](syntax.md) | Complete language syntax specification |
| [grammar.peg](grammar.peg) | Formal PEG grammar for parser implementation |
| [inventory.md](inventory.md) | Inventory, positions, lots, and booking algorithms |
| [algorithms.md](algorithms.md) | Interpolation, balancing, tolerance algorithms |
| [bql.md](bql.md) | Beancount Query Language specification |
| [options.md](options.md) | Configuration options reference |
| [validation.md](validation.md) | Complete validation error catalog |
| [ordering.md](ordering.md) | Directive ordering and sort rules |
| [wasm-plugins.md](wasm-plugins.md) | WASM plugin system design |

### Implementation Specifications

| File | Description |
|------|-------------|
| [architecture.md](architecture.md) | System architecture and crate structure |
| [decimals.md](decimals.md) | Decimal arithmetic, precision, tolerance rules |
| [api.md](api.md) | Library API design and serialization format |
| [error-recovery.md](error-recovery.md) | Parser error recovery and source locations |
| [properties.md](properties.md) | Property-based testing properties (22 properties) |
| [test-vectors.md](test-vectors.md) | Golden test vectors catalog (220+ cases) |

### Project Specifications

| File | Description |
|------|-------------|
| [glossary.md](glossary.md) | Definitions of terms |
| [performance.md](performance.md) | Performance targets and benchmarks |
| [compatibility.md](compatibility.md) | Python beancount compatibility notes |
| [ci.md](ci.md) | CI/CD testing strategy |

### Formal Specifications (TLA+)

| File | Description |
|------|-------------|
| [tla/Inventory.tla](tla/Inventory.tla) | Inventory operations formal spec |
| [tla/BookingMethods.tla](tla/BookingMethods.tla) | FIFO/LIFO/STRICT booking formal spec |
| [tla/TransactionBalance.tla](tla/TransactionBalance.tla) | Transaction balancing formal spec |

### Test Fixtures

| File | Description |
|------|-------------|
| [fixtures/syntax-edge-cases.beancount](fixtures/syntax-edge-cases.beancount) | Parser edge cases |
| [fixtures/booking-scenarios.beancount](fixtures/booking-scenarios.beancount) | Booking algorithm scenarios |
| [fixtures/validation-errors.beancount](fixtures/validation-errors.beancount) | Intentional errors for testing |

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                         rustledger                             │
├─────────────────────────────────────────────────────────────────┤
│  CLI / WASM / Library API                                        │
├─────────────────────────────────────────────────────────────────┤
│  Parser → Loader → Interpolation → Booking → Validation         │
├─────────────────────────────────────────────────────────────────┤
│  Core Types: Amount, Position, Inventory, Directive              │
├─────────────────────────────────────────────────────────────────┤
│  rust_decimal, chrono, wasmtime                                  │
└─────────────────────────────────────────────────────────────────┘
```

See [architecture.md](architecture.md) for detailed diagrams.

## Implementation Priority

### Phase 1: Core (MVP)
1. **Parser** - Parse full syntax to AST (`syntax.md`, `grammar.peg`, `error-recovery.md`)
2. **Loader** - Handle includes, collect options (`options.md`, `ordering.md`)
3. **Core Types** - Amount, Position, Inventory (`inventory.md`, `decimals.md`)
4. **Interpolation** - Fill missing posting amounts (`algorithms.md`)
5. **Booking** - Lot matching algorithms (`inventory.md`, `tla/BookingMethods.tla`)
6. **Validation** - Balance assertions, account lifecycle (`validation.md`)

### Phase 2: Tooling
7. **bean-check** - Validate ledger files
8. **BQL Engine** - Query language (`bql.md`)
9. **bean-query** - Interactive query REPL

### Phase 3: Extensibility
10. **WASM Plugins** - Plugin runtime (`wasm-plugins.md`)
11. **Built-in Plugins** - implicit_prices, etc.

## Key Metrics

| Metric | Python Beancount | rustledger Target |
|--------|------------------|---------------------|
| Parse + validate (10K txns) | 4-6 seconds | < 500ms |
| Memory usage | ~500 MB | < 100 MB |
| Startup time | ~1 second | < 50ms |
| WASM bundle | N/A | < 2 MB gzipped |

See [performance.md](performance.md) for benchmarks.

## Testing Strategy

| Test Type | Description | Location |
|-----------|-------------|----------|
| Unit Tests | Inline `#[test]` | `crates/*/src/` |
| Integration | Fixture-based | `crates/*/tests/` |
| Golden Tests | 220+ cases from Lima | `spec/fixtures/lima-tests/` |
| Property Tests | 22 proptest properties | `properties.md` |
| Compatibility | Compare vs Python | `tests/compat/` |
| Formal | TLA+ model checking | `spec/tla/` |
| Fuzz | libFuzzer targets | `fuzz/` |

Run `scripts/fetch-test-vectors.sh` to download golden test vectors.

See [ci.md](ci.md) for CI/CD pipeline.

## Quick Reference

- **Terminology**: [glossary.md](glossary.md)
- **Python differences**: [compatibility.md](compatibility.md)
- **API usage**: [api.md](api.md)
- **Error codes**: [validation.md](validation.md)

## Sources

These specs are derived from:
- [Official Beancount Documentation](https://beancount.github.io/docs/)
- [Beancount Source Code](https://github.com/beancount/beancount)
- [beancount-parser-lima](https://github.com/tesujimath/beancount-parser-lima)
- [Beancount v3 Design Doc](https://docs.google.com/document/d/1qPdNXaz5zuDQ8M9uoZFyyFis7hA0G55BEfhWhrVBsfc)
