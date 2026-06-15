# rustledger-ops

Pure operations on beancount directives — dedup, categorize, reconcile.

## Overview

This crate provides reusable functions for transforming and analyzing collections of beancount directives. All operations are pure — they take directives in and return results out, with no I/O or framework coupling.

Analogous to Python beancount's `ops/` module.

## Modules

| Module | Description |
|--------|-------------|
| `fingerprint` | Structural hashing and stable fingerprinting of transactions |
| `dedup` | Duplicate detection (structural, fuzzy, and fingerprint-based) |
| `categorize` | Rule-based and pattern-based account categorization |
| `merchants` | Merchant name normalization and lookup dictionary |
| `enrichment` | Shared types for operation results (confidence, method, alternatives) |
| `ml` | ML-based categorization (TF-IDF + Naive Bayes); host-only, absent on wasm targets |
| `transfer` | Transfer detection between own accounts |
| `reconcile` | Reconciliation of imported vs. existing directives |

## Usage

```rust
use rustledger_ops::dedup::find_structural_duplicates;
use rustledger_ops::fingerprint::structural_hash;

// Find duplicate transactions in a directive list
let duplicates = find_structural_duplicates(&directives);

// Compute a structural hash of a single transaction
let hash = structural_hash("2024-01-15", &transaction_data);
```

## Design

Operations in this crate depend on `rustledger-plugin-types` (for `DirectiveWrapper` and related types) plus utility crates (`rust_decimal`, `jiff`, `blake3`, `regex`, and a host-only ML stack for the `ml` module). They know nothing about the plugin runtime, CLI, LSP, or import system.

This separation allows the same operations to be used by:
- The plugin system (via thin `NativePlugin` wrappers)
- The import pipeline (for dedup and categorization)
- CLI commands (e.g., `rledger dedup`)
- The LSP (for diagnostics and code actions)

## License

GPL-3.0
