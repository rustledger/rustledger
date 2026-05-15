# ADR-0001: Crate Organization

## Status

Accepted

## Context

Rustledger aims to be a Beancount-compatible accounting library and CLI toolkit. We need to decide how to structure the codebase - as a single monolithic crate or as multiple smaller crates.

Key considerations:

- Users may want only parsing, only validation, or the full toolkit
- Compile times increase with crate size
- Testing and documentation are easier with focused modules
- WASM builds need minimal dependencies

## Decision

Organize the codebase as a workspace with multiple focused crates:

- **rustledger-core**: Core types (Directive, Transaction, Amount, etc.) with no internal dependencies
- **rustledger-parser**: Beancount file parser, depends only on core
- **rustledger-loader**: File loading, includes, caching, and processing pipeline (sort → synth-plugins → Early validation → book → regular-plugins → Late validation → finalize)
- **rustledger-validate**: Validation rules, depends on core, parser, booking
- **rustledger-booking**: Balance booking algorithms, depends on core
- **rustledger-query**: BQL query language, depends on core, parser, loader
- **rustledger-plugin**: Native + WASM + Python plugin system (30+ plugins), depends on core
- **rustledger-plugin-types**: Shared WASM plugin interface types (minimal, no internal deps)
- **rustledger-importer**: Bank statement import framework (CSV, OFX)
- **rustledger**: CLI binary (`rledger`, `bean-*` commands)
- **rustledger-wasm**: WebAssembly bindings for JS/TS
- **rustledger-lsp**: Language Server Protocol for editor integration
- **rustledger-ffi-wasi**: FFI via WASI JSON-RPC for embedding in any language

## Consequences

### Positive

- Users can depend on only what they need (`rustledger-parser` for parsing only)
- Faster incremental compilation due to smaller compilation units
- Clear boundaries between concerns
- WASM builds can exclude unnecessary dependencies
- Each crate can have focused documentation and tests

### Negative

- More boilerplate for inter-crate dependencies
- Need to maintain version compatibility across crates
- Initial setup complexity is higher

### Neutral

- Using a Cargo workspace for coordinated releases
