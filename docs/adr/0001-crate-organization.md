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

- **rustledger-core**: Core types (Directive, Transaction, Amount, etc.) with no dependencies beyond std
- **rustledger-parser**: Beancount file parser, depends only on core
- **rustledger-loader**: File loading with include resolution, depends on parser
- **rustledger-validate**: Validation rules, depends on core
- **rustledger-booking**: Balance booking algorithms, depends on core
- **rustledger-query**: BQL query language, depends on core
- **rustledger-plugin**: Plugin infrastructure, depends on core
- **rustledger**: Umbrella crate re-exporting all functionality
- **rustledger-wasm**: WebAssembly bindings

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
