______________________________________________________________________

## title: Development description: Contributing to rustledger

# Development

Guides for contributing to rustledger development.

## Getting Started

1. Clone the repository
1. Install Rust toolchain
1. Run `cargo build --all-features`
1. Run `cargo test --all-features`

See [CONTRIBUTING.md](https://github.com/rustledger/rustledger/blob/main/CONTRIBUTING.md) for detailed setup.

## Guides

| Guide | Description |
|-------|-------------|
| [Contributing Plugins](contributing-plugins.md) | Adding native plugins to rustledger |
| [Testing](testing.md) | Running tests, adding test cases |
| [Benchmarking](benchmarking.md) | Performance testing and profiling |

## Roadmaps

| Roadmap | Description |
|---------|-------------|
| [Testing Roadmap](testing-roadmap.md) | Test infrastructure improvements |
| [Import Roadmap](import-roadmap.md) | Bank import feature development |
| [Performance Roadmap](performance-roadmap.md) | Optimization phases |

## Quick Commands

```bash
# Build
cargo build --all-features

# Test
cargo test --all-features

# Lint
cargo clippy --all-features -- -D warnings

# Format
cargo fmt --all

# Benchmark
cargo bench

# Check dependencies
cargo deny check
```

## Project Structure

```
rustledger/
├── crates/
│   ├── rustledger-core/         # Core types
│   ├── rustledger-parser/       # Lexer and parser
│   ├── rustledger-loader/       # File loading
│   ├── rustledger-booking/      # Booking engine
│   ├── rustledger-validate/     # Validation
│   ├── rustledger-query/        # BQL engine
│   ├── rustledger-completion/   # Shared completion logic
│   ├── rustledger-plugin/       # Plugin system
│   ├── rustledger-plugin-types/ # Shared plugin types
│   ├── rustledger-importer/     # Import framework
│   ├── rustledger-ops/          # Pure directive operations
│   ├── rustledger-lsp/          # LSP server
│   ├── rustledger-wasm/         # WASM target
│   ├── rustledger-ffi-wasi/     # WASI FFI
│   └── rustledger/              # CLI binary
├── spec/                     # Specifications
└── tests/                    # Integration tests
```

## See Also

- [Architecture](../reference/architecture.md) - System design
- [ADRs](../reference/adr/) - Design decisions
- [Compatibility](../reference/compatibility.md) - Beancount compatibility
