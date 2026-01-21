# Rustledger Development Guidelines

This document provides context for AI assistants working on the rustledger codebase.

## Project Overview

Rustledger is a pure Rust implementation of Beancount, the double-entry bookkeeping language. It provides a 10-30x faster alternative to Python beancount with full syntax compatibility.

## Architecture

The project is a Cargo workspace with these crates:

| Crate | Purpose |
|-------|---------|
| `rustledger-core` | Core types (Amount, Position, Inventory, Directives) |
| `rustledger-parser` | Lexer and parser with error recovery |
| `rustledger-loader` | File loading, includes, options |
| `rustledger-booking` | Interpolation and booking engine (7 methods) |
| `rustledger-validate` | Validation with 27 error codes |
| `rustledger-query` | BQL query engine |
| `rustledger-plugin` | Native and WASM plugin system (20 plugins) |
| `rustledger` | CLI tools (rledger-check, rledger-query, etc.) |
| `rustledger-wasm` | WebAssembly library target |
| `rustledger-lsp` | Language Server Protocol implementation |

## Rust-Specific Patterns

### Error Handling Strategy

This project uses a layered error handling approach:

| Layer | Crate | Pattern |
|-------|-------|---------|
| Library crates | `rustledger-*` | `thiserror` with typed errors |
| CLI binaries | `rustledger` | `anyhow` for ergonomic error chains |
| Tests | All | `anyhow` or `.unwrap()` with clear context |

**Error type conventions:**
```rust
// In library code - use thiserror
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("unexpected token at {location}: expected {expected}, found {found}")]
    UnexpectedToken { location: Span, expected: String, found: String },

    #[error("invalid amount: {0}")]
    InvalidAmount(#[from] DecimalError),
}

// In CLI code - use anyhow
fn main() -> anyhow::Result<()> {
    let ledger = load_file(&path).context("failed to load ledger")?;
    Ok(())
}
```

**Rules:**
- Never use `.unwrap()` in library code unless mathematically impossible to fail
- Use `.expect("reason")` only when failure indicates a bug
- Propagate errors with `?`, add context with `.context()` or `.with_context()`
- User-facing errors must include file location (path, line, column)

### Async Runtime

This project is **synchronous** - no async runtime is used. Reasons:
- File I/O is the only blocking operation, and it's fast enough sync
- Simpler mental model for accounting calculations
- WASM target doesn't support async well

**If async is ever needed:**
- Use `tokio` (not async-std)
- Prefer `tokio::fs` over `std::fs` in async contexts
- Use `#[tokio::main]` for CLI, `#[tokio::test]` for async tests

### Memory Management Guidelines

| Type | When to Use |
|------|-------------|
| `&str` | Borrowed string, no ownership needed |
| `String` | Owned string, needs modification or storage |
| `Cow<'a, str>` | May or may not need to own (parsing, transformations) |
| `Arc<str>` | Shared ownership across threads (interned strings) |
| `Box<T>` | Single ownership of heap data, rare in this codebase |
| `Rc<T>` | **Avoid** - not thread-safe, use `Arc` instead |

**String interning:**
The project uses string interning for frequently repeated values:
- Account names (`Assets:Bank:Checking`)
- Currency codes (`USD`, `EUR`)
- Payee names

Interned strings are stored as `Arc<str>` in a global interner. Use `intern_string()` to intern.

**Allocation guidelines:**
- Prefer `SmallVec<[T; N]>` for small, bounded collections (e.g., posting legs)
- Use `Vec::with_capacity()` when size is known
- Avoid `clone()` in hot paths - prefer borrowing
- Use `Cow` for functions that sometimes need to modify strings

### Type-First Development

When implementing new features:
1. **Define types first** - structs, enums, traits
2. **Write trait bounds** - what capabilities are needed?
3. **Let the compiler guide you** - fix errors iteratively
4. **Implement logic last** - once types compile, logic is constrained

This approach works well with AI assistance because:
- Rust's compiler provides structured feedback
- Type errors are specific and actionable
- The AI can iterate quickly on compiler output

## Code Standards

### Rust Idioms

- Use `Result<T, E>` for fallible operations, not panics
- Prefer `?` operator over `.unwrap()` in production code
- Use `thiserror` for error types, `anyhow` in CLI/tests only
- Prefer iterators over explicit loops where idiomatic
- Use `#[must_use]` on functions returning important values
- Prefer `&str` over `String` when possible
- Use `Cow<'a, str>` for potentially-owned strings

### Testing

| Test Type | Location | Framework |
|-----------|----------|-----------|
| Unit tests | `#[cfg(test)]` in source files | `#[test]` |
| Integration tests | `crates/*/tests/*.rs` | `#[test]` |
| Snapshot tests | Parser output, error messages | `insta` |
| Property tests | Invariants, roundtrips | `proptest` |
| Fuzzing | Parser, untrusted input | `cargo-fuzz` (nightly) |

**Test naming:** `test_<function>_<scenario>`
```rust
#[test]
fn test_parse_amount_with_commodity() { }

#[test]
fn test_parse_amount_negative_value() { }

#[test]
fn test_parse_amount_missing_currency_returns_error() { }
```

### Documentation

- All public items must have doc comments
- Include examples in doc comments where helpful
- Use `# Errors` section to document error conditions
- Use `# Panics` section if function can panic (should be rare)

## Build Commands

```bash
# Quick feedback loop (run after every change)
cargo check --all-features --all-targets

# Full test suite
cargo test --all-features

# Lint with warnings as errors
cargo clippy --all-features --all-targets -- -D warnings

# Format all files
treefmt

# Security audit
cargo deny check

# Coverage report
cargo llvm-cov --html
```

## Common Tasks

### Adding a New Plugin

1. Create struct implementing `NativePlugin` trait in `rustledger-plugin/src/native/`
2. Register in `NativePluginRegistry::new()`
3. Add tests in `tests/native_plugins_test.rs`

### Adding a BQL Function

1. Add case to `evaluate_function()` in `rustledger-query/src/executor.rs`
2. Add completion in `rustledger-query/src/completions.rs`
3. Add tests and documentation

### Adding a Validation Error

1. Add variant to `ValidationError` enum in `rustledger-validate/src/lib.rs`
2. Implement detection in `validate_*` function
3. Add tests covering the error case

## Git Workflow

- Use conventional commits: `feat:`, `fix:`, `docs:`, `refactor:`, `test:`, `chore:`
- PRs require CI to pass before merge
- Use merge queue for main branch

## Security Considerations

- **Parser**: Must handle malformed input gracefully (no panics)
- **Loader**: Must prevent path traversal in `include` directives
- **WASM**: Must be sandboxed, no file system access
- **Dependencies**: Check for known vulnerabilities with `cargo deny`

## Performance Guidelines

- Profile before optimizing - correctness first
- Avoid unnecessary allocations in hot paths
- Use `SmallVec` for small, stack-allocated collections
- String interning is used for accounts, currencies, payees

## What NOT to Do

- Don't add features beyond what's requested
- Don't refactor code that isn't related to the task
- Don't add unnecessary error handling for impossible cases
- Don't create abstractions for one-time operations
- Don't add backwards-compatibility shims - just change the code
