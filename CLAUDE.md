# Claude Code Context

This document provides context for Claude Code when reviewing pull requests and assisting with development.

## ⚠️ IMPORTANT: Always Use Worktrees

**All development work in this repository MUST use git worktrees.** This enables parallel development sessions and clean branch isolation.

### Quick Reference

```bash
# Check if you're in a worktree or main repo
if [ "$(git rev-parse --git-dir)" != "$(git rev-parse --git-common-dir)" ]; then
  echo "Already in a worktree - work here directly"
else
  echo "In main repo - create a worktree for your branch"
fi
```

### Workflow Rules

1. **Before starting any new work**, check if you're already in a worktree:
   - If YES → Work directly in this worktree (don't create another)
   - If NO → Create a worktree for your branch using `./scripts/worktree new <branch>`

2. **Never use `git checkout -b` in the main repo** - always use worktrees instead

3. **Each task/branch gets its own worktree** at `../<repo>-<branch-name>`

### Commands

| Command | Description |
|---------|-------------|
| `./scripts/worktree new <branch>` | Create worktree for new/existing branch |
| `./scripts/worktree list` | List all active worktrees |
| `./scripts/worktree remove <branch>` | Remove a worktree after PR merged |
| `./scripts/worktree clean` | Remove all worktrees except main |
| `./scripts/worktree cd <branch>` | Print path (use with `cd $(...)`) |

### Example Session

```bash
# Starting new work from main repo
./scripts/worktree new feature/add-csv-export
cd $(./scripts/worktree cd feature/add-csv-export)

# Now work in /home/user/.../rustledger-feature-add-csv-export
# Make changes, commit, push, create PR

# After PR is merged, clean up
cd /path/to/main/rustledger
./scripts/worktree remove feature/add-csv-export
```

### Why Worktrees?

- **Parallel sessions**: Run multiple Claude Code instances on different branches
- **No stashing**: Switch tasks without committing half-done work
- **Clean state**: Each worktree is isolated, no cross-contamination
- **Faster CI feedback**: Work on fixes while waiting for CI on another branch

---

## Project Overview

rustledger is a pure Rust implementation of Beancount, the double-entry bookkeeping language. It provides a 10-30x faster alternative to Python beancount with full syntax compatibility.

## Architecture

The project is a Cargo workspace with 12 crates:

| Crate | Purpose |
|-------|---------|
| `rustledger-core` | Core types (Amount, Position, Inventory, Directives) |
| `rustledger-parser` | Lexer and parser with error recovery |
| `rustledger-loader` | File loading, includes, options |
| `rustledger-booking` | Interpolation and booking engine (7 methods) |
| `rustledger-validate` | Validation with 27 error codes |
| `rustledger-query` | BQL query engine |
| `rustledger-plugin` | Native and WASM plugin system (20 plugins) |
| `rustledger-importer` | CSV/OFX import framework |
| `rustledger` | CLI tool (`rledger check`, `rledger query`, etc.) |
| `rustledger-wasm` | WebAssembly library target |
| `rustledger-ffi-wasi` | JSON API for embedding in any language |
| `rustledger-lsp` | Language Server Protocol implementation |

## Code Standards

### Rust Idioms

- Use `Result<T, E>` for fallible operations, not panics
- Prefer `?` operator over `.unwrap()` in production code
- Use `thiserror` for error types, `anyhow` in CLI/tests
- Prefer iterators over explicit loops where idiomatic
- Use `#[must_use]` on functions returning important values

### Performance

- Avoid unnecessary allocations (prefer `&str` over `String` when possible)
- Use `Cow<'a, str>` for potentially-owned strings
- Prefer `SmallVec` for small, stack-allocated collections
- Profile before optimizing - correctness first

### Testing

- Unit tests in `#[cfg(test)]` modules within source files
- Integration tests in `crates/*/tests/` directories
- Use `insta` for snapshot testing of parser output
- Use `proptest` for property-based testing
- All public APIs must have tests

### Documentation

- All public items must have doc comments
- Include examples in doc comments where helpful
- Use `# Errors` section to document error conditions
- Use `# Panics` section if function can panic

## Pull Request Review Policy

### Review Checklist

When reviewing PRs, check each of these areas:

1. **Correctness**: Does the code do what it claims?
2. **Beancount Compatibility**: Does it match Python beancount behavior?
3. **Error Handling**: Are errors handled gracefully with good messages?
4. **Tests**: Are there sufficient tests for new functionality?
5. **Performance**: Any obvious performance issues?
6. **Security**: Any potential security concerns (especially in parser/loader)?
7. **Documentation**: Are public APIs documented?
8. **Style**: Does it follow project conventions?

### Review Standards by PR Type

| PR Type | Focus Areas | Approval Threshold |
|---------|-------------|-------------------|
| Bug fix | Correctness, regression tests, no side effects | 1 approval |
| Feature | All checklist items, especially tests and docs | 1 approval |
| Parser changes | Beancount compatibility, fuzz testing, error messages | 1 approval + extra scrutiny |
| Breaking change | Migration path, documentation, all areas | 2 approvals |
| Security fix | Vulnerability addressed, no new issues introduced | 1 approval, expedited |

### Review Process

1. **Read the PR description** - Understand the intent
2. **Check CI status** - All checks should pass
3. **Review file changes** - Focus on logic, not just style
4. **Run locally if needed** - For complex changes
5. **Leave constructive feedback** - Suggest improvements, explain concerns
6. **Approve or request changes** - Be clear about blockers vs suggestions

### Common Review Comments

- "Add a test for this edge case"
- "This could panic on empty input - use `get()` instead of indexing"
- "Consider using `&str` instead of `String` here"
- "Does this match Python beancount behavior?"
- "This allocation could be avoided with..."

### Auto-merge Rules

PRs can auto-merge after CI passes if:
- Single approval obtained
- No "request changes" reviews pending
- PR is not marked as draft
- No merge conflicts

## Security Considerations

- **Parser**: Must handle malformed input gracefully (no panics)
- **Loader**: Must prevent path traversal in `include` directives
- **WASM**: Must be sandboxed, no file system access
- **Dependencies**: Check for known vulnerabilities with `cargo deny`

## Common Patterns

### Adding a new plugin

1. Create struct implementing `NativePlugin` trait in `rustledger-plugin/src/native/`
1. Register in `NativePluginRegistry::new()`
1. Add tests in `tests/native_plugins_test.rs`

### Adding a BQL function

1. Add case to `evaluate_function()` in `rustledger-query/src/executor.rs`
1. Add completion in `rustledger-query/src/completions.rs`
1. Add tests and documentation

### Adding a validation error

1. Add variant to `ValidationError` enum in `rustledger-validate/src/lib.rs`
1. Implement detection in `validate_*` function
1. Add tests covering the error case

## Build Commands

```bash
cargo check --all-features --all-targets  # Quick check
cargo test --all-features                  # Run all tests
cargo clippy --all-features -- -D warnings # Lint
cargo fmt --all -- --check                 # Format check
cargo deny check                           # Security audit
```

## Known Limitations & TODOs

### Decimal Precision (1 compat test failure)

**Issue**: `rust_decimal` has a maximum precision of 28 digits, while Python's `decimal.Decimal` has arbitrary precision. This causes 1 compatibility test failure out of 694 (99.86% pass rate).

**Affected file**: `beancount-lazy-plugins/tests_data_output_some_fund_output.beancount`
- Contains amounts with 28 decimal places (e.g., `0.7142857142857142857142857143`)
- Python detects a `2×10⁻²⁵ USD` residual imbalance
- Rust considers it balanced due to precision limits

**TODO**: Replace `rust_decimal` with an arbitrary-precision decimal library (e.g., `bigdecimal`) to achieve 100% compatibility with Python beancount's balance checking. This is a significant refactor affecting `rustledger-core` and all downstream crates.

**Practical impact**: None for real-world usage. No legitimate ledger has 28-decimal-place amounts.

## Roadmap

See [ROADMAP.md](ROADMAP.md) for the full project roadmap including near-term, medium-term, and long-term goals.
