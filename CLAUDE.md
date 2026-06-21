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

1. **Never use `git checkout -b` in the main repo** - always use worktrees instead

1. **Each task/branch gets its own worktree** at `../<repo>-<branch-name>`

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

### Long-lived reference branches — do NOT delete

A few remote branches are kept intentionally and are **not** cleanup targets,
even when they have no open PR. Run `git log origin/<branch>` for full context
before touching any of them (they are remote-only — a bare `<branch>` ref won't
resolve unless you've fetched it locally).

| Branch | Why it's kept |
|--------|---------------|
| `spike/ffi-wit-component` | WIT / Component-Model FFI design spike for #1384. Reference if the `rustledger:ledger` component contract (the typed WIT API) changes. |
| `spike/ledger-resource` | Stateful `resource session` "A+B boundary" redesign spike for #173. Reference for a future stateful embedding API. |
| `benchmarks`, `compatibility` | CI-managed data branches (nightly benchmark / compatibility results). Written by automation — never hand-delete. |

When pruning merged/closed PR branches, skip the rows above.

______________________________________________________________________

## Project Overview

rustledger is a pure Rust implementation of Beancount, the double-entry bookkeeping language. It provides a 10-30x faster alternative to Python beancount with full syntax compatibility.

## Architecture

The project is a Cargo workspace with 16 crates plus editor extensions:

| Crate | Purpose |
|-------|---------|
| `rustledger-core` | Core types (Amount, Position, Inventory, Directives) |
| `rustledger-parser` | Lexer and parser with error recovery |
| `rustledger-loader` | File loading, includes, options |
| `rustledger-booking` | Interpolation and booking engine (7 methods) |
| `rustledger-validate` | Validation with 26 error codes |
| `rustledger-query` | BQL query engine |
| `rustledger-completion` | Editor-agnostic completion logic (shared by LSP + WASM) |
| `rustledger-plugin` | Native and WASM plugin system (30 plugins) |
| `rustledger-plugin-types` | Shared plugin type definitions |
| `rustledger-importer` | Import framework for bank statements |
| `rustledger-ops` | Pure operations on directives — dedup, categorize, reconcile |
| `rustledger` | CLI tool (`rledger check`, `rledger query`, etc.) |
| `rustledger-wasm` | WebAssembly library target |
| `rustledger-lsp` | Language Server Protocol implementation |
| `rustledger-ffi-wasi` | FFI via WASI (wasip1) JSON-RPC for embedding — legacy, slated for removal in Phase 5 (#1419) |
| `rustledger-ffi-component` | FFI via WASI Preview 2 / Component Model (typed WIT contract, `rustledger:ledger@2.1.0`) — primary embedding surface, default in the rustfava embedder (#1384 Phase 4) |

| Package | Purpose |
|---------|---------|
| `packages/vscode` | VS Code extension (thin LSP client wrapper) |

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
1. **Beancount Compatibility**: Does it match Python beancount behavior?
1. **Error Handling**: Are errors handled gracefully with good messages?
1. **Tests**: Are there sufficient tests for new functionality?
1. **Performance**: Any obvious performance issues?
1. **Security**: Any potential security concerns (especially in parser/loader)?
1. **Documentation**: Are public APIs documented?
1. **Style**: Does it follow project conventions?

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
1. **Check CI status** - All checks should pass
1. **Review file changes** - Focus on logic, not just style
1. **Run locally if needed** - For complex changes
1. **Leave constructive feedback** - Suggest improvements, explain concerns
1. **Approve or request changes** - Be clear about blockers vs suggestions

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

### Requesting Copilot Code Review

Request or re-request a Copilot review on any PR:

```bash
gh pr edit <PR_NUMBER> --add-reviewer @copilot
```

This triggers a fresh review against the current diff. Copilot leaves "Comment" reviews (never approves or blocks merging).

### Using GLM5 for PR Reviews

You can use [opencode](https://opencode.ai) with Together AI's GLM-5 model for additional PR review perspectives.

**Setup:**

```bash
# Ensure Together AI API key is available
export TOGETHER_API_KEY="your-api-key"
```

**Review a PR:**

```bash
# Save PR diff to a file (opencode can't run gh in non-interactive mode)
gh pr diff <PR_NUMBER> > /tmp/pr-diff.txt

# Run GLM5 review
opencode run -m togetherai/zai-org/GLM-5 -f /tmp/pr-diff.txt -- \
  "Review this PR diff. Check code examples for accuracy, type correctness, and completeness. Identify any issues."
```

**Available models:**

```bash
opencode models | grep togetherai  # List all Together AI models
```

Common models: `togetherai/zai-org/GLM-5`, `togetherai/deepseek-ai/DeepSeek-V3`, `togetherai/Qwen/Qwen3-Coder-480B-A35B-Instruct-FP8`

**Important:** Always validate GLM5 findings against actual source code - it can produce false positives (e.g., claiming WASM32 pointer packing is broken when it's correct for 32-bit targets).

## Security Considerations

- **Parser**: Must handle malformed input gracefully (no panics)
- **Loader**: Must prevent path traversal in `include` directives
- **WASM**: Must be sandboxed, no file system access
- **Dependencies**: Check for known vulnerabilities with `cargo deny`

## Python Compatibility Policy

rledger aims for full Python beancount compatibility on **correct behavior**, but deliberately **does not copy bugs we can fix locally**.

Each Python bug we encounter falls into one of three buckets:

1. **Fixable** — we deviate, stay stricter or more correct than Python. Examples: cost-spec precision (beanquery#275, fixed in #1106 / #1113), `FIRST` aggregator short-circuit (beanquery#279, we evaluate eagerly), empty-aggregate quirk (beanquery#1055, we return the SQL identity), elided-zero-to-unopened-account check (Python #877-equivalent, we catch via two-phase validation).

1. **Not fixable locally** — we match Python and document the limitation. Example: the `rust_decimal` 28-digit ceiling (would require migrating to an arbitrary-precision library like `bigdecimal` — significant refactor for negligible practical benefit).

1. **Out of scope** — we mask the Python-side divergence in the compat suite so it doesn't pollute the metric. Example: `KNOWN_PYTHON_DIVERGENCES` entries in `scripts/compat-bql-test.py`.

### Checklist for a deliberate Python deviation

When you choose to be stricter or more correct than Python on a specific case:

- [ ] Add an inline code comment naming the Python issue (e.g. `// Stricter than Python: see beanquery#279 — we evaluate eagerly`).
- [ ] Add a regression test pinning the stricter behavior in the appropriate crate.
- [ ] If the deviation surfaces in the BQL compat suite, register it under `KNOWN_RUST_DIVERGENCES` in `scripts/compat-bql-test.py` (so the metric stays honest about which side has the bug).
- [ ] If the deviation involves a pipeline architecture decision (e.g. multi-phase validation), document the architecture in a code comment so future contributors don't re-derive the rationale.

### Pointers to existing examples

- `rustledger-booking/src/interpolate.rs` — early/late validation split that catches Python #877's silent miss (see also `rustledger-validate::validate_early`).
- `rustledger-query/src/executor/aggregation.rs` — eager balance evaluation that avoids beanquery#279.
- `scripts/compat-bql-test.py` — `_is_beanquery_empty_aggregate_quirk` runtime predicate for beanquery#1055.
- `rustledger-loader/src/process.rs` — split plugin pass (synth pre-booking, regular post-booking) so the Early validator sees plugin-synthesized Opens while cost-spec-reading plugins still see booked values. See `PluginPass` rustdoc. The pipeline is `sort → synth-plugins → Early → book → regular-plugins → Late → finalize`.

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

### VS Code Extension

The VS Code extension (`packages/vscode`) is a **thin wrapper** around `rledger-lsp`. All language features come from the LSP.

**Design principles:**

- No TextMate grammar — semantic highlighting provided by LSP
- No syntax validation — diagnostics provided by LSP
- No indentation rules — keep it minimal
- Only provide: file associations, LSP client connection, auto-update

**What the extension contains:**

- `extension.ts` — LSP client + GitHub Releases auto-update
- `language-configuration.json` — comment character (`;`) and bracket pairs only
- `package.json` — file associations (`.beancount`, `.bean`) and settings

**Building locally:**

```bash
cd packages/vscode
npm ci
npm run package  # Creates rustledger-vscode.vsix
```

**Version handling:** The extension version is synced from the release tag during CI (not from `package.json`).

## Build Commands

```bash
cargo check --all-features --all-targets  # Quick check
cargo test --all-features                  # Run all tests
cargo clippy --all-features -- -D warnings # Lint
cargo fmt --all -- --check                 # Format check
cargo deny check                           # Security audit
```

## Pre-push Hooks & Fast Testing

The pre-push hook runs `cargo check` (2-30s) but intentionally **does not** run `cargo test` (full workspace takes 10-30 min). This means compilation-correct but semantically-wrong changes can be pushed and only caught in CI.

**Before pushing, test the crates you changed:**

```bash
# Test only the crate(s) you modified (5-30s typically)
cargo test -p rustledger-parser
cargo test -p rustledger-lsp --all-features

# Or use the just recipe to auto-detect changed crates:
just test-changed
```

The `just test-changed` recipe detects which crates have uncommitted or staged changes and runs tests only for those. This is the recommended workflow before pushing.

**Bypass the pre-push hook** (for WIP commits): `git push --no-verify`

## Headless / Automated Issue Resolution

When running in headless mode (`claude -p`) or via Agent Orchestrator (`ao`), follow this exact workflow:

### 1. Understand the Issue

- Read the full GitHub issue including all comments
- Identify acceptance criteria — what does "done" look like?
- If the issue is ambiguous, make reasonable assumptions and document them in the PR description

### 2. Plan Before Coding

- Identify which crates are affected
- Check existing tests for the area you're changing
- If it's a parser or booking change, check Beancount compatibility test suite

### 3. Implement

- Work in a git worktree (ao handles this automatically)
- Make minimal, focused changes — one issue per PR
- Follow existing patterns in the crate you're modifying
- Add tests for every code path you change or add

### 4. Verify Before PR

Run the commands from the **Build Commands** section above in order, and fix any failures before proceeding.

### 5. Create the PR

- Title: `fix: <description>` or `feat: <description>` (conventional commits)
- Body must include: what changed, why, how to test, and `Closes #<issue>`
- Request review if the change touches parser, booking, or public API
- If CI fails, read the error and fix it — do not open the PR with failing CI

### 6. Self-Review Checklist

Before marking the PR as ready:

- [ ] Changes are minimal and focused on the issue
- [ ] All new code has tests
- [ ] No `.unwrap()` in library code
- [ ] Error messages include file location context
- [ ] Public APIs have doc comments
- [ ] No unrelated formatting or refactoring changes

## Known Limitations & TODOs

### Decimal Precision (1 compat test failure)

**Issue**: `rust_decimal` has a maximum precision of 28 digits, while Python's `decimal.Decimal` has arbitrary precision. This causes 1 compatibility test failure out of 694 (99.86% pass rate).

**Affected file**: `beancount-lazy-plugins/tests_data_output_some_fund_output.beancount`

- Contains amounts with 28 decimal places (e.g., `0.7142857142857142857142857143`)
- Python detects a `2×10⁻²⁵ USD` residual imbalance
- Rust considers it balanced due to precision limits

**TODO**: Replace `rust_decimal` with an arbitrary-precision decimal library (e.g., `bigdecimal`) to achieve 100% compatibility with Python beancount's balance checking. This is a significant refactor affecting `rustledger-core` and all downstream crates.

**Practical impact**: None for real-world usage. No legitimate ledger has 28-decimal-place amounts.
