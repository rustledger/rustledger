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
| `benchmarks`, `compatibility`, `profiling` | CI-managed data branches (nightly benchmark / compatibility results; `profiling` holds the deterministic instruction-count + heap trend history written by `profile.yml`). Written by automation — never hand-delete. |
| `fuzz-corpus` | CI-managed data branch holding the durable fuzz corpus (tens of thousands of inputs; the nightly commit message records the current count), written by the nightly `fuzz.yml` run and re-fetched by every later PR so each replays a corpus strictly stronger than the day before. Deleting it does not merely lose history: it silently resets every PR's fuzzing to cold, and nothing goes red to say so. Written by automation — never hand-delete. (Crash inputs are deliberately *not* kept here — they belong in-tree under `crates/<crate>/fuzz/regressions/<target>/`, committed alongside their fix, so losing this branch cannot resurrect a fixed bug.) |

When pruning merged/closed PR branches, skip the rows above.

None of these have an open PR, so any check of the form "no PR ⇒ stale" deletes
all of them. `git branch --merged` is no help either: this repo squash-merges,
so genuinely merged branches never appear in it. Classify by **PR state**
(`gh pr list --head <branch> --state all`), then subtract this table.

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
| `rustledger-ffi-wasi` | Slimmed FFI-support helpers crate reused by `rustledger-ffi-component` (loader orchestration + WIT-input construction + `compute_directive_hash`). Phase 5 (#1419) is complete: the wasip1 JSON-RPC surface AND the Directive→JSON DTO are removed; the crate is deliberately retained (its survivors are FFI glue kept out of core `rustledger-loader`). |
| `rustledger-ffi-component` | FFI via WASI Preview 2 / Component Model (typed WIT contract, `rustledger:ledger@3.0.0`) — primary embedding surface, default in the rustfava embedder (#1384 Phase 4) |

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

1. **Fixable** — we deviate, stay stricter or more correct than Python. Examples: cost-spec precision (beanquery#275, fixed in #1106 / #1113), `FIRST` aggregator short-circuit (beanquery#279, we evaluate eagerly), empty-aggregate quirk (beanquery#1055, we return the SQL identity), elided-zero-to-unopened-account check (Python #877-equivalent, we catch via two-phase validation), over-precise balance residuals beyond `rust_decimal`'s ~28–29-significant-digit ceiling (#1240 — a two-tier validator recomputes the residual in `BigDecimal`; see Decimal Precision below).

1. **Not fixable locally** — we match Python and document the limitation. Example: an amount *literal* written with more than ~28–29 significant digits is rounded on parse (`rust_decimal`'s coefficient ceiling); no real ledger contains them, and a recovery side channel was prototyped and rejected (see Decimal Precision below). Over-precise *residuals* are a separate, already-fixed case (above).

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

## Canonical-Function Discipline (Phase-3 of the 2026-07 duplication review)

A repo-wide correctness review (PRs #1731–#1743) traced every found bug to one
anti-pattern:

> **A consumer that can't (or won't) call the canonical function re-derives
> the logic inline, and nothing asserts agreement.**

Every re-derivation starts byte-identical and silently drifts (POSSIGN's
hardcoded account roots, the query weight ladder's precision loss, three
divergent account-name validators, the green/red parser mirrors). When you
write code that computes something the pipeline already computes, apply, in
order of preference:

1. **Call the canonical.** If a layering boundary blocks the call, move or
   re-expose the canonical rather than copying it. Existing canonicals to
   know: `rustledger_booking::{transaction_tolerances, cost_number_weight,
   price_weight}` (balance semantics), `rustledger_core::booking_sort_key`
   (directive order), `CostSpec::resolve` / `Position::from_posting`
   (cost resolution), `rustledger_parser::is_valid_account_name` (account
   names — implemented by RUNNING the lexer, so it cannot drift),
   `AccountTypes` (config-aware account classification — never match root
   prefixes by string), `cost_spec_from_tokens` / `meta_value_from_tokens`
   (green/red CST semantics), `process_pads` + `Ledger::balance_view`
   (pad expansion), `rustledger_core::format::{escape_csv, escape_string}`
   and `DisplayContext` (rendering).
1. **If the copy is deliberate, document the divergence at BOTH sites** with
   cross-references naming each other and a revisit condition (examples:
   `is_booking_reduction`'s paired comments; the valuation plugin's
   value-denominated FIFO; the LSP's single-pass validation pipeline).
1. **Pin agreement with a drift-guard test** that compares the two surfaces
   end-to-end on the shapes that historically broke (examples:
   `query_report_realization_parity_test`, `fuzz_green_eq_red` + its corpus
   test, `cost_number_wire_parity` across all five `CostNumber` mirrors).
   A guard that a future divergence CANNOT trip is decoration — assert on
   the exact observable, not a proxy (a bare substring match on `60.00 USD`
   was once satisfied by the wrong output line).

Two supporting rules from the same review:

- **Tests must be hermetic in what they assert about the environment.**
  Asserting "stdout is not a TTY", "no `~/.config/rledger` exists", or "this
  env var is unset" breaks on real developer machines (#1729). Inject the
  environmental inputs (`PagerEnv`-style) instead of assuming them, and never
  `set_var` in parallel tests.
- **Availability-gated tests must fail loudly somewhere.** A test that
  silently skips when a tool is missing is a test that never runs anywhere
  (the use-before-open bug shipped behind exactly that skip for its entire
  life). The `python-gated-cargo-tests` CI job asserts tool presence before
  running and greps for skip markers after; new gated suites must be added
  to it.

## Toolchain Bumps

CI pins an explicit stable version instead of floating (`toolchain: 1.97.0`
at every site that previously said `stable`; the MSRV job and the
nightly-based jobs keep their own separate pins), after a floating-`stable`
release broke every open PR overnight (#1745: new lints plus a
debug-frame-size change that overflowed the BQL parser's test-thread
stack). To bump:

1. Update the version in **BOTH places in lockstep**: every stable-channel
   `toolchain:` pin in `.github/workflows/*.yml` (grep for the `pinned
   stable` comment; leave MSRV/nightly pins alone) AND
   `rust-toolchain.toml`'s `channel`. rustup's file-based override beats the workflow-installed
   toolchain, so splitting them silently strands wasm targets on the wrong
   install (#1751 — every wasip2 job failed with "can't find crate for
   `std`").
1. Before pushing, run clippy + the full test suite under the NEW version
   (`rustup toolchain install <ver>`, `RUSTUP_TOOLCHAIN=<ver> cargo clippy
   --all-features --all-targets -- -D warnings`) and under the nix-pinned
   MSRV. New-lint fixes and behavioral breakage land in the bump PR itself.
1. Note that workflow-only PRs skip the component-build jobs via the
   `should_build` path gate — a toolchain bump PR should touch a Rust file
   (or dispatch the jobs manually) so the gated jobs actually validate it.

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

### Decimal Precision (#1240 — resolved via two-tier validation)

`rustledger-core::Decimal` is `rust_decimal::Decimal` (16 bytes, `Copy`, ~28–29
significant digits), kept as-is for hot-path speed. Python's `decimal.Decimal` is
arbitrary precision, so a balance **residual** born from products of
normal-precision inputs can require more digits than `rust_decimal` can hold.
Historically rledger rounded such a residual to zero and called the transaction
balanced where Python flagged an imbalance — e.g.
`beancount-lazy-plugins/tests_data_output_some_fund_output.beancount`, where
Python detects a `2.19×10⁻²⁵ USD` residual.

**Resolved** by a two-tier check in the balance validator
(`validate_transaction_balance` in `rustledger-validate`): it computes the fast
residual via `rustledger_booking::calculate_residual` (`rust_decimal`); when that
is non-zero it escalates to `rustledger_booking::calculate_residual_precise`,
which recomputes the residual in `BigDecimal` from each posting's exact
(≤28–29-digit) inputs.
`rledger check` now reports that residual (`2.187500000E-25 USD`) — at full
hot-path speed for ordinary ledgers, with no change to the `Decimal` type.

**Remaining limitation (a non-issue):** a single amount *literal* written with
more than ~28–29 significant digits is still rounded when parsed, because the
value itself cannot be held in `rust_decimal`. No legitimate ledger contains such
literals. A per-posting "side channel" to carry the exact literal into the
precise residual was prototyped and **rejected** (`spike/decimal-exact-sidechannel`,
PR #1613): recovering the value is not enough — the tolerance comparison,
cost/price weights, and every metadata egress (text / BQL / wasm) would each have
to become exact-aware, which is disproportionate work for a case that does not
occur in practice.
