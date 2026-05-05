# Contributing to Rustledger

Thank you for your interest in contributing to Rustledger!

## Development Setup

### Prerequisites

- Rust 1.90+ (`rustup update stable`) - Rust 2024 edition
- Node.js 18+ (for MCP server)
- wasm-pack (for WASM builds): `cargo install wasm-pack`

### Building

```bash
# Build all crates
cargo build

# Run tests
cargo test

# Build WASM package
cd crates/rustledger-wasm
wasm-pack build --target web

# Build MCP server
cd packages/mcp-server
npm install && npm run build
```

## Git Workflow

### Branching Strategy

We use a simple GitHub Flow:

```
main ─────●─────●─────●─────●───── (stable, releases tagged here)
           \   /       \   /
            \_/         \_/
         feature/x    fix/y
```

- **`main`** - Stable, production-ready code. All releases are tagged here.
- **Feature branches** - Short-lived branches for development, merged to `main`.

### Branch Naming

Branches must follow this pattern:

```
<type>/<description>
```

| Type | Purpose |
|------|---------|
| `feature/` | New features |
| `fix/` | Bug fixes |
| `docs/` | Documentation changes |
| `chore/` | Maintenance, CI, dependencies |
| `refactor/` | Code refactoring |

**Examples:**

- `feature/add-csv-export`
- `fix/balance-calculation`
- `docs/update-readme`
- `chore/bump-dependencies`

**Rules:**

- Use lowercase letters, numbers, and hyphens only
- Keep descriptions concise but descriptive
- No uppercase, underscores, or special characters

### Commit Messages

We use [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>: <description>

[optional body]
```

**Types:**

- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation only
- `chore`: Maintenance tasks
- `refactor`: Code refactoring
- `test`: Adding/updating tests
- `ci`: CI/CD changes

**Examples:**

```
feat: add CSV export for query results
fix: correct balance calculation for multi-currency accounts
docs: update installation instructions
chore: bump rust_decimal to 1.36
```

## Release Process

Releases are fully automated via GitHub Actions when a version tag is pushed.

### Creating a Release

1. Update version in `Cargo.toml`:

   ```toml
   [workspace.package]
   version = "1.0.0"
   ```

1. Update internal crate dependencies to match.

1. Commit and tag:

   ```bash
   git add -A
   git commit -m "chore: bump version to 1.0.0"
   git push
   git tag v1.0.0
   git push origin v1.0.0
   ```

### Version Tags

| Tag Format | Description | npm Tag |
|------------|-------------|---------|
| `v1.0.0` | Stable release | `latest` |
| `v1.0.0-rc.1` | Release candidate | `next` |
| `v1.0.0-beta.1` | Beta release | `next` |

### What Gets Published

On tag push, the release workflow automatically:

1. **Builds binaries** for Linux, macOS, Windows (x64 + ARM64)
1. **Creates GitHub Release** with all artifacts
1. **Publishes to crates.io** (all Rust crates)
1. **Publishes to npm**:
   - `@rustledger/wasm` - WASM bindings
   - `@rustledger/mcp-server` - MCP server

## Code Style

- Run `cargo fmt` before committing
- Run `cargo clippy` to check for lints
- All code must pass CI checks

## Pull Request Process

### Creating a PR

1. Create a feature branch from `main`
1. Make your changes with clear, atomic commits
1. Ensure all tests pass: `cargo test`
1. Push and open a PR against `main`
1. Fill out the PR template completely

### Draft PRs

Use draft PRs for:

- Work in progress that needs early feedback
- Large changes you want to discuss before finalizing
- Experimental features

Convert to "Ready for review" when complete.

### Review Requirements

| PR Type | Required Approvals | Auto-merge |
|---------|-------------------|------------|
| Bug fix | 1 | Yes, after CI passes |
| Feature | 1 | No |
| Breaking change | 2 | No |
| Security fix | 1 | Yes, expedited |

### Review SLA

- **Initial review**: Within 48 hours
- **Follow-up reviews**: Within 24 hours
- **Urgent/security**: Same day

If your PR hasn't been reviewed, feel free to ping in the PR comments.

### What Reviewers Check

1. **Correctness**: Does the code do what it claims?
1. **Tests**: Are there sufficient tests for the changes?
1. **Beancount compatibility**: Does it match Python beancount behavior?
1. **Performance**: Any obvious performance regressions?
1. **Security**: Any potential vulnerabilities (especially in parser/loader)?
1. **Documentation**: Are public APIs documented?
1. **Style**: Does it follow project conventions?

### Merge Policy

- All CI checks must pass
- Required approvals must be obtained
- PR branch should be up-to-date with `main`
- Squash merge for single-purpose PRs
- Merge commit for multi-commit PRs that should preserve history

### After Merge

- Delete the feature branch
- Close related issues
- Update documentation if needed

## Plugin testing requirements

Native beancount plugins live in `crates/rustledger-plugin/src/native/plugins/` and are tested in `crates/rustledger-plugin/tests/native_plugins_test.rs`. Issue #992 surfaced a class of bug where a plugin silently emitted wrong output because the consumer ignored a discriminator field (`is_total`) and the test had a weak count assertion (`assert!(count >= 1)`). The plan in #992 documents the structural fixes; the requirements below codify them so future plugins don't regress.

### Required for every new or modified plugin

1. **Test matrix, not "happy path"**. Cover every input variant the plugin can encounter:
   - Each branch of every input enum (e.g. `@`, `@@`, cost, both, none for posting prices)
   - Edge cases (empty, zero, negative, missing optional fields)
   - Each output kind the plugin can emit

2. **Strict count assertions**. Use `assert_eq!(emitted.len(), 1)` — **never** `assert!(emitted.len() >= 1)`. The latter accepts both correct emission and over-emission, which is exactly the failure mode that hid the #992 double-emit bug.

3. **No `(partial)` test ports**. When porting tests from upstream beancount's `<plugin>_test.py`, port the **whole file** or document explicitly which cases are intentionally skipped and why. Test files with `// Converted from … (partial)` comments are no longer accepted.

4. **Differential coverage where applicable**. If your plugin reimplements a beancount built-in, drop a fixture under `tests/compatibility/files/plugin/<name>/` that enables the plugin via `plugin "..."` directive. The BQL compat harness (PR #1000, `scripts/compat-bql-test.py`) automatically diffs rledger's output against bean-check's. No new harness code is required — just the fixture.

5. **Type-driven exhaustive matching**. When consuming an enum-shaped input, use `match` and let the compiler enforce that every variant is handled. Don't extract a discriminator field manually and condition on it — that's the bug shape from #992. (Example: `PriceAnnotationData::view()` from `rustledger-plugin-types` returns a typed enum; new consumers should `match` on its arms rather than reading the underlying `is_total: bool`. The view API is added in PR #999.)

### For numeric plugins specifically

Plugins that compute new numbers from existing ones (`implicit_prices`, `unrealized`, `sell_gains`, `coherent_cost`, `check_average_cost`) MUST also include at least one property test (`proptest`) covering an algebraic invariant. Examples:

- `implicit_prices`: emitted price round-trips through `PriceDatabase` to the original
- `unrealized`: `Sum(realized) + Sum(unrealized) = Sum(total)` at any cutoff date
- `sell_gains`: gains posting balances the transaction
- `no_duplicates`: output has no duplicates by `(date, type, key fields)`

Property tests run 256 cases per CI run by default. They catch bugs example tests miss because the input space is too large to enumerate manually.

### When adding a new plugin

1. Implementation in `crates/rustledger-plugin/src/native/plugins/<name>.rs`
2. Tests at `crates/rustledger-plugin/tests/native_plugins_test.rs` covering the matrix above
3. Fixtures under `tests/compatibility/files/plugin/<name>/` if the plugin is a beancount reimplementation
4. At least one proptest case if numeric computation
5. Mutation-survival ≤ 10% on the new code (target; CI runs `cargo mutants` and warns today, see Phase 3 of the plugin-testing plan for the planned blocking gate)

### Why these requirements exist

See issue #992, which traced a single rendering bug to a chain of mutually-reinforcing test gaps:

- `(partial)` upstream test port (only the cost path was covered, not `@`/`@@`)
- `assert!(count >= 1)` — accepted both 1 emission AND 100 emissions
- Two parallel implementations of the same logic (plugin path vs query path) that diverged because nothing tied them together
- `is_total: bool` consumed without exhaustive matching

Each requirement above closes one of those gaps. Following all of them eliminates the bug class structurally.

## Questions?

Open an issue or discussion on GitHub.
