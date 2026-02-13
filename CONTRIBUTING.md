# Contributing to Rustledger

Thank you for your interest in contributing to Rustledger!

## Development Setup

### Prerequisites

- Rust 1.85+ (`rustup update stable`) - Rust 2024 edition
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
2. Make your changes with clear, atomic commits
3. Ensure all tests pass: `cargo test`
4. Push and open a PR against `main`
5. Fill out the PR template completely

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
2. **Tests**: Are there sufficient tests for the changes?
3. **Beancount compatibility**: Does it match Python beancount behavior?
4. **Performance**: Any obvious performance regressions?
5. **Security**: Any potential vulnerabilities (especially in parser/loader)?
6. **Documentation**: Are public APIs documented?
7. **Style**: Does it follow project conventions?

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

## Questions?

Open an issue or discussion on GitHub.
