# Contributing to Rustledger

Thank you for your interest in contributing to Rustledger!

## Development Setup

### Prerequisites

- Rust 1.75+ (`rustup update stable`)
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

## Questions?

Open an issue or discussion on GitHub.
