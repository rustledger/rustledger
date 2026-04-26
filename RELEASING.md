# Releasing rustledger

This document describes how to release a new version of rustledger.

## Overview

Releases use [release-plz](https://release-plz.ieni.dev/) with **manual trigger**:

1. **You**: Trigger the release workflow manually
1. **Automatic**: release-plz creates a release PR from conventional commits
1. **You**: Review and merge the release PR
1. **Automatic**: Tag is created, triggering build and publish workflows

## How It Works

### Conventional Commits

Version bumps are determined by commit messages:

| Commit Type | Version Bump | Example |
|-------------|--------------|---------|
| `fix:` | Patch (0.0.x) | `fix: handle empty input` |
| `feat:` | Minor (0.x.0) | `feat: add new report type` |
| `feat!:` or `fix!:` | Major (x.0.0) | `feat!: change API` |

**Important:** Only `feat` and `fix` are "releasable" commit types. Other types (`chore`, `docs`, `refactor`, `test`, etc.) do NOT trigger version bumps, even with the `!` breaking change marker.

```bash
# ✅ Correct - triggers major version bump
git commit -m "feat!: add new required field to Config"

# ❌ Wrong - chore doesn't trigger releases, breaking change ignored
git commit -m "chore!: add new required field to Config"
```

### Release Flow

```
You trigger Release-plz workflow manually
     │
     ▼
release-plz creates/updates Release PR
  • Bumps versions in Cargo.toml
  • Generates CHANGELOG.md entries
  • Syncs npm package.json versions
     │
     ▼
You review and merge PR
     │
     ▼
release-plz creates git tag (v0.9.0)
     │
     ▼
release-build.yml builds:
  • Native binaries (8 platforms)
  • WASM package
  • FFI-WASI binary
  • VS Code extension (.vsix)
     │
     ▼
release-publish.yml distributes to:
  • crates.io (all workspace crates)
  • npm (@rustledger/wasm, @rustledger/mcp-server)
  • Docker (ghcr.io/rustledger/rustledger)
  • Homebrew, Scoop, COPR, AUR
```

## Release Process

### 1. Write conventional commits

```bash
git commit -m "feat: add balance sheet report"
git commit -m "fix: handle unicode in account names"
git push origin main
```

### 2. Trigger the release workflow

Go to **Actions** → **Release-plz** → **Run workflow** → Enable "Create release PR" → **Run**

Or use the CLI:

```bash
gh workflow run release-plz.yml -f create_pr=true
```

### 3. Review the release PR

release-plz creates a PR titled "chore: release". Review:

- Version bump is correct
- Changelog entries look good
- CI passes

#### Fixing missing version bumps

If release-plz missed a crate (e.g., internal bug fixes that don't change the API), manually bump it on the release PR branch:

```bash
# Checkout the release PR branch
git fetch origin
git checkout release-plz-<timestamp>

# Bump the crate version
sed -i 's/^version = "0.10.0"/version = "0.10.1"/' crates/<crate-name>/Cargo.toml

# Add changelog entry
# Edit crates/<crate-name>/CHANGELOG.md to add the new version section

# Update Cargo.lock and push
cargo check -p <crate-name>
git add -A
git commit -m "chore(<crate>): bump <crate-name> to 0.10.1"
git push
```

### 4. Merge the PR

Merge via the merge queue. release-plz will:

1. Create a git tag (e.g., `v0.9.0`)
1. Create a GitHub Release with changelog

### 5. Monitor the release

```bash
# Watch the build
gh run list --workflow=release-build.yml --limit 3

# Watch the publish
gh run list --workflow=release-publish.yml --limit 3
```

The release takes ~30-45 minutes to build all platforms.

## What Gets Released

### Binaries (8 targets)

| Platform | Target |
|----------|--------|
| Linux x64 | `x86_64-unknown-linux-gnu` |
| Linux x64 (static) | `x86_64-unknown-linux-musl` |
| Linux ARM64 | `aarch64-unknown-linux-gnu` |
| Linux ARM64 (static) | `aarch64-unknown-linux-musl` |
| macOS x64 | `x86_64-apple-darwin` |
| macOS ARM64 | `aarch64-apple-darwin` |
| Windows x64 | `x86_64-pc-windows-msvc` |
| Windows ARM64 | `aarch64-pc-windows-msvc` |

### VS Code Extension

The VS Code extension (`rustledger-vscode.vsix`) is built and attached to the GitHub Release. The extension version is automatically synced from the release tag (e.g., `v0.11.0` → extension version `0.11.0`).

The extension is distributed via GitHub Releases only (not the VS Code Marketplace). Users can:

- Download manually from the [releases page](https://github.com/rustledger/rustledger/releases)
- Use the extension's built-in auto-update feature

### Package Managers

| Channel | Registry/Repo |
|---------|---------------|
| crates.io | `rustledger`, `rustledger-*` |
| npm | `@rustledger/wasm`, `@rustledger/mcp-server` |
| Docker | `ghcr.io/rustledger/rustledger` |
| Homebrew | `homebrew-core` (official) |
| Scoop | `rustledger/scoop-rustledger` |
| COPR | `copr.fedoraproject.org/rustledger` |

## Configuration

### `release-plz.toml`

```toml
[workspace]
semver_check = true           # Use conventional commits for versioning
changelog_update = true       # Generate changelog
git_tag_enable = true         # Create git tags
git_release_enable = false    # release-build.yml handles GitHub releases
publish = false               # release-publish.yml handles crates.io publishing

[changelog]
commit_parsers = [...]        # Map commit types to changelog sections
```

### Workflow files

| File | Purpose |
|------|---------|
| `release-plz.yml` | Creates release PRs, syncs npm versions |
| `release-build.yml` | Builds binaries, creates GitHub Release |
| `release-publish.yml` | Distributes to crates.io, npm, Docker, Homebrew, Scoop, COPR, AUR |

### Trusted Publishing

Both crates.io and npm use OIDC trusted publishing - no API tokens required:

- **crates.io**: Uses `rust-lang/crates-io-auth-action` for tokenless publishing
- **npm**: Uses `--provenance` flag with OIDC

## Troubleshooting

### Release PR not created

Check that commits follow conventional commit format:

```bash
git log --oneline -10
```

### Release publish failed

Re-run just the publish workflow:

```bash
gh run rerun <run-id>
```

### Tag already exists error

If release-plz fails with "Reference already exists" for the tag:

```bash
# 1. Delete the tag locally and remotely
git push --delete origin v0.9.0
git tag -d v0.9.0

# 2. Create a PR with "chore: release" in the commit message
git checkout -b chore/trigger-release
git commit --allow-empty -m "chore: release v0.9.0"
git push -u origin chore/trigger-release
gh pr create --title "chore: release v0.9.0" --body "Retrigger release after tag fix"

# 3. Merge the PR to trigger the Release job
```

The `Release` job only runs when the commit message contains `chore: release`.

### Manual release (emergency)

If automation fails, you can still release manually:

```bash
# Update version
cargo set-version 0.9.0 --workspace

# Update npm packages
sed -i 's/\"version\": \"[^\"]*\"/\"version\": \"0.9.0\"/' packages/mcp-server/package.json

# Commit and tag
git add -A
git commit -m "chore: release v0.9.0"
git tag v0.9.0
git push origin main --tags
```

## Version Numbering

We follow [Semantic Versioning](https://semver.org/):

- **Major** (1.0.0): Breaking API changes
- **Minor** (0.2.0): New features, backward compatible
- **Patch** (0.1.1): Bug fixes, backward compatible

### What Counts as a Breaking Change?

cargo-semver-checks runs on every PR and will catch these:

| Change | Breaking? | Why |
|--------|-----------|-----|
| Adding a public field to a struct | **Yes** | Existing code using struct literals breaks |
| Removing a public field/method | **Yes** | Existing code using it breaks |
| Changing a function signature | **Yes** | Existing callers break |
| Adding a new public method | No | Existing code still works |
| Adding a new optional parameter with default | No | Existing code still works |

**Tip:** Use `#[non_exhaustive]` on public structs to allow adding fields without breaking changes:

```rust
#[non_exhaustive]
pub struct Config {
    pub name: String,
    // Future fields won't break consumers
}
```

### Manual Version Bumping with `release-plz set-version`

release-plz may not always detect breaking changes from commit messages. This happens because:

1. **Package comparison takes precedence**: release-plz compares the actual package contents between versions. If the package "looks the same" to cargo-semver-checks, it may not bump the version even with a `feat!:` commit.

1. **cargo-semver-checks has limitations**: It doesn't catch all breaking changes (e.g., adding required fields to structs, behavioral changes).

When the automatic release PR proposes the wrong version, use `release-plz set-version`:

```bash
# Install release-plz locally
cargo install release-plz

# Bump all workspace packages to a specific version
release-plz set-version \
  rustledger-core@0.10.0 \
  rustledger-parser@0.10.0 \
  rustledger-booking@0.10.0 \
  rustledger-plugin@0.10.0 \
  rustledger-validate@0.10.0 \
  rustledger-loader@0.10.0 \
  rustledger-query@0.10.0 \
  rustledger-importer@0.10.0 \
  rustledger@0.10.0 \
  rustledger-wasm@0.10.0 \
  rustledger-ffi-wasi@0.10.0 \
  rustledger-lsp@0.10.0

# IMPORTANT: Also update the workspace version in root Cargo.toml
# release-plz set-version only updates individual crates, not [workspace.package].version
# Use -i.bak for macOS compatibility, then remove backup
sed -i.bak 's/^version = ".*"/version = "0.10.0"/' Cargo.toml && rm Cargo.toml.bak

# This updates both Cargo.toml and CHANGELOG.md files
# Then commit and create a PR
git add -A
git commit -m "chore: release v0.10.0

BREAKING CHANGE: <describe the breaking change>"
git push -u origin chore/bump-v0.10.0
gh pr create --title "chore: release v0.10.0"
```

> **Note:** The `sed` command updates the `[workspace.package].version` field in the root `Cargo.toml`. This is required because `release-plz set-version` only updates individual crate versions, not the workspace version.

### When to Use Manual Version Bumping

Use `release-plz set-version` when:

- The automatic release PR proposes a patch/minor but you made a breaking change
- You added required fields to public structs (cargo-semver-checks misses this)
- You made behavioral changes that break existing code
- The `feat!:` or `BREAKING CHANGE:` marker wasn't detected

### Forgot to Mark a Breaking Change?

If a breaking change was merged without the `!` marker, the simplest fix is to use `release-plz set-version` as shown above.

Alternatively, you can try adding an empty commit (though this doesn't always work):

```bash
git checkout main && git pull
git checkout -b fix/mark-breaking-change
git commit --allow-empty -m "feat(crate-name)!: description of breaking change

BREAKING CHANGE: Describe what breaks and how to migrate."
git push -u origin fix/mark-breaking-change
gh pr create --title "feat(crate-name)!: mark as breaking change"
```

**Note:** Empty commits may not trigger version bumps because release-plz compares package contents. Use `set-version` for guaranteed results.
