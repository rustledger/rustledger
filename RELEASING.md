# Releasing rustledger

This document describes how to release a new version of rustledger.

## Overview

Releases are automated via [release-plz](https://release-plz.ieni.dev/) and GitHub Actions:

1. **Automatic**: release-plz creates a release PR from conventional commits
2. **You**: Review and merge the release PR
3. **Automatic**: Tag is created, triggering build and publish workflows

## How It Works

### Conventional Commits

Version bumps are determined by commit messages:

| Commit Type | Version Bump | Example |
|-------------|--------------|---------|
| `fix:` | Patch (0.0.x) | `fix: handle empty input` |
| `feat:` | Minor (0.x.0) | `feat: add new report type` |
| `feat!:` or `BREAKING CHANGE:` | Major (x.0.0) | `feat!: change API` |

### Automated Flow

```
Push to main
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
release-build.yml builds binaries
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

### 2. Review the release PR

release-plz automatically creates a PR titled "chore: release". Review:

- Version bump is correct
- Changelog entries look good
- CI passes

### 3. Merge the PR

Merge via the merge queue. release-plz will:

1. Create a git tag (e.g., `v0.9.0`)
2. Create a GitHub Release with changelog

### 4. Monitor the release

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

### Mergify Auto-merge

Release PRs from `release-plz` are automatically merged when CI passes (configured in `.github/mergify.yml`).

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
