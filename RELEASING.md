# Releasing rustledger

How to cut a new release of rustledger.

## Overview

Releases are cut manually:

1. Bump versions across the workspace and npm packages.
2. Open a `chore: release vX.Y.Z` PR and merge it once CI is green.
3. Create the GitHub Release for the new tag — this triggers the build and publish workflows.

There is no automatic version-bump bot. We removed `release-plz` because it was creating more friction than it was saving.

## Release Process

### 1. Decide the version

Pick a version per [SemVer](https://semver.org/):

- **Major** (`1.0.0`): breaking API change.
- **Minor** (`0.X.0`): new feature, backward compatible.
- **Patch** (`0.0.X`): bug fix only.

You are responsible for deciding what counts as breaking — there is no automated semver check on PRs. If you want to verify, run it locally:

```bash
cargo install cargo-semver-checks
cargo semver-checks check-release --feature-group all-features
```

### 2. Bump versions

The version surface is:

- Workspace `Cargo.toml`:
  - `[workspace.package].version`.
  - All 10 entries under `[workspace.dependencies]` that path-depend on a sibling crate (`rustledger-core`, `rustledger-parser`, `rustledger-loader`, `rustledger-booking`, `rustledger-validate`, `rustledger-query`, `rustledger-plugin`, `rustledger-plugin-types`, `rustledger-importer`, `rustledger-ops`). Their pinned `version = "X.Y.Z"` must match — `cargo publish` rejects a crate whose dep version doesn't match what's on crates.io.
- All 14 crate `Cargo.toml` files under `crates/` (each currently hardcodes its own `version = "X.Y.Z"` rather than inheriting from the workspace).
- `packages/mcp-server/package.json`: both `version` and the `@rustledger/wasm` entry under `dependencies`. **Don't try to update `package-lock.json`** — `@rustledger/wasm@X.Y.Z` doesn't exist on npm yet during the bump PR, so `npm install` fails with `ETARGET`. The publish workflow regenerates the lockfile after wasm is published.
- `packaging/rpm/rustledger.spec`: `Version`, `Source0` URL, and the `%setup -n rustledger-X.Y.Z` directory all hardcode the version. COPR pulls this file from the release tag via SCM integration, so missing this means COPR keeps building the old version.
- `Cargo.lock`: refreshed by `cargo check` after the Cargo.toml edits.

`packages/vscode/package.json` is *not* bumped here — the VS Code extension version is synced from the release tag at build time. The AUR `PKGBUILD`s under `packaging/arch/` also don't need manual edits — `release-publish.yml` `sed`-bumps them at release time. The Homebrew formula at `packaging/homebrew/rustledger.rb` is bumped automatically by `dawidd6/action-homebrew-bump-formula` during release-publish.

### 3. Open a release PR

```bash
git switch -c release/v0.14.0
git add -A
git commit -m "chore: release v0.14.0"
git push -u origin release/v0.14.0
gh pr create --title "chore: release v0.14.0" --body "Bump to v0.14.0."
```

Wait for CI to go green, then merge.

### 4. Create the GitHub Release

After the PR merges, fast-forward your local `main` and create the release pinned to that exact commit so the tag can't drift onto something newer:

```bash
git switch main
git pull --ff-only origin main
gh release create v0.14.0 --target "$(git rev-parse HEAD)" --generate-notes
```

`--target <sha>` is important — without it, `gh release create` tags whatever the default branch points to *at the moment the API request lands*, which races with any subsequent merges. Pinning to the SHA you just pulled guarantees the tag points at the version-bump commit.

This creates the `v0.14.0` tag and triggers two workflows:

- `release-build.yml` — builds binaries for all 8 platforms, the WASM package, the FFI-WASI binary, and the VS Code extension; attaches them to the release.
- `release-publish.yml` — distributes to crates.io, npm, Docker, Homebrew, Scoop, COPR, AUR.

The full release takes ~30–45 minutes.

### 5. Verify

```bash
gh run list --workflow=release-build.yml --limit 1
gh run list --workflow=release-publish.yml --limit 1

# After publish completes, confirm npm `latest` moved
npm view @rustledger/wasm version
npm view @rustledger/mcp-server version
```

Both npm queries should return the new version.

## What Gets Released

### Binaries

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

### VS Code extension

`rustledger-vscode.vsix` is built and attached to the release. The extension version is auto-synced from the release tag (e.g., `v0.14.0` → extension version `0.14.0`).

Distributed via GitHub Releases only (not the VS Code Marketplace). Users download manually or rely on the extension's built-in auto-update.

### Package managers

| Channel | Registry/Repo |
|---------|---------------|
| crates.io | `rustledger`, `rustledger-*` |
| npm | `@rustledger/wasm`, `@rustledger/mcp-server` |
| Docker | `ghcr.io/rustledger/rustledger` |
| Homebrew | `homebrew-core` (official) |
| Scoop | `rustledger/scoop-rustledger` |
| COPR | `copr.fedoraproject.org/rustledger` |
| AUR | `rustledger`, `rustledger-bin` |

## Trusted Publishing

crates.io and npm both use OIDC trusted publishing — no API tokens required:

- **crates.io**: `rust-lang/crates-io-auth-action` for tokenless publishing.
- **npm**: `npm publish --provenance` with OIDC.

Trusted-publish tokens are publish-scoped only — they cannot run `npm dist-tag`. The publish workflow handles `latest`-tag correctness at publish time by refusing to publish a version older than the registry's current `latest`. Post-hoc retagging via the workflow isn't possible without a long-lived `NPM_TOKEN`.

## Workflow files

| File | Purpose |
|------|---------|
| `release-build.yml` | Builds binaries, WASM, FFI-WASI, VSCode extension; attaches to GitHub Release |
| `release-publish.yml` | Distributes to crates.io, npm, Docker, Homebrew, Scoop, COPR, AUR |

## Troubleshooting

### A `release-publish` job failed mid-distribution

Re-run only the failed jobs:

```bash
gh run list --workflow=release-publish.yml --limit 3
gh run rerun --failed <run-id>
```

The publish workflow is idempotent. Already-published artifacts are skipped (the npm step refuses any version older than `latest` on the registry; `cargo publish` exits gracefully on "already exists").

### npm `latest` points at the wrong version

The publish workflow's monotonicity guard prevents stale-tag re-dispatches from clobbering `latest`. If you somehow get into a bad state anyway, repairing `latest` requires a personal `npm dist-tag add` from an account with publish rights — trusted-publish tokens can't do it. (Background: this happened during the v0.13.0 release; see #918.)

### Tag already exists

```bash
git push --delete origin v0.14.0
git tag -d v0.14.0
gh release create v0.14.0 --generate-notes
```

### Forgot to bump a crate

If `cargo publish` fails for a crate because crates.io rejects "already exists", that's the safe path — the publish step skips it and continues.

If you discover the missed bump *after* the release tag exists: cut a follow-up patch release (e.g., `v0.14.1`) with the missing bump.
