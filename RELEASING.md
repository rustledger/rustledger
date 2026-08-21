# Releasing rustledger

How to cut a new release of rustledger.

## Overview

Releases are cut manually:

1. Bump versions across the workspace and npm packages.
1. Run a pre-flight smoke check (`tsc`, `wasm-pack build`) — catches the surfaces CI doesn't exercise per-PR.
1. Open a `chore: release vX.Y.Z` PR and merge it once CI is green.
1. Create the GitHub Release for the new tag — this triggers the build and publish workflows.

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

Bump the Cargo surface with `cargo set-version` (in the dev shell). Do not
hand-edit it: there are 17 crates carrying a literal `version`, plus 15
`[workspace.dependencies]` entries whose pinned version must match, and
`cargo publish` rejects a crate whose dep version disagrees with what is on
crates.io.

```bash
cargo set-version 0.22.0     # workspace package version, every member's
                             # `[package] version`, and the sibling pins
                             # under `[workspace.dependencies]`
cargo check --workspace      # refreshes Cargo.lock
```

`cargo set-version` does **not** touch these, and each has broken a release
before:

- **`packages/mcp-server/package.json`** — bump `version` only. It is a
  standalone npm package whose version comes from no Cargo.toml.

  **Leave the `@rustledger/wasm` dependency alone**, and leave
  `package-lock.json` alone with it. That version does not exist on npm until
  the publish workflow's earlier job puts it there, so a manifest naming it
  cannot install: `npm ci` fails `ETARGET`, which fails the `MCP Server` CI
  job, which `build` requires — and the release PR can never merge.
  `release-publish.yml` sets the dependency to the release version itself,
  just before its `npm install`, the same way it force-syncs the package
  version.

  Both force-syncs exist because the manual step was missed: v0.17.0 shipped
  with `package.json` still at 0.16.5, so `@rustledger/mcp-server@0.17.0` was
  never published. The dependency one was added during the v0.22.0 cut, which
  was the first release after the `MCP Server` gate landed (#1885) and so the
  first to hit the deadlock.
- **`packaging/rpm/rustledger.spec`** — `Version`, the `Source0` URL, and the
  `%setup -n rustledger-X.Y.Z` directory all hardcode the version. COPR pulls
  this from the release tag, so missing it means COPR keeps building the old
  version — which is what happened between v0.16.5 and v0.21.0. Also check
  `BuildRequires: rust >= X.Y` against `[workspace.package].rust-version`: an
  out-of-date pin makes COPR fail at parse time on edition2024 syntax (#927).
- **Eight standalone lockfiles.** Every `Cargo.lock` outside the root belongs
  to a nested project that is not a workspace member — the four `fuzz`
  targets, the two `sample_stub` test fixtures, and the two `examples/wasm-*`
  templates. Each records path-dependent `rustledger-*` versions, and neither
  `cargo set-version` nor `cargo check --workspace` touches any of them.
  Regenerate them all:

  ```bash
  for lock in $(git ls-files '*Cargo.lock' | grep -v '^Cargo.lock$'); do
    cargo update --manifest-path "$(dirname "$lock")/Cargo.toml" --workspace
  done
  ```

  `--workspace` updates only the path dependencies, leaving third-party
  versions alone, so this cannot smuggle an unrelated dependency bump into a
  release commit.

  This is not theoretical bookkeeping: `crates/rustledger-ffi-wasi/fuzz/Cargo.lock`
  was still recording `0.20.2` two releases after that version shipped,
  because the instructions here named no such file. Only the two fixture
  locks moved in the v0.21.0 release commit, which is what a hand-maintained
  list of files looks like when it drifts.

Not bumped here: `packages/vscode/package.json` (synced from the release tag
at build time), the AUR `PKGBUILD`s under `packaging/arch/` (`release-publish.yml`
`sed`-bumps them), and the Homebrew formula (homebrew-core **autobumps** —
BrewTestBot opens the PR itself, roughly every 3 hours).

`crates/rustledger-lsp/Cargo.toml` carries a comment worth reading before you
try to hand-set a crate's version to signal a breaking change: the workspace
runs in lockstep, `cargo set-version` overwrites anything hand-written, and the
only result is a downstream pin no published crate can satisfy. Breaking
changes belong in the release notes.

### 3. Pre-flight smoke check

Before opening the release PR, build the things CI doesn't exercise on every PR. The mcp-server in particular has its own `tsc` step that the regular CI matrix doesn't run, and a TS error there silently blocks `Publish MCP server to npm` (this hid an `amount`/`date` type bug across both v0.13.0 and v0.14.0 — see #926).

```bash
# Every crate in release-publish.yml's CRATES array must already EXIST on
# crates.io. Trusted publishing cannot create one, so a crate added since the
# last release fails the crates.io job part-way through and takes every
# dependent crate down with it — which is how v0.22.0 broke, with
# rustledger-returns and rustledger-budget both correctly listed and neither
# ever published. Without `--check-registry` this is the offline per-PR check
# that the array matches the workspace.
python3 scripts/check-publish-crates.py --check-registry

cargo check --workspace --all-features --all-targets

# mcp-server: needs @rustledger/wasm@<previous version> available on npm to install.
# If you've already bumped the dep to ^X.Y.Z (which doesn't exist yet),
# revert that line, build, then re-apply before committing.
( cd packages/mcp-server && npm ci && npm run build )

# wasm: catches breakage in the browser target (e.g., the jiff `js` feature
# regression in #925).
( cd crates/rustledger-wasm && wasm-pack build --target web --release )
```

### 4. Open a release PR

```bash
git switch -c release/v0.14.0
git add -A
git commit -m "chore: release v0.14.0"
git push -u origin release/v0.14.0
gh pr create --title "chore: release v0.14.0" --body "Bump to v0.14.0."
```

Wait for CI to go green, then merge.

### 5. Create the GitHub Release

After the PR merges, fast-forward your local `main` and create the release pinned to that exact commit so the tag can't drift onto something newer:

```bash
git switch main
git pull --ff-only origin main
gh release create v0.14.0 --target "$(git rev-parse HEAD)" --generate-notes
```

`--target <sha>` is important — without it, `gh release create` tags whatever the default branch points to *at the moment the API request lands*, which races with any subsequent merges. Pinning to the SHA you just pulled guarantees the tag points at the version-bump commit.

This creates the `v0.14.0` tag and starts a chain of **three** workflows:

- `release-build.yml` — builds binaries for all 8 platforms, the WASM package, the FFI-WASI binary, the FFI-Component (wasip2) wasm, and the VS Code extension; attaches them to the release.
- `release-publish.yml` — distributes to crates.io, npm, Docker, Scoop, COPR, AUR (Homebrew autobumps separately).
- `release-test.yml` — fires on `workflow_run` once Release Publish *completes*, success **or** failure, and checks the published channels actually serve the new version. It used to run only on success, so one expired packaging credential could suppress the verification entirely: at v0.22.0 a stale COPR token failed the run and nothing checked crates.io or npm at all. This is the one that catches a publish that "succeeded" without shipping: v0.17.0 passed build and publish while `@rustledger/mcp-server@0.17.0` was never published, because `package.json` was still 0.16.5.

The first two run in parallel (see the race note under Troubleshooting); the
third waits on the second. The full release takes ~30–45 minutes.

`rustledger-ffi-component-<tag>.wasm` must end up attached to the release —
rustfava and the desktop app resolve it from there, so a build that drops it
breaks them without failing anything here.

### 6. Verify

```bash
gh run list --workflow=release-build.yml --limit 1
gh run list --workflow=release-publish.yml --limit 1
gh run list --workflow=release-test.yml --limit 1   # runs after publish

# After publish completes, confirm npm `latest` moved
npm view @rustledger/wasm version
npm view @rustledger/mcp-server version

# The FFI component artifact rustfava and desktop depend on. Exact match:
# the release also carries `...wasm.sha256`, so a substring grep passes when
# only the checksum was uploaded and the wasm itself is missing.
gh release view vX.Y.Z --json assets --jq '.assets[].name' \
  | grep -Fxq "rustledger-ffi-component-vX.Y.Z.wasm" && echo "component attached"
```

Both npm queries should return the new version. Check all three workflows —
`release-test.yml` is the only one that looks at what the registries actually
serve, so a green build and publish on their own do not mean the release
shipped.

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
| COPR | `copr.fedorainfracloud.org/rustledger` |
| AUR | `rustledger`, `rustledger-bin` |

## Trusted Publishing

crates.io and npm both use OIDC trusted publishing — no API tokens required:

- **crates.io**: `rust-lang/crates-io-auth-action` for tokenless publishing.
- **npm**: `npm publish --provenance` with OIDC.

Trusted-publish tokens are publish-scoped only — they cannot run `npm dist-tag`. The publish workflow handles `latest`-tag correctness at publish time by refusing to publish a version older than the registry's current `latest`. Post-hoc retagging via the workflow isn't possible without a long-lived `NPM_TOKEN`.

## Workflow files

| File | Purpose |
|------|---------|
| `release-build.yml` | Builds binaries, WASM, FFI-WASI, FFI-Component, VSCode extension; attaches to GitHub Release |
| `release-publish.yml` | Distributes to crates.io, npm, Docker, Scoop, COPR, AUR (Homebrew autobumps separately) |
| `release-test.yml` | Runs after Release Publish completes; verifies the published channels serve the new version |

## Adding a new workspace crate

Three places must be updated when introducing a new `rustledger-*` crate. Skipping any of them silently breaks the next release.

1. **Workspace `Cargo.toml`**: add a `[workspace.dependencies]` entry with the version pinned to the current workspace version. Crates that depend on it use `path = "..."` from there.

1. **`.github/workflows/release-publish.yml`** — add the crate to the `CRATES=()` array in the `Publish to crates.io` step, **in dependency order**. If your new crate is depended on by `rustledger-plugin`, it must appear before plugin in the array, otherwise plugin's publish fails with `failed to select a version for the requirement`. (This was the bug we hit in v0.14.0 with `rustledger-ops`; fixed in #924.)

1. **First crates.io publish must be manual** — trusted-publishing OIDC tokens *cannot create new crates*, only push new versions of existing ones. Before the first release that includes the new crate:

   ```bash
   cargo login <a personal API token from crates.io>
   cargo publish -p rustledger-<crate>
   ```

   Then go to `https://crates.io/crates/rustledger-<crate>/settings` and configure trusted publishing for this repo's release-publish workflow. After that, all subsequent versions publish via the normal flow.

## Troubleshooting

### A `release-publish` job failed mid-distribution

Re-run only the failed jobs:

```bash
gh run list --workflow=release-publish.yml --limit 3
gh run rerun --failed <run-id>
```

The publish workflow is idempotent. Already-published artifacts are skipped (the npm step refuses any version older than `latest` on the registry; `cargo publish` exits gracefully on "already exists").

### Race between `Release Build` and `Release Publish`

`Release Build` is triggered by the tag push (`on: push: tags: 'v*'`); `Release Publish` is triggered when the GitHub release is published (`on: release: types: [published]`). In the usual `gh release create` flow the tag push and the release-published event happen close together, so the workflows run **in parallel**. `Build Docker images` and `Update AUR (rustledger-bin)` need binaries from the GitHub release; if they start before `Release Build` finishes uploading them, they fail at the extract step. Re-run them after `Release Build` is `success`:

```bash
gh run view <release-publish-run-id> --json jobs --jq '.jobs[] | select(.conclusion == "failure") | .databaseId'
gh run rerun --failed --job=<job-id>
```

### COPR build wasn't triggered

`Trigger COPR build` fails with `Login invalid/expired`. COPR tokens expire
(180 days), and the job authenticates from **repository secrets**, not from
any file in the tree — a local `~/.config/copr` does nothing for CI. Renew at
<https://copr.fedorainfracloud.org/api>, then set both halves of the pair;
each prompts with hidden input, so neither value lands in shell history:

```bash
gh secret set COPR_LOGIN   # the `login` field from the COPR page
gh secret set COPR_TOKEN   # the `token` field
gh run rerun --failed <release-publish-run-id>
```

`username` is hardcoded in the workflow, so only those two move. Until this
succeeds COPR keeps building the previous version — silently, which is why
the job fails the run rather than warning.

### Homebrew formula didn't update

There's nothing to do — homebrew-core **autobumps** rustledger. BrewTestBot detects each GitHub release and opens the `rustledger <version>` PR itself (~every 3 hours); it merges after Homebrew CI passes. Check progress:

```bash
gh search prs --repo Homebrew/homebrew-core "rustledger" --json title,state,url
```

(There is no Homebrew job in `release-publish.yml` — a manual `brew bump-formula-pr` is rejected for autobump formulae. To opt out of autobump, add `no_autobump!` or a `livecheck`/`skip` to the formula.)

### Need to redrive `Release Publish` after a workflow fix

`gh workflow run "Release Publish" -f tag=vX.Y.Z` runs the workflow YAML from `main` against source checked out at the tag. So **workflow fixes** pushed to main after a tag still apply on retrigger — but **source-tree fixes do not** (the checkout is at the tag, not main). If the failing job needs source changes, you have to cut a patch release (e.g., the v0.14.1 mcp-server TS fix that couldn't be back-redriven into the v0.14.0 publish).

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
