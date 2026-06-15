# Testing & Engineering Quality

Forward-looking roadmap for rustledger's testing infrastructure and engineering-quality
gates. This file tracks only not-yet-done work; shipped work lives in the changelog.

> Part of the [rustledger roadmap](./index.md).

## Now / In progress

Partially-done or actively-worth-doing-next work that builds on infrastructure
already in place.

| Item | Notes |
|------|-------|
| Promote `semver-plugin-types` to a **required** check | The `cargo-semver-checks` gate on `rustledger-plugin-types` runs on every PR (#1233); make it a required status check so accidental breaking changes to the published plugin DTOs can't be merged. |
| **unwrap/panic-in-lib cleanup** | Sweep library crates for `.unwrap()`/`panic!` in non-test code and replace with `Result`/`?` (per the project's "no `.unwrap()` in library code" rule). Deferred from #1237. |
| **Error message quality testing** | Compatibility suite counts errors but doesn't yet verify message helpfulness (location, type, actionable wording) vs `bean-check`. No script exists yet — the approach is a curated set of known-bad inputs with expected error patterns. |

## Next

Committed, well-scoped future items.

| Item | Notes | Rough effort |
|------|-------|--------------|
| **OSS-Fuzz integration** | Google's continuous 24/7 fuzzing, auto-files bugs on crashes. Needs `Dockerfile` + `build.sh` + `project.yaml` and a PR to google/oss-fuzz. Builds on the existing `fuzz.yml` targets. | ~1 day |
| **Incremental test running** | Only run tests affected by changed files using `cargo-nextest` file-to-test mapping. Significant CI-time savings on partial changes. | ~2-3 days |
| **dylint custom lints** | Project-specific lints via `dylint` to enforce conventions the standard clippy set can't (e.g. backing the unwrap/panic-in-lib rule, hot-path and sync-primitive conventions). Deferred from #1237. | — |
| **SemVer gate Tier-2 (core / parser)** | Extend `cargo-semver-checks` beyond the plugin DTOs to `rustledger-core` and `rustledger-parser`. Follow-up to #1233. | — |
| **`cargo-public-api` visibility** | Track the full public API surface with `cargo-public-api` so API changes are visible in diffs, complementing the SemVer gate. Follow-up to #1233. | — |
| **Plugin-commutativity property** | The one deferred member of the #1235 pipeline-property family: assert that plugins marked commutative produce the same result regardless of application order. Needs a `COMMUTATIVE` trait marker before the property can be written. | — |
| **BQL file-sampling lift** | `compat-bql-test.py` currently caps execution at `MAX_FILES = 30`. Lift the limit via parallel execution and/or nightly-vs-PR sampling tiers. | ~4 hours |

## Exploring / Later

Aspirational / brainstorm — not committed, may be reshaped or dropped.

- **loom for concurrency** — model-check concurrent code paths with `loom` to surface
  interleaving bugs the grep ratchets and Miri don't catch. (Deferred from #1237.)
- **Differential testing against Beancount** — run `rledger` and `bean-check` on the same
  inputs and auto-detect behavior divergence, reusing the compatibility corpus.
- **Chaos testing** — inject random failures (disk, network, memory pressure) and test
  graceful degradation; most useful for cache and file-loading code.
- **Contract testing for plugins** — property-test plugin API contracts, ensure plugins
  can't crash the host, and test WASM sandbox isolation.
- **Benchmark regression detection** — benchmarks run today but don't fail on regression;
  add statistical-significance testing (criterion `--baseline`) and block PRs above a
  threshold (e.g. >5%).
- **Visual regression testing** — snapshot CLI output formatting and error-message
  rendering; ensure colored output doesn't break.
- **Cross-platform testing matrix** — extend beyond Linux x86_64 to macOS ARM64, Windows,
  and Linux ARM64 for critical paths.
- **Load testing** — exercise very large ledgers (1M+ transactions), profile memory under
  load, and detect leaks in long-running processes.

---

Shipped: see [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md) for completed testing & quality work.
