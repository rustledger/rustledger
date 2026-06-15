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

| Item | Notes |
|------|-------|
| **Plugin-commutativity property** | The one deferred member of the #1235 pipeline-property family, and the test-side of [compatibility bet #1](./index.md#1-finish-compatibility--make-drop-in-literally-true): assert that plugins marked commutative produce the same result regardless of application order. Needs a `COMMUTATIVE` trait marker before the property can be written. |
| **SemVer gate Tier-2 (core / parser)** | Extend `cargo-semver-checks` beyond the plugin DTOs to `rustledger-core` and `rustledger-parser` — the next crates third parties build against. Follow-up to #1233. |
| **`cargo-public-api` visibility** | Track the full public API surface with `cargo-public-api` so API changes show up in diffs, complementing the SemVer gate. Follow-up to #1233. |
| **OSS-Fuzz integration** | Google's continuous 24/7 fuzzing, auto-filing bugs on crashes. Needs `Dockerfile` + `build.sh` + `project.yaml` and a PR to google/oss-fuzz; builds on the existing `fuzz.yml` targets. |
| **dylint custom lints** | Project-specific lints via `dylint` for conventions clippy can't express (backing the unwrap/panic-in-lib rule, hot-path and sync-primitive conventions). Deferred from #1237. |
| **Incremental test running** | Only run tests affected by changed files via `cargo-nextest` file-to-test mapping — meaningful CI savings on partial changes. |
| **BQL file-sampling lift** | `compat-bql-test.py` caps execution at `MAX_FILES = 30`. Lift the limit via parallel execution and/or nightly-vs-PR sampling tiers so the headline compat number reflects the full corpus. |

## Exploring / Later

Genuinely uncertain — pursued only if it earns its keep against the gates already
in place. Each of these has a concrete reason it might *not* be worth it.

- **Differential testing against Beancount** — run `rledger` and `bean-check` on the same
  inputs and auto-detect divergence, reusing the compatibility corpus. The strongest
  candidate here: it directly serves the compatibility bet, and the corpus already exists.
  Open question is mostly how to triage *intended* deviations (the "fixable Python bugs"
  policy) from real ones without drowning in noise.
- **Contract testing for plugins** — property-test the plugin API contract: that a plugin
  can't crash or corrupt the host and that WASM sandbox isolation holds. Pairs with the
  stable-plugin-surface platform bet; worth it once the plugin ABI is the thing third
  parties depend on.
- **loom for concurrency** — model-check concurrent code paths with `loom` for interleaving
  bugs Miri and the grep ratchets miss. (Deferred from #1237.) Gated on there being enough
  hand-written concurrency to justify it — most parallelism today is structured rayon.
- **Benchmark regression detection** — benchmarks run but don't fail on regression. Adding
  criterion `--baseline` comparison with a significance threshold would make the
  performance bet's "protect the lead" claim enforceable rather than aspirational. The
  hard part is a stable enough CI baseline to avoid false alarms.
- **Cross-platform CI matrix** — extend beyond Linux x86_64 to macOS ARM64 and Windows for
  the parser/booking core. Justified by where users actually run, not for its own sake.

---

Shipped: see [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md) for completed testing & quality work.
