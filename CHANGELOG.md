# Changelog

Shipped work, by area. Forward-looking plans live in [docs/roadmap/](docs/roadmap/index.md); completed items land here so the roadmaps stay forward-only.

### Performance

- **Source double-allocation removed** — `Arc<str>` for source code instead of clone (Phase 0.1, ~16% faster, 50% less source memory).
- **Profile-Guided Optimization (PGO)** — release binaries built with benchmark profile data (Phase 0.2, ~13% faster).
- **LTO release profiles** — `thin` LTO on `release` (avoids Apple linker crash), `fat` LTO on dedicated `release-linux` and `wasm-release` profiles, with `codegen-units = 1` + `strip` (Phase 0.3).
- **Zero-copy string parsing** — parser returns borrowed `&str`/`Cow<str>` and interns later instead of eager `.to_string()` (Phase 1, ~7% faster).
- **FxHashMap / rustc-hash on hot paths** — non-cryptographic hashing for interned-string/currency keys across core, validate, booking, query, loader; inventory hot path is fxhash-only (Phase 2.4, issue #1237).
- **imbl persistent collections** — `Inventory.positions` uses `imbl::Vector` for O(1) clone via structural sharing, removing quadratic snapshot blow-up (Phase 2.5, issue #1086).
- **Full string interning** — `InternedStr` extended to payee/narration/tags/links on `Transaction` and `Document`; cache re-interning deduplicates 150+ strings/ledger (Phase 3, ~6% faster).
- **Rayon validation parallelization** — parallel transaction interpolation and independent checks, sorting kept sequential (Phase 4, ~5% faster).
- **Parallel query execution** — simple per-posting query evaluation runs via `par_iter()` above a threshold, `DISTINCT` dedup stays sequential (Phase 4.3).
- **parking_lot locks** — faster, smaller, non-poisoning `RwLock`/`Mutex` in query executor and LSP state (Phase 4.4).
- **Binary cache (rkyv)** — zero-copy deserialization cache keyed on BLAKE3 of path+mtime+size, with invalidation and `--no-cache`/`-C` CLI flags; 2.3x faster on cache hit (30ms → 13ms) (Phase 5, issue #939).
- **Logos lexer + structured rowan CST parser** — SIMD-accelerated tokenization and hand-written lossless CST, replacing the Chumsky combinator parser (Phase 6.1).
- **Parser fast paths** — empty-collection avoidance, SIMD escape check, in-parser string interning, hand-rolled Decimal/date parsing, `Cow` strings; 1K txns 1,204μs → 700μs, -42% (Phase 6.3, PR #812).
- **Validation fast paths** — precomputed tolerances, BigDecimal bypass when Decimal residual is zero, alloc-free account-name validation; 1K txns 210μs → 90μs, -57% (Phase 6.4, PR #814).
- **Parallel file loading** — sibling includes read + parsed in parallel via rayon with sequential order-preserving merge (DiskFileSystem only); multi-file ledgers load 2-4x faster (Phase 6.5, PR #813).

**Overall:** ~20x faster validation and ~34x faster balance reports vs Python beancount on 10K-transaction ledgers; ~13ms on cache hit.

### Importing & Ingestion

- Import trait system (`Importer` trait, `ImportResult`, registry)
- CSV importer with column mapping, date formats, and debit/credit split
- OFX/QFX importer
- CSV auto-inference: delimiter, date format, and column-role detection (`--auto`)
- `rustledger-ops` crate: pure operations for dedup, categorize, fingerprint, reconcile, merchants, and transfer detection
- Rules engine with substring, regex, and exact-match rules and priority ordering
- Built-in merchant dictionary (~230 patterns across groceries, dining, transport, subscriptions, etc.)
- Transaction fingerprinting via blake3 structural hashing for stable dedup
- Enriched import results (`EnrichedImportResult`) with confidence scores and categorization method
- Naive Bayes ML categorization trained on the user's ledger, wired into `rledger extract --suggest-categories`
- WASM import plugins: third-party importers as sandboxed `.wasm` modules
- Balance-directive generation via `rledger extract --balance`/`--balance-date` (amount user-supplied; automatic statement extraction still future)

### Testing & Engineering Quality

- **Phase 1 — Quick Wins:** Miri weekly UB detection (`miri.yml`), `cargo-nextest` for fast parallel CI tests, Codecov coverage reporting (`quality.yml`), and Criterion micro-benchmarks in CI (`bench-pr.yml`).
- **Phase 2 — Fuzzing infrastructure:** CI fuzzing (`fuzz.yml`) with `fuzz_parse`, `fuzz_parse_line`, `fuzz_query_parse` (query engine), and `fuzz_booking` targets, running on parser PRs and nightly.
- **Phase 3 — Compatibility enhancements:** Expanded BQL compat corpus to ~17 curated queries (`bql-queries.toml`) covering aggregates, date/string functions, and edge cases; file sampling via `compat-bql-test.py` (`MAX_FILES = 30`, plugin fixtures prioritized).
- **Phase 4 — Formal verification bridge:** Kani proof harnesses (`crates/rustledger-core/src/kani_proofs.rs`, `kani.yml`) verifying core invariants, plus TLA+ trace-to-test automation wired into `tla.yml` (19 specs).
- **Phase 5 — Mutation testing:** Per-package `cargo-mutants` matrix (`mutation.yml`, #1238) — each package mutated in its own fail-isolated job with its own time budget and per-package artifact upload.
- **Phase 6 — WASM testing:** `wasm-pack` Node.js + browser tests for `rustledger-wasm` (`wasm.yml`, `tests/node.rs`).
- **Pipeline-boundary property tests (#1235):** `pipeline_invariants.rs` across parser/booking/validate/query/plugin, plus `booking_phase_invariants.rs`, `tla_proptest.rs`, and `plugin_determinism.rs` — pinning parse/format roundtrip + idempotence, booking idempotence, validation determinism, plugin wire-format roundtrip, and query-result determinism.
- **Grep ratchets (#1237):** `check-sync-primitives.sh` (forbids `std::sync::Mutex`/`RwLock` in library code) and `check-hot-path-collections.sh` (forbids SipHash `HashMap`/`HashSet` in `fxhash-only` modules), wired into `ci.yml` alongside the existing `check-unsafe-invariant.sh` gate.
- **SemVer / API-stability gate (#1233):** `semver-plugin-types` CI job runs `cargo-semver-checks` against `rustledger-plugin-types` (Tier-1 plugin DTOs) on every PR.
- **FFI synth-pass parity (#1404):** `rustledger-ffi-wasi`'s `load_file`/`load_source` route loading through the canonical `process::load` pipeline instead of a duplicated partial loader, so the pre-booking synth pass (`auto_accounts`, `document_discovery`) runs through the JSON-RPC and WIT/component surfaces — previously it ran only natively. Added `load_synth_plugins.rs` (ffi-wasi) and component parity tests pinning generated-`Open` output, closing the coverage gap that let the divergence ship.

### Formal Verification

- Built 18 TLA+ specifications, 16 of which are model-checked on every CI run (`.github/workflows/tla.yml`).
- Conservation/inventory invariants: `Conservation.tla` (ConservationInvariant, NonNegativeInventory), `MultiCurrency.tla` (multi-currency conservation).
- Double-entry and account invariants: `DoubleEntry.tla` (TransactionsBalance, NoSelfTransfer), `AccountStateMachine.tla` (ClosedHaveZeroBalance, TypeOK), `Interpolation.tla` (AtMostOneNull, CompleteImpliesBalanced).
- Booking-method specs: `FIFOCorrect.tla`, `LIFOCorrect.tla`, `HIFOCorrect.tla`, `STRICTCorrect.tla`, `AVERAGECorrect.tla`, `NONECorrect.tla` — each verifying correct lot selection / booking-method semantics.
- System specs: `PriceDB.tla` (price database consistency), `ValidationCorrect.tla` (balance-assertion validation), `PluginCorrect.tla` (plugin execution ordering), `ConcurrentAccess.tla` (concurrent read/write safety), `QueryExecution.tla` (BQL query execution invariants).
- Illustrative demo specs (not in CI): `SimpleInventory.tla` (basic add/reduce) and `BuggyInventory.tla` (demonstrates TLC catching bugs); `FIFOCheck.tla` retained for historical reference.
- Found and fixed a real bug: `FIFOCheck.tla` revealed `inventory.rs` was selecting lots by insertion order instead of acquisition date; the TLC counterexample was converted to `crates/rustledger-core/tests/tla_fifo_bug_test.rs` and the bug fixed via date-based sorting in `reduce_ordered()`.
- Established CI runner tooling (`tools/tla2tools.jar`) with per-spec `.cfg` files and multi-core model-checking support.
