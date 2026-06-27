# Performance

> Part of the [rustledger roadmap](./index.md).

Forward-looking performance work. rustledger is already 10-30x faster than Python Beancount on typical ledgers; this tracks the remaining optimizations and ideas, not what has already shipped.

## Now / In progress

Items that are partially done or the most valuable next steps.

| Item | Notes |
|------|-------|
| Bumpalo arena for AST nodes | Phase 6 (lexer + arena) is partial: the Logos lexer and structured CST parser shipped, but AST allocation still uses the global allocator. Move AST nodes into a [bumpalo](https://github.com/fitzgen/bumpalo) arena (~11 instructions/alloc, mass-reset on discard), which fits the parse → use → discard lifecycle exactly. The win depends on how alloc-bound parsing actually is — measure with `pipeline_bench` before and after rather than committing to a number up front. |
| Pre-size remaining hot HashMaps | Largely addressed — the dominant lever turned out to be the *hasher*, not capacity. Hot per-item maps (validation balance/tolerance, CSV-import header→column, query GROUP BY / pivot / window / price) used the default SipHash where the codebase standard is `FxHashMap`; now swapped across all three (≈ −8.3% validation, −5.6% import, SipHash eliminated in query). What's left is pre-sizing the query-executor maps with `with_capacity_and_hasher` on known-size inputs. |

## Next

Committed, well-scoped future work.

| Item | Notes |
|------|-------|
| Memory-mapped files for large ledgers | Optional `mmap` (via `memmap2`) above a size threshold (e.g. 50MB), with fallback to standard read for smaller files. Zero-copy load avoids one full read into a buffer; the payoff is concentrated in the largest files, where I/O dominates parse time. Gate on a benchmark with a representative large ledger before shipping. |
| Incremental LSP reparse | Re-parse only the edited region instead of the whole document on each keystroke. The Logos lexer + lossless rowan CST already give us the structure to support range-based reparsing in `rustledger-lsp`; this keeps editor latency flat as ledgers grow. |
| Remaining parser/validation micro-optimizations | Continue the fast-path approach (zero-alloc collections, SIMD escape/scan, hand-rolled numeric parsing) for any hot spots profiling still surfaces. |

## Exploring / Later

Aspirational ideas; not yet committed and may not pan out.

| Item | Notes |
|------|-------|
| Query-result caching / materialized views | Cache or pre-materialize results of repeated BQL queries (e.g. balance/inventory rollups) so dashboards and watch-mode workflows avoid recomputing from scratch. Needs an invalidation story tied to ledger changes. Exploratory. |
| Streaming / large-ledger handling | Process very large ledgers without holding the full directive set in memory at once — streaming parse/validate and chunked computation for ledgers that exceed comfortable memory budgets. Exploratory; depends on demand for 1M+ transaction files. |
| Further parallelism | Extend rayon-based parallelism into additional independent stages where profiling shows multi-core headroom, keeping order-sensitive steps (sorting, booking) sequential. The inverse is also open: validation *already* uses rayon, and on small ledgers its plumbing (~9% of instructions in a profile) is pure overhead — a size threshold that runs serially below N directives may help typical-ledger latency more than adding parallelism would. Exploratory. |
| Formatter allocation churn | `format_directives` is ~40% allocator-bound on large output — a fresh `String` / `format!` per line and per amount (measured with the `profile_format` example). The lever is rendering into one reused buffer. Deferred: `rledger format` is an occasional command, off the per-check hot path, so only worth it if it surfaces for a real user. |

## Notes

- Benchmark each change with `cargo bench --bench pipeline_bench`; nightly CI tracks results on the benchmarks branch.
- Per-subsystem cachegrind harnesses exist as `profile_*` examples (`pipeline` / `query` / `booking` / `validate` / `format` / `import`): build with `--profile profiling`, then run under `valgrind --tool=cachegrind` + `cg_annotate`.
- The booking lot inventory's `imbl::Vector` cost (~20% on cost-heavy ledgers) is a **deliberate** trade for O(1) BQL JOURNAL snapshots (#1086, documented on `core::Inventory`) — not a target; don't revert it to `Vec`.
- Only pursue arena/mmap/streaming work if profiling shows the corresponding bottleneck on real workloads — correctness first.

---

Shipped performance work: see [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md).
