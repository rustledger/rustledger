# Performance

> Part of the [rustledger roadmap](./index.md).

Forward-looking performance work. rustledger is already 10-30x faster than Python Beancount on typical ledgers; this tracks the remaining optimizations and ideas, not what has already shipped.

## Now / In progress

Items that are partially done or the most valuable next steps.

| Item | Notes |
|------|-------|
| Bumpalo arena for AST nodes | Phase 6 (lexer + arena) is partial: the Logos lexer and structured CST parser shipped, but AST allocation still uses the global allocator. Move AST nodes into a [bumpalo](https://github.com/fitzgen/bumpalo) arena (~11 instructions/alloc, mass-reset on discard), which fits the parse → use → discard lifecycle exactly. The win depends on how alloc-bound parsing actually is — measure with `pipeline_bench` before and after rather than committing to a number up front. |
| Pre-allocate hot HashMaps | Add `.with_capacity()` in validation and query execution to avoid rehashing on known-size maps (`rustledger-validate`, `rustledger-query/src/executor.rs`). |

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
| Further parallelism | Extend rayon-based parallelism into additional independent stages where profiling shows multi-core headroom, keeping order-sensitive steps (sorting, booking) sequential for correctness. Exploratory. |

## Notes

- Benchmark each change with `cargo bench --bench pipeline_bench`; nightly CI tracks results on the benchmarks branch.
- Only pursue arena/mmap/streaming work if profiling shows the corresponding bottleneck on real workloads — correctness first.

---

Shipped performance work: see [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md).
