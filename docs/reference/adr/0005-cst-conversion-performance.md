# ADR-0005: CST Conversion Performance (green-tree walking)

## Status

Accepted (June 2026).

**Decision:** ship the parse cache (recommendation 1) and accept the cold-parse
CST cost (recommendation 2). The **green-tree rewrite (Phase 2) is declined** -
the empirical findings put its ceiling at ~20-25% off cold parse for a large,
compat-risky rewrite of `convert.rs`, which does not justify the risk while the
parse cache recovers the cost users actually feel (repeated runs) at no risk.

Shipped: parse cache for `report` (#1314) and `query` (#1315); `report` /
`query` / `check` unified on one cache path with `--no-cache` (#1316); the two
edge cleanups #1311 / #1312. The Phase 2 design below is retained as a record
of what was evaluated and why it was not pursued; revisit only if cold-parse
latency (not repeated-run latency) is later shown to matter enough to justify
the rewrite.

Original status: Proposed (June 2026), updated with
[Empirical findings](#empirical-findings-june-2026).

## Context

ADR-0003 records the migration to a lossless CST (the `#1262` series): a Logos
lexer feeds a rowan green-tree builder, and `cst::convert::parse_via_cst` walks
the resulting tree to produce the typed `ParseResult`. The CST is what powers
the opinionated formatter and the CST-backed LSP handlers (rename, selection
range, range formatting), so it is the strategic direction and is not in
question here.

The migration carried a performance cost that became visible on the nightly
**balance-report benchmark**, which runs `rledger report <10k-txn-file>
balances`:

| Date | rustledger balance report |
|------|---------------------------|
| through 2026-06-08 | ~37 ms |
| 2026-06-09 onward | ~106-138 ms |

The jump lands exactly on `#1282` (`#1262` phase 3.7), which changed
`rustledger_parser::parse` from the fast direct parser to unconditionally call
`parse_via_cst`; `#1283` then deleted the direct parser. Earlier history shows
the direct parser was itself a deliberate "~3x" win (`d65a62fd`,
`winnow_parser`).

Why only the report regressed while the `check` validation benchmark stayed
flat at ~37 ms: `check` **caches parse output to disk**
(`crates/rustledger/src/cmd/check.rs`), so its
repeated benchmark runs are cache hits that skip parsing. `report` has no cache
and re-parses on every invocation, so it pays the full CST cost every time. The
benchmark dashboard only tracks `balances` and `check`, so the parser slowdown
was masked everywhere except the one un-cached path.

Two already-merged PRs trimmed the edges:

- **#1311** - skips `balance_view()` cloning for pad-free ledgers and removes a
  redundant deep-clone from `process_pads`. ~132 -> ~116 ms.
- **#1312** - fuses five top-level `children()` walks in `parse_via_cst` into one
  pass. ~124 -> ~118 ms on the parse-bound `accounts` report.

Neither touches the dominant cost. This ADR proposes how to reclaim the rest.

## Cost model

A flat `perf` profile of `rledger report <10k> accounts` (a parse-bound path;
`accounts` does no balance math) attributes ~40% of total runtime to CST
construction and traversal:

```
18.24%  rustledger_parser::cst::convert::parse_via_cst
 3.73%  rowan ... to_next_sibling_or_token
 3.16%  rowan NodeCache::token
 3.15%  rowan PreorderWithTokens::next
 2.96%  cst::convert::convert_transaction
 1.95%  rowan SyntaxNode::first_child_or_token
 1.73%  cst::lossless_tokens::lossless_kind_tokens
 1.62%  rowan SyntaxElementChildren::next
 1.20%  rowan cursor::free
 0.91%  rowan NodeCache::node
 0.90%  rowan NodeData::new
 0.88%  rowan GreenNode::new
 ...    libc malloc / free / memmove  (~10% aggregate)
```

The cost decomposes into two distinct, separately-addressable layers.

### Layer A - red-node materialization

rowan has two trees. The **green tree** (`GreenNode`/`GreenToken`) is the
compact, immutable, deduplicated representation the builder produces; nodes know
only their own length, not their absolute position. The **red tree**
(`SyntaxNode`/`SyntaxToken`, a.k.a. the cursor layer) is a lazily-materialized
overlay that adds parent pointers and absolute offsets. Every time code touches
a `SyntaxNode` child, rowan allocates a reference-counted `NodeData` for it and
later frees it (`NodeData::new`, `cursor::free`, the `malloc`/`free` churn).

`parse_via_cst` and the entire `cst::ast` + converter layer are built on the
**red** tree: `ast_node!` wraps a `SyntaxNode` (`ast.rs:109`), and every
converter walks `node.syntax().children_with_tokens()` (the dominant traversal
idiom throughout `convert.rs`). So conversion materializes a red node for essentially every node
in the file, drives the allocator hard, and chases pointers through the cursor
API (`PreorderWithTokens`, `SyntaxElementChildren`, `first_child_or_token`,
`to_next_sibling_or_token`).

### Layer B - redundant per-node accessor re-walks

The typed AST accessors each re-walk a node's children from scratch. `children::<N>(node)`
(`ast.rs:103`) is `node.children().filter_map(N::cast)`. A single
`convert_transaction` calls `.date()`, `.flag()`, `.strings()`, `.tags()`,
`.links()`, `.postings()`, plus an explicit `children_with_tokens()` walk and a
`convert_meta_entries()` walk - **each one re-iterates the same TRANSACTION
node's children and re-materializes the same red nodes**. For a posting-heavy
transaction that is roughly 8x redundant traversal of the same child list.

Layer B is cheaper to fix and lower risk than Layer A. They compose: fixing B
reduces the number of red materializations, fixing A removes the per-materialization
allocation cost.

## Empirical findings (June 2026)

The plan below was partly validated against measurements before committing to the
risky parts. Two results changed the recommendation.

### Phase 1 (Layer B) is performance-neutral

`convert_transaction`'s three full-children body walks (postings, meta entries,
body tags/links) were fused into a single pass. Output stayed byte-identical (all
529 parser tests + corpus + CST baselines green). The isolated parse bench
(`parse_large/1000`, criterion) moved **within ±2% noise** across three runs
(5.70 / 5.84 / 5.77 ms) - **no improvement**. The change was discarded.

Reason: a single converter is a small slice (`convert_transaction` is 3.2% self),
and on typical transactions the "redundant" walks find nothing to do, so removing
them saves only iteration overhead - which is cheap. Layer B is not a lever.

### A clean isolated-parse profile reshapes the cost model

Profiling a tight `parse()`-only loop over a 10k-directive ledger (no report,
booking, or I/O) attributes the cost much more broadly than "redundant walks":

| Bucket | ~share | Frames |
|--------|--------|--------|
| `parse_via_cst` **self** | ~32% | the big inlined full-file passes (`walk_descendants_once` over every token, the directive loop, span fixup) |
| red-cursor traversal | ~18% | `to_next_sibling_or_token`, `PreorderWithTokens::next`, `SyntaxElementChildren::next`, `first_child_or_token`, `first_child` |
| allocator | ~15% | `malloc`/`free`/`memmove`/`_int_malloc`/`cfree`/`malloc_consolidate` |
| red-node materialization | ~4.5% | `NodeData::new`, `cursor::free`, `Arc::drop_slow` |
| green build + lex | ~6% | `NodeCache::token/node`, `GreenNode::new`, `parse_structured` |
| conversion data work | ~9% | `convert_transaction`, `lossless_kind_tokens`, `Spanned<Posting>` drop, accessors |

Implications:

- The red-tree overhead that a green-tree rewrite (Phase 2) targets is the
  traversal + materialization buckets, **~20-25%** combined, concentrated in the
  full-file `walk_descendants_once` pass and the per-posting accessors - not the
  per-directive body walks. So Phase 1 as originally scoped could never have
  helped; a green-tree rewrite's realistic ceiling is **~20-25% off parse**, not
  the 2-3x.
- The 2-3x gap versus the deleted direct parser is **structural**: the CST
  inherently builds a green tree (lex + build ~6%) and overlays a red tree to
  walk it; the direct parser did neither (tokens -> AST directly). The old
  ~37 ms report time is **not reachable while keeping the lossless CST**, by any
  amount of conversion tuning.

### Revised recommendation

Ranked by value / risk:

1. **Parse cache for `report` (and `query`).** `check` already caches parse
   output to disk; extending that to the other un-cached CLI commands recovers
   the *entire* parse cost on repeated invocations - the real-world common case -
   with low risk and zero parser changes. (Does not help a cold first run, e.g.
   the nightly benchmark, but helps users.) **Highest value/risk; recommended
   first.**
2. **Accept the cold-parse cost.** The lossless CST is the strategic direction
   (it powers the formatter and LSP); ~130 ms for a 10k balance report is still
   ~27x faster than `beancount`. A legitimate stopping point.
3. **Green-tree walking (Phase 2 below).** ~20-25% off cold parse for a large,
   compat-risky rewrite of `convert.rs`. Worth it only if cold-parse latency is
   later shown to matter enough to justify the risk; if pursued, target the
   full-file `walk_descendants_once` pass first (the biggest single red-walk),
   measured before committing to the full converter.
4. **Lazy `compute_alignment` (Phase 3).** ~0.7% today; do only if Phase 3's
   other costs shrink and it becomes visible.

The phased plan below stands as the *implementation* design **if** a green-tree
rewrite is chosen, but it is no longer the default path. Phase 1 (single-pass
converters) is dropped as proven neutral.

## Goals / non-goals

**Goals**

- Recover the bulk of the `parse_via_cst` regression (target: back under ~60 ms
  on the 10k balance report; stretch: near the old ~37 ms).
- Zero change to parser output. The corpus and CST output baselines must stay
  byte-identical at every step.
- Keep the lossless CST and the typed-AST surface the formatter and LSP depend
  on.

**Non-goals**

- Reviving the deleted direct parser or a second parse path. `#1262`
  deliberately unified on one parser; ADR-0003 stands.
- Changing the grammar, token set, or any diagnostic.
- Speeding up booking/validation/report rendering (separate concerns).

## Decision (proposed)

Optimize the conversion in place, in phases ordered by risk, with the parser
baselines as a hard gate between each. Land each phase as its own PR.

### Phase 0 - measurement harness (prerequisite)

Before touching conversion, make the win measurable in CI-comparable form:

- Add a criterion bench `parse_via_cst_10k` in
  `crates/rustledger-parser/benches/` that parses a generated 10k-directive
  source and reports ns/iter. This isolates parse from report rendering and
  from the disk cache, so regressions/improvements are attributable.
- Confirm the existing `corpus_baseline` and `cst_baseline` integration tests
  run locally (they hash `ParseResult` / CST output against a stored baseline -
  these are the correctness gate; a behavior change fails them).

No behavior change. Mergeable on its own.

### Phase 1 - single-pass per-node converters (Layer B) — DROPPED (proven neutral)

> **Outcome:** implemented for `convert_transaction` and measured
> performance-neutral (within ±2% noise, output byte-identical). See
> [Empirical findings](#empirical-findings-june-2026). Retained below only to
> document what was tried and why it does not help. Do not pursue.

Eliminate the redundant accessor re-walks. For each directive converter, walk
the node's children **once** and dispatch by kind into local accumulators,
instead of calling N accessors that each re-walk.

Concretely, replace the accessor-call style:

```rust
let date  = node.date()?;          // walk children, find DATE
let flag  = node.flag();           // walk children, find FLAG
let strs  = node.strings()...;     // walk children, find STRING tokens
let tags  = node.tags()...;        // walk children, find TAGs
let links = node.links()...;       // walk children, find LINKs
// + an explicit children_with_tokens() walk for body tags/links
// + convert_meta_entries(node.syntax())  (another walk)
```

with one walk that classifies each child token/node as it is seen:

```rust
let mut date = None; let mut flag = None;
let mut strings = SmallVec::new(); let mut tags = Vec::new(); ...
for el in node.syntax().children_with_tokens() {
    match el { Token(t) => match t.kind() { DATE => ..., FLAG => ..., STRING => ..., TAG => ..., LINK => ... },
               Node(n) => match n.kind() { POSTING => ..., META_ENTRY => ... } }
}
```

- Start with `convert_transaction` (the hottest converter and the one with the
  most accessors) to validate the approach and measure, then apply the same
  shape to the other directive converters.
- The typed accessors in `ast.rs` stay (the formatter and LSP use them); this
  changes only the converters' internal traversal.
- This keeps the red tree. Expected: removes most of the *redundant*
  materializations; does not remove the per-node materialization itself.

Risk: low-medium. Pure internal refactor; output-identical; gated by baselines.
Each converter is independent, so this can be sliced into a few small PRs
(transaction first, then the rest).

### Phase 2 - green-tree conversion (Layer A) — DECLINED

> **Decision:** not pursued (see [Status](#status)). ~20-25% off cold parse for
> a large, compat-risky rewrite of `convert.rs` does not justify the risk while
> the parse cache already recovers the repeated-run cost. Retained below as a
> record of the evaluated approach; revisit only if cold-parse latency is later
> shown to matter.

Convert by walking the **green** tree directly, materializing red nodes only
where genuinely needed, so the per-node `NodeData` allocation disappears.

The challenge is offsets: green nodes carry only their own text length, so
absolute spans must be computed by threading a running offset down the walk.
rowan exposes this via `GreenNodeData::children()` (yielding
`GreenChild`/`Cow<GreenNodeData|GreenTokenData>` with `text_len`) - accumulate
`offset` as you iterate siblings, recurse with `offset + child_start`.

Proposed shape:

- Introduce a thin internal walker over `GreenNodeData` that yields
  `(kind, absolute_text_range, &GreenTokenData|&GreenNodeData)` without touching
  the cursor layer. `bom_offset` folds into the running offset exactly as today.
- Re-express the Phase-1 single-pass converters against this walker. Token text
  comes from `GreenTokenData::text()`; spans from the accumulated offset; all
  the existing classification logic is unchanged.
- Keep `walk_descendants_once` and the error-extraction passes on whichever
  representation is cheaper; they can move to the green walker in the same way.
- The public `ParseResult.syntax_root` (a `GreenNode`) and the typed-AST surface
  are unaffected - we are changing only how `parse_via_cst` reads the tree it
  already built, not what it stores or exposes.

Risk: high. This is the large, delicate change. Mitigations:

- Land it converter-by-converter behind the Phase-1 refactor, so each step is a
  small, output-identical diff gated by the baselines.
- Offset arithmetic is the main hazard (off-by-one against the red tree's
  `text_range`). The CST baseline (which stores exact spans) catches any drift
  immediately.
- Keep a temporary debug assertion in dev builds that, for a sample of nodes,
  compares the green-walked absolute range against the red `text_range()` of the
  same node, and remove it once baselines + fuzz are green.

### Phase 3 - lazy alignment (optional, small)

`parse_via_cst` eagerly calls `compute_alignment` (`#1299`) on every parse to
cache the formatter's column layout, but only the formatter/LSP/FFI/WASM format
paths read `ParseResult.alignment`; `report`/`check`/`query`/`validate` never
do. The profile shows this is <1% today, so this is low priority, but if Phase 2
shrinks everything else it becomes proportionally visible. If so, make
`alignment` a lazily-computed memoized value (`OnceLock`) behind an accessor so
non-format consumers pay nothing. Deferred until measured.

## Verification strategy

The gate at every phase, in order:

1. `cargo test -p rustledger-parser` (the full suite, ~529 tests) - includes
   `corpus_baseline::parser_output_matches_baseline` and
   `cst_baseline::cst_output_matches_baseline`, which fail on any output drift.
2. The fuzz targets (`fuzz_parse`, `fuzz_booking`) for a fixed corpus run - the
   parser must remain panic-free on malformed input (a real risk when hand-rolling
   green-tree offset math).
3. The compat suite (`scripts/compat-bql-test.py` / the CI compatibility job,
   ~800 files) - end-to-end behavior against `bean-check` / `bean-query`.
4. The Phase-0 criterion bench, before/after, reported in each PR description.

A phase does not merge unless 1-3 are unchanged from main and 4 shows the
expected improvement.

## PR slicing

This is the slicing **if a green-tree rewrite is chosen**. Given the empirical
findings it is no longer the default path; the parse-cache win was shipped
instead (see below).

- ~~Phase 0 bench, Phase 1 single-pass converters~~ — Phase 1 proven neutral; bench
  exists via the in-tree `parser_bench`.
1. `perf(parser): green-tree walker + convert_transaction on green` (Phase 2 pilot)
2. `perf(parser): remaining converters + error passes on green` (Phase 2)
3. (optional) `perf(parser): lazy formatter alignment` (Phase 3)

Each is independently revertible and baseline-gated.

**Shipped instead (recommendation 1):** `perf(report): reuse the on-disk parse
cache` (PR #1314) routes `report` through the parse cache `check` already uses,
recovering the full parse cost on repeated invocations (~124 ms -> ~46 ms on a
10k-txn balance report) with no parser changes.

## Alternatives considered

- **Revert to the direct parser / keep two parse paths.** Rejected: contradicts
  `#1262` / ADR-0003, and a second parser is the maintenance burden the migration
  removed. The lossless CST is required for the formatter and LSP.
- **Give `report` / `query` the disk parse cache `check` uses.** Not a rejected
  alternative - this is recommendation 1 above and was shipped (#1314 for
  `report`, #1315 for `query`). Listed here for completeness: it recovers the
  full parse cost on repeated invocations but not on a cold benchmark run, and
  is orthogonal to the underlying conversion cost.
- **Accept the cost as the price of lossless parsing.** Tenable, but a ~3x parse
  regression on the headline benchmark is worth reclaiming when the levers above
  are output-preserving.

## Open questions

- Does rowan 0.16's public `GreenNodeData` API expose enough to walk children
  with offsets without an unsafe or a vendored helper? (Needs a spike in Phase 2
  pilot; if not, the walker may need a small `cursor`-free helper.)
- ~~Is Phase 1 alone enough...?~~ **Answered (see Empirical findings):** Phase 1
  is performance-neutral and has been dropped.
- If a parse cache is added for `report`/`query`, does any consumer depend on
  `report` re-parsing fresh each run (it should not - `check` already caches)?
  Confirm cache-invalidation parity with `check` before reusing its mechanism.
