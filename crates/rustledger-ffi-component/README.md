# rustledger-ffi-component

Rustledger embedding as a **WASI Preview 2 / Component Model** component,
replacing the hand-rolled JSON-RPC wire shape of `rustledger-ffi-wasi`. Part of
the WASI-p1 → p2 migration ([#1384](https://github.com/rustledger/rustledger/issues/1384)).

`wit/world.wit` is the single source of truth for the wire shape; `src/lib.rs`
implements the `rustledger` world's exports.

**Status: Phase 1 done (the contract); Phase 2 in progress (the guest).** The
crate **builds as a real wasip2 component** today — `version` is wired
end-to-end; the remaining exports are honest `unimplemented!()` stubs being
filled in against the existing loader/query logic, one interface at a time.

```bash
# the wasip2 target lives in the default dev shell (flake.nix)
cargo build -p rustledger-ffi-component --target wasm32-wasip2
wasm-tools print target/wasm32-wasip2/debug/rustledger_ffi_component.wasm | head -1   # => (component …
```

## Status

- `wit/world.wit` **validates** with `wasm-tools component wit` (fully resolves
  and round-trips).
- **`wit-bindgen rust` generates** ~9k lines of typed Rust from it — so the
  contract compiles with the real binding generator, not just the parser.

Reproduce:

```bash
wasm-tools component wit crates/rustledger-ffi-component/wit/world.wit   # validate
wit-bindgen rust crates/rustledger-ffi-component/wit/world.wit --out-dir /tmp/g  # codegen
```

## Scope covered

**Read surface** (`interface ledger`) — `version`, `load`, `validate`, `query`,
and their `-file` variants — translated 1:1 from `types/output.rs`: `amount`,
`cost-number`, `cost`, `meta`/`meta-value`, `posting`, all 12 `directive` cases,
`error`, `plugin`, `source-include`, `ledger-options`, `position`,
`column-info`, `query-value`, and the load/validate/query result records.

**Construction & transformation** (`interface builder`) — `create` /
`create-batch` (from `types/input.rs`: `input-cost` = `cost` + the `merge`
average-cost marker, `input-posting`, 12 `input-directive` cases; both fallible,
batch all-or-nothing per the handler) plus `filter` / `clamp` over a date window
(`entry.filter` / `entry.clamp`). Reuses `amount`, `cost-number`, `meta-value`;
input metadata is user key/values only (source location is assigned on load).

**Batch** (`interface ledger`) — `batch` / `batch-file` (`query.batch`): load
once, run several queries.

**Util** (`interface util`) — `types` / `is-encrypted` / `get-account-type`
(`util.types` / `util.isEncrypted` / `util.getAccountType`).

## Modeling decisions (and what the translation surfaced)

1. **`cost` is defined once and reused for posting cost *and* position cost.**
   The consistency that #1399 had to enforce by hand + review is now structural
   — `cost.number` is one `cost-number` variant everywhere, by construction.

2. **`meta-value` is a closed, non-recursive variant.** The JSON DTO types user
   metadata as arbitrary `serde_json::Value`, but it is only ever produced from
   `MetaValue` — a finite set (text / number / bool / amount / null) with no
   nesting. So the "recursive meta-value" risk flagged in the plan does **not**
   exist on this side; it maps cleanly.

3. **The Component Model forbids recursive types.** Verified: `wasm-tools`
   rejects a `query-value` that contains itself, even through a `list`. The only
   self-referential query cells — BQL `object` (map of cells) and `set` (list of
   cells) — are therefore carried in a single, clearly-named `json(string)`
   escape-hatch case rather than awkwardly flattened. Every other cell is fully
   typed; `object`/`set` are rare in real query output. `metadata` stays typed
   because its values are already flat strings. **This is the one place WIT
   can't fully express the JSON shape** — the key finding of Phase 1.

4. **Per-result `api_version` dropped in favour of a `version()` func.** Under a
   versioned WIT contract the wire shape *is* the version; stamping an
   `api_version` string onto every response is a JSON-RPC-ism. `version()`
   remains for runtime negotiation.

5. **Maps → ordered `list<tuple<...>>`.** WIT has no map type; `Meta.user`,
   `display_precision`, `inferred_tolerance_default` become key/value lists
   (which also preserves source order).

## Phase 1 complete

The **entire** JSON-RPC method surface is now modeled across five interfaces —
`ledger` (load/validate/query/batch + `-file` variants), `builder`
(create/create-batch/filter/clamp), `util` (types/is-encrypted/get-account-type),
`format` (format-source/format-entries), exported by the `rustledger` world. The
query cell shapes were verified against `convert.rs::value_to_json` (`interval`
carries `count` + a proper `interval-unit` enum; `metadata` is a flat string
map). The contract validates with `wasm-tools` and generates ~35k lines via
`wit-bindgen`.

## Phase 2 (in progress)

- [x] Crate scaffold + `wit_bindgen::generate!`; builds as a wasip2 component.
- [x] Toolchain wired: `wasm32-wasip2` target in `flake.nix`, workspace member,
      `wit-bindgen` workspace dep.
- [x] `version` export wired.
- [x] `load` wired — reuses `ffi-wasi`'s `load_source` (loader orchestration) and
      `directive_to_json` (core→DTO), then maps DTO→WIT for all 12 directive
      kinds plus options/errors/plugins/includes (`src/convert.rs`).
- [x] `validate` wired — `load_source` + `ValidationSession` (early/late/finalize).
- [x] `query` wired — runs the executor directly for typed rows and projects
      `rustledger_query::Value` → WIT `query-value`; `object`/`set` cells use the
      `json` escape hatch (WIT can't type them recursively).
- [x] `batch` wired (source-based: `load_source` once, run N queries).
- [x] file variants wired. `load-file` uses a new reusable `helpers::load_file`
      in `ffi-wasi` (Loader + booking + options) — extracted from the
      `handle_load_file` handler, which now calls it too (DRY; all `ffi-wasi`
      tests green). `validate-file`/`query-file`/`batch-file` read the file and
      run the source path, matching the handlers (single file, no includes).
- [x] `builder`: `create` / `create-batch` (WIT input → `input_entry_to_directive`
      → core → WIT) and `filter` (date-range `[begin, end)` over WIT directives).
- [ ] `builder`: `clamp` — **deferred to rustledger/rustledger#1401.** It
      synthesizes directives via the JSON-based `clamp_entries`; wiring it here
      cleanly needs a *typed* `clamp` on core directives in `rustledger-ops`,
      rather than ~250 lines of `DirectiveJson` `Deserialize` + reverse-conversion
      glue to bridge an algorithm that shouldn't be JSON-based.
- [x] `util` (`types` / `is-encrypted` / `get-account-type`) and `format`
      (`format-source` / `-file` / `-entry` / `-entries`) wired. `format-*-entry`
      reuse the builder input conversion + `canonicalize_directives`.
- [ ] Close the metadata fidelity gap: numeric metadata currently surfaces as
      `meta-value::text` because the reused DTO stringifies it — faithful typing
      needs the core `MetaValue` (`directive_to_json` flattens it).
- [x] Parity harness (`rustledger-ffi-component-tests`): instantiates the built
      component in a wasmtime host (typed `bindgen!`, no JSON-RPC) and asserts
      `version`/`load`/`query` agree with the reused `ffi-wasi` path — the first
      thing that *runs* the conversion code. Skips if the wasm isn't built.
- [ ] Broaden parity coverage (all exports; field-level diff) and wire the
      component-build step into CI (#1200 harness).
- [ ] `entry.clamp`; the metadata-fidelity refinement (numeric meta → `text`).

Then Phase 3+ (release artifact, rustfava migration). See #1384 for the full plan.
