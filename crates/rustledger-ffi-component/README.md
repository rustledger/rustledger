# rustledger-ffi-component

Rustledger embedding as a **WASI Preview 2 / Component Model** component,
replacing the hand-rolled JSON-RPC wire shape of `rustledger-ffi-wasi`. Part of
the WASI-p1 → p2 migration ([#1384](https://github.com/rustledger/rustledger/issues/1384)).

`wit/world.wit` is the single source of truth for the wire shape; `src/lib.rs`

- `src/convert.rs` implement the `rustledger` world's exports.

## Status

- **Workspace member**, but not yet a published release artifact (`publish = false`).
- **All 20 exports are implemented and build as a real wasip2 component**, across
  four interfaces: `ledger` (load / validate / query / batch + their `-file`
  variants), `builder` (create / create-batch / filter / clamp), `util` (types /
  is-encrypted / get-account-type), `format` (source / file / entry / entries).
- Exports reuse `rustledger-ffi-wasi`'s loader/query/ops logic via shared
  helpers; the DTO↔WIT conversion lives in `src/convert.rs`.
- **Parity-tested** by `rustledger-ffi-component-tests`: it instantiates the
  built component in a wasmtime host (typed `bindgen!`, no JSON-RPC) and asserts
  agreement with the reused `rustledger-ffi-wasi` path.
- **Not yet wired to a consumer** — rustfava still uses the JSON-RPC surface.
  Both coexist during the dual-ship window; the JSON-RPC surface is retired in
  Phase 5.

```bash
# the wasip2 target lives in the default dev shell (flake.nix)
cargo build -p rustledger-ffi-component --target wasm32-wasip2
wasm-tools print target/wasm32-wasip2/debug/rustledger_ffi_component.wasm | head -1   # => (component …

# validate / regenerate the contract directly
wasm-tools component wit crates/rustledger-ffi-component/wit/world.wit
wit-bindgen rust crates/rustledger-ffi-component/wit/world.wit --out-dir /tmp/g
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

**Format** (`interface format`) — `format-source` / `-file` / `-entry` /
`-entries`; the entry variants reuse the builder input conversion +
`canonicalize_directives`.

## Modeling decisions (and what the translation surfaced)

1. **`cost` is defined once and reused for posting cost *and* position cost.**
   The consistency that #1399 had to enforce by hand + review is now structural
   — `cost.number` is one `cost-number` variant everywhere, by construction.

1. **`meta-value` is a closed, non-recursive variant.** The JSON DTO types user
   metadata as arbitrary `serde_json::Value`, but it is only ever produced from
   `MetaValue` — a finite set (text / number / bool / amount / null) with no
   nesting. So the "recursive meta-value" risk flagged in the plan does **not**
   exist on this side; it maps cleanly.

1. **The Component Model forbids recursive types.** Verified: `wasm-tools`
   rejects a `query-value` that contains itself, even through a `list`. The only
   self-referential query cells — BQL `object` (map of cells) and `set` (list of
   cells) — are therefore carried in a single, clearly-named `json(string)`
   escape-hatch case rather than awkwardly flattened. Every other cell is fully
   typed; `object`/`set` are rare in real query output. `metadata` stays typed
   because its values are already flat strings. **This is the one place WIT
   can't fully express the JSON shape** — the key finding of Phase 1.

1. **Per-result `api_version` dropped in favor of a `version()` func.** Under a
   versioned WIT contract the wire shape *is* the version; stamping an
   `api_version` string onto every response is a JSON-RPC-ism. `version()`
   remains for runtime negotiation.

1. **Maps → ordered `list<tuple<...>>`.** WIT has no map type; `Meta.user`,
   `display_precision`, `inferred_tolerance_default` become key/value lists
   (which also preserves source order).

## Known gaps / remaining work

- **Metadata fidelity:** numeric metadata currently surfaces as
  `meta-value::text` because the reused DTO stringifies it — faithful typing
  needs the core `MetaValue` (`directive_to_json` flattens it).
- **Broaden parity coverage** (all exports; field-level diff) and wire the
  component-build step + an end-to-end `load-file` parity test into CI ([#1402](https://github.com/rustledger/rustledger/issues/1402)).
- **Phase 3+:** release artifact, then rustfava migration; **Phase 5** retires
  the JSON-RPC surface and moves the shared loader/conversion logic to a neutral
  home. See [#1384](https://github.com/rustledger/rustledger/issues/1384) for the
  full plan.
