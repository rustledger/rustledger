# rustledger-ffi-component (WIT contract — Phase 1)

The typed **WIT** embedding contract for rustledger, replacing the hand-rolled
JSON-RPC wire shape of `rustledger-ffi-wasi`. Part of the WASI-p1 → p2 /
Component Model migration ([#1384](https://github.com/rustledger/rustledger/issues/1384)).

**This iteration is Phase 1: the contract only.** `wit/world.wit` is the single
source of truth for the wire shape; the production guest crate that implements
these exports (wiring them to the loader/query) is Phase 2. There is no
`Cargo.toml` here yet — this is not a workspace member.

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

**Construction surface** (`interface builder`) — `create` / `create-batch`
(replacing `entry.create` / `entry.createBatch`) — translated from
`types/input.rs`: `input-cost` (= `cost` + the `merge` average-cost marker),
`input-posting`, all 12 `input-directive` cases. Reuses `amount`,
`cost-number`, and `meta-value`; input metadata is user key/values only (no
source location — assigned on load). Both calls are fallible; the batch is
all-or-nothing, matching the handler's `?`-propagation.

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

## Remaining Phase 1 work

- **Ops methods**: `entry.clamp`, `entry.filter`, and the `query.batch` /
  `query.batchFile` result envelope.
- **Util helpers**: `util.getAccountType`, `util.isEncrypted`, `util.types`.
- **Verify a few cell shapes** against `convert.rs::value_to_json` — notably the
  exact `interval` fields and the `metadata` debug-string projection.

## Next (Phase 2+)

Production guest crate (`wit_bindgen::generate!`, exports wired to the real
loader/query), parity tests vs. the JSON-RPC output (extend the #1200 harness),
release artifact, then the rustfava migration. See #1384 for the full plan.
