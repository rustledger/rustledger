# ADR-0006: WIT / Component-Model embedding contract

## Status

Proposed (June 2026). Phase 1 (the typed WIT contract) and Phase 2 (all 20
exports wired; builds as a real `wasm32-wasip2` component; parity harness)
landed in #1384. The JSON-RPC embedding surface (`rustledger-ffi-wasi`,
WASI Preview 1) remains the shipped, supported path during the dual-ship
window; the Component-Model path (`rustledger-ffi-component`, WASI Preview 2)
is not yet a release artifact (`publish = false`). The retire-JSON-RPC step
(Phase 5) is planned, not accepted.

## Context

`rustledger-ffi-wasi` embeds rustledger in any language via a JSON-RPC 2.0 API
over WASI Preview 1 (see `docs/guides/integration.md`, "WASI FFI (JSON-RPC)").
Its wire shape is a set of hand-written DTOs (`crates/rustledger-ffi-wasi/ src/types/`) that mirror the core types by hand, plus consumer stubs generated
from those DTOs (ADR-0004: ts-rs TypeScript, schemars JSON Schema, Pydantic).

ADR-0004 attacks wire-format drift by generating *consumers* from the
hand-mirrored DTOs. It does not remove the DTOs themselves, and it does not
give the **host** side of an embedding any generated, enforced contract — the
host (e.g. rustfava) and the guest agree on the JSON shape by convention and
review. #1399 is a concrete instance of that cost: the cost shape had to be
kept consistent between posting cost and position cost by hand.

The WASI Component Model (Preview 2) offers a different fix: a typed `.wit`
interface is the single source of truth, and binding generators emit typed
Rust on **both** sides (`wit-bindgen` for the guest, `wasmtime::component:: bindgen!` for the host). The shapes that JSON-RPC keeps consistent by review
become compile-time-enforced.

This ADR records the decision to build that contract and the constraints the
translation surfaced.

## Decision

Introduce `crates/rustledger-ffi-component`: a `wasm32-wasip2` component whose
`wit/world.wit` is the single source of truth for the embedding wire shape,
replacing the hand-mirrored DTOs of `rustledger-ffi-wasi` for embedding.

### 1. The WIT contract is the wire shape

`wit/world.wit` (package `rustledger:ledger`) translates the `types/output.rs`
and `types/input.rs` DTOs 1:1 into WIT records/variants and exports four
interfaces (`ledger`, `builder`, `util`, `format`) from the `rustledger`
world — the entire former JSON-RPC method surface. The contract is itself the
versioned wire shape; a `version()` func remains for runtime negotiation,
replacing the per-response `api_version` string (a JSON-RPC-ism).

### 2. The Component Model forbids recursive types — `json(string)` escape hatch

WIT/the Component Model cannot express recursive types (verified: `wasm-tools`
rejects a `query-value` that contains itself, even through a `list`). Two BQL
query cells are self-referential: `object` (a map of cells) and `set` (a list
of cells). These two cases — and only these — are carried in a single,
clearly-named `json(string)` case that serializes the cell as JSON. Every other
`query-value` case is fully typed; `object`/`set` are rare in real query output.
This is the one place WIT cannot fully express the JSON shape, and is the key
finding of Phase 1.

### 3. `meta-value` is a closed, non-recursive variant

The JSON DTO types user metadata as arbitrary `serde_json::Value`, but it is
only ever produced from core `MetaValue` — a finite, non-nesting set
(text / number / boolean / amount / null). So the feared "recursive
meta-value" does not exist on this side; it maps cleanly to a closed WIT
`variant` with no escape hatch needed.

### 4. `cost` is defined once and reused

A single `cost` / `cost-number` shape is used for both posting cost and
position cost. The consistency #1399 had to enforce by hand + review is now
structural — by construction, `cost.number` is the same `cost-number` variant
everywhere.

### 5. Maps become ordered `list<tuple<...>>`

WIT has no map type. `Meta.user`, `display_precision`, and
`inferred_tolerance_default` become key/value lists, which also preserves
source order.

### 6. Dual-ship, then retire JSON-RPC

During the migration both crates coexist. `rustledger-ffi-component` reuses
`rustledger-ffi-wasi`'s loader orchestration (`load_source`) and core→DTO
conversion (`directive_to_json`) and maps those DTOs into WIT types, so there
is one source of conversion logic, not two. The crate is not yet a release
artifact. The plan:

- **Phase 1–2 (#1384, landed):** the contract + all 20 exports wired, builds as
  a wasip2 component, parity harness asserts the component agrees with the
  JSON-RPC path.
- **Phase 3+:** release artifact, broaden parity coverage, wire the
  component build into CI, migrate rustfava to the component.
- **Phase 5:** retire the WASI-p1 JSON-RPC surface. When it is removed, the
  shared loader/conversion logic moves out of `rustledger-ffi-wasi` to a
  neutral home.

## Consequences

### Positive

- **Host and guest share one generated, enforced contract.** The shapes
  JSON-RPC keeps consistent by review (e.g. the #1399 cost footgun) become
  compile-time errors on either side if they drift.
- **Single source of truth for the embedding wire shape** is the `.wit` file,
  removing the hand-mirrored embedding DTOs (for the embedding surface) that
  ADR-0004 could only generate consumers *from*, not eliminate.
- **No per-response `api_version` bookkeeping**; the contract is versioned.
- **Cost / meta-value consistency is structural**, not review-enforced.

### Negative

- **`object`/`set` query cells are not typed** — they ship as a `json(string)`
  escape hatch. Consumers of those rare cells parse JSON, as before.
- **Two embedding crates coexist during the dual-ship window**, with
  `rustledger-ffi-component` depending on `rustledger-ffi-wasi` for shared
  logic. This is temporary coupling, resolved at Phase 5.
- **New toolchain surface:** `wasm32-wasip2` target, `wit-bindgen`, and a
  `wasmtime` component host for the parity harness.
- **Metadata fidelity gap (in progress):** numeric metadata currently surfaces
  as `meta-value::text` because the reused DTO stringifies it; faithful typing
  needs the core `MetaValue`, which `directive_to_json` flattens.

### Neutral

- The WIT contract supersedes the **FFI-WASI/embedding** portion of ADR-0004's
  remit (the "equivalent FFI-WASI types" of ADR-0004 §1 and the embedding
  Python stubs of ADR-0004 Phase 3). ADR-0004 continues to govern the
  `rustledger-wasm` npm/TypeScript surface, which is unaffected.

## Alternatives considered

- **Extend ADR-0004 codegen to the JSON-RPC DTOs (status quo, generate more
  consumers).** Keeps the hand-mirrored DTOs and the JSON-RPC transport;
  generates the host side from the same DTOs. Does not give the host a
  *typed, enforced* contract and keeps the JSON-RPC-isms (`api_version`,
  untyped `serde_json::Value` metadata). The WIT contract removes the DTOs for
  embedding rather than generating more from them.
- **Flatten `object`/`set` cells into typed WIT.** Impossible under the
  recursive-type prohibition without an unbounded-depth encoding; the
  `json(string)` escape hatch is the pragmatic choice for two rare cell kinds.
- **`cargo-component` build.** Not needed — `wasm32-wasip2` emits a component
  directly from a `cdylib`.

## Related

- #1384 — the WASI-p1 → p2 migration (this work).
- #1399 — the cost-shape consistency the typed `cost` now enforces structurally.
- #1401 — typed `rustledger_ops::clamp` used by the `builder` interface.
- #1402 — follow-ups: hoist the plugin pass into the loader, move the
  account-type taxonomy to `rustledger-core`, add an end-to-end `load-file`
  parity test.
- [ADR-0004](0004-ts-types-from-rust-dtos.md) — generating wire-format bindings
  from the hand-mirrored DTOs; this ADR supersedes the FFI-WASI/embedding
  portion of its remit (see Neutral).
- [ADR-0001](0001-crate-organization.md) — crate organization; adds
  `rustledger-ffi-component`.
- `crates/rustledger-ffi-component/wit/world.wit` — the contract.
- `crates/rustledger-ffi-component/README.md` — modeling decisions and status.
- `docs/guides/integration.md` — the Component Model (WIT) integration section.
