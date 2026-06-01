# ADR-0004: Generate wire-format bindings from Rust DTOs

## Status

Accepted — Phase 1, Phase 2, and Phase 3 (May 2026). Spike landed in
#1220; Phase 1 (#1223) shipped the per-DTO ts-rs derives, the
`scripts/regen-bindings.sh` post-process, the generated
`bindings/index.d.ts`, and the CI freshness gate. Phase 2 (#1225)
replaced the inline `typescript_custom_section` DTO block in
`src/lib.rs` with `include_str!("../bindings/index.d.ts")` so the
wasm-bindgen-generated `pkg/*.d.ts` and the importable
`bindings/index.d.ts` are the same types. The inline TS in
`src/lib.rs` shrinks to ~150 lines covering only the wasm-bindgen-
managed runtime classes and standalone function signatures. Phase 3
(#1232) adds `schemars::JsonSchema` derives alongside the ts-rs
derives, emits `bindings/index.schema.json` (draft-2020-12), and pipes
the schema through `datamodel-code-generator` to emit
`bindings/types.py` (Pydantic v2). Closes the hand-maintained Python
stubs and external-integrator-contract gaps that Phase 1/2 left
explicit.

## Context

`crates/rustledger-wasm/` ships **three hand-maintained TypeScript surfaces**:

- `beancount.d.ts` (494 lines)
- `beancount_wasm.d.ts` (398 lines)
- `typescript_custom_section` block inside `src/lib.rs` (wasm-bindgen embeds it in the generated `.d.ts` that ships with the npm package)

Each gets out of sync with the Rust DTOs independently. PRs #1209, #1210, #1211, #1212, #1215, #1216 all had to update all three surfaces in lockstep. PR #1210 was an audit pass that found 7 directive variants entirely missing from one surface and `Posting.price` missing from another.

#1200's audit cascade (8 PRs over ~3 days) closed the wire-format-drift backlog but didn't solve the *structural* problem: any future wire-format field will need three TS updates and a manual audit to confirm all three actually got updated.

This ADR records the design decision for a structural fix.

## Spike

Prototype landed in **PR #1220** via the temporary example
`crates/rustledger-wasm/examples/tsrs_spike.rs`. The four DTOs that
matter for the audit (`MetaValueJson`, `TypedValueJson`, `PostingJson`,
`DirectiveJson`, plus supporting types) were mirrored verbatim into
the spike with `#[derive(TS)]` added. ts-rs wrote per-type `.d.ts`
files under `crates/rustledger-wasm/bindings/bindings/` (the outer
`bindings/` is ts-rs's per-crate output root; the inner one comes
from the `export_to = "bindings/"` attribute on each derive).

The spike was intentionally a snapshot of the production DTOs at the
moment of writing — not a tracked artifact. Phase 1 (PR #1223) added
`#[derive(TS)]` directly to the production DTOs and deleted the
spike example; the spike's job was to inform the design decision,
not stay current.

### What ts-rs got right

1. **Discriminated unions narrow correctly.** `DirectiveJson` emits
   ```ts
   export type DirectiveJson =
     | { "type": "transaction", ..., postings: Array<PostingJson>, ... }
     | { "type": "balance", ..., tolerance: string | null, ... }
     | ...
   ```
   so `switch (d.type) { case "balance": d.tolerance ... }` narrows. Same for `CostNumberJson` with its `kind` discriminator.

2. **Untagged unions render exactly.** `MetaValueJson` becomes `string | boolean | { number: string, currency: string } | null` — identical to what we ship by hand.

3. **Doc comments translate to JSDoc.** Rustdoc on a field shows up as `/** ... */` above the TS field.

4. **Cross-file imports compose cleanly.** Per-type files reference each other via `import type { MetaValueJson } from "./MetaValueJson"`.

5. **`#[ts(optional)]` solves the `Option<T> + skip_serializing_if = "Option::is_none"` mismatch.** Without it, ts-rs emits `field: T | null` (present-but-null); with it, `field?: T` (optional, matching wire absence). One attribute per Option field.

### Where ts-rs falls short

1. **`TypedValueJson` discriminated narrowing is lost.** The Rust DTO is `struct TypedValueJson { value_type: String, value: MetaValueJson }` — a struct with two fields. ts-rs emits the corresponding wide TS:
   ```ts
   export type TypedValueJson = { type: string, value: MetaValueJson };
   ```
   The hand-written shape we ship today (post-#1215) is narrower:
   ```ts
   export type TypedValue =
     | { type: "string"; value: string }
     | { type: "amount"; value: { number: string; currency: string } }
     | ...
   ```
   This is a **structural Rust-side limitation**, not a ts-rs bug. The hand-written TS encodes per-variant payload constraints (`type: "amount"` implies `value` is an `AmountValue`) that the Rust DTO doesn't express. Restructuring the Rust DTO as a serde-tagged enum is awkward because the `null` variant needs `value: ()` (which doesn't serialize cleanly) or a custom `Deserialize` impl.

2. **Per-type file output** doesn't directly produce our two `.d.ts` files (`beancount.d.ts`, `beancount_wasm.d.ts`). Needs a collation step.

3. **Cosmetic differences** — `Array<T>` instead of `T[]`; trailing commas in object types. tsc accepts both; ESLint may complain but it's a one-line `.eslintrc` exception.

## Decision

**Adopt ts-rs with the following design constraints:**

### 1. Per-struct derives on the production DTOs

Add `#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]` to the wire-format DTOs in `crates/rustledger-wasm/src/types.rs` (and equivalent FFI-WASI types if we generate those too). Behind a feature flag so the default build doesn't pull in `ts-rs`. The CI gate runs `cargo test -p rustledger-wasm --features ts-export` and `git diff --exit-code crates/rustledger-wasm/bindings/`.

### 2. Generated files replace `beancount.d.ts` and `beancount_wasm.d.ts`

The two hand-written files are deleted and replaced by:

- **`bindings/index.d.ts`** — concatenation of all per-type files into a single shippable surface, written by a small post-processing script that runs alongside the ts-rs export. Replaces both current `.d.ts` files.
- The npm package exports `bindings/index.d.ts` as the type entry.

This is a **breaking change to the TS API surface** in terms of file layout (consumers importing from `beancount_wasm.d.ts` directly will need to update), but the type *shapes* are identical or narrower than what we ship today.

### 3. Keep the `typescript_custom_section` inline shape — for now

The `typescript_custom_section` block in `src/lib.rs` is what wasm-bindgen embeds in its generated `.d.ts`. We can't drop it without breaking wasm-bindgen's TS integration. **Phase 2** (a follow-up issue) replaces this block with an `include_str!` of the generated `bindings/index.d.ts` so it stays in sync automatically. For Phase 1, we keep it hand-written but the audit burden drops from three surfaces to one (since the other two go away entirely).

### 4. Keep `TypedValueJson` narrowing hand-tuned

For Phase 1, ts-rs outputs the wide `{ type: string, value: MetaValueJson }` for `TypedValueJson`. The post-processing script detects this specific type and replaces it with the narrower discriminated union we ship today. Document the override in the script so future contributors don't lose it during a generator-version bump.

**Phase 2 alternative**: restructure `TypedValueJson` as a tagged Rust enum with a custom `Deserialize` for the `null` variant. This becomes worthwhile if more types need the same narrowing trick; for now, one type doesn't justify the FFI-WASI refactor.

### 5. Python `.pyi` stubs — explicitly out of scope

`crates/rustledger-ffi-wasi/python/compat.py` is a manual wrapper. Auto-generating Python stubs from the same Rust DTOs is interesting but the spike target is JS/TS. File a separate issue if Python stub generation becomes a priority; until then, the Python compat layer stays hand-maintained.

## Consequences

### Positive

- **Single source of truth** for the wire shape. Adding a field to a Rust DTO automatically updates the TS — no audit pass required.
- **CI catches drift** at the `git diff --exit-code` step. The "forgot to regenerate" failure mode becomes a CI failure, not a silent ship.
- **Narrowing is preserved** for the load-bearing cases (`DirectiveJson` discriminated union, `CostNumberJson::kind`, `MetaValueJson` untagged union).
- **`#[ts(optional)]` is a one-attribute fix** for the only widespread mismatch ts-rs introduced.

### Negative

- **`TypedValueJson` needs a hand-tuned override** in the post-processing script. This is documented but adds a small ongoing maintenance burden.
- **Breaking change to the file layout** of `crates/rustledger-wasm/*.d.ts`. The npm package exports change; downstream consumers importing the explicit file paths must update. Mitigation: ship both files as re-exports of `bindings/index.d.ts` for one release cycle, then deprecate.
- **New dep**: `ts-rs` 12.x. Active maintenance, MIT-licensed, no known cargo-deny findings. Worth checking `cargo deny check` before merge.
- **Wasm-bindgen integration unchanged** in Phase 1 — the `typescript_custom_section` is still hand-maintained. Phase 2 closes that gap.

## Alternatives considered

- **`tsify` / `wasm-bindgen-derive`**: tighter wasm-bindgen integration but couples to wasm-bindgen, which means `rustledger-plugin-types` (wasm-bindgen-free) can't participate. ts-rs is generator-agnostic, which keeps the door open for plugin-types generation later.
- **`specta`**: supports multiple target languages (TS, Python, Rust). Heavier dep, less Rust-ecosystem mindshare than ts-rs. Worth revisiting if/when Python stub generation becomes interesting.
- **Status quo with a `.d.ts` audit checklist**: relies on humans never forgetting. The PR #1210 audit was specifically the failure mode of this approach.

## Phase 3 (May 2026) — JSON Schema + Python (#1232)

Phase 1 + 2 closed TypeScript drift but two surfaces remained
hand-maintained:

1. **Python compat layer** — `crates/rustledger-ffi-wasi/python/compat.py`
   was hand-edited. Same class of drift bug ADR-0004 closed for TS was
   still live for Python.
2. **External integrator contract** — no machine-readable wire-format
   schema for non-Rust/non-TS consumers (LLM tool builders, third-party
   SDK authors, the MCP server).

### Decision

Layer two derives on the existing DTOs and pipe the schemars output
into `datamodel-code-generator`:

1. Add `#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]`
   alongside every existing `#[derive(TS)]`. schemars respects the
   serde attributes already on the DTOs (`#[serde(tag = "type")]`,
   `#[serde(rename = ...)]`, `#[serde(skip_serializing_if = ...)]`) so
   the cost is one extra derive per type, no per-field annotation.
2. A new `#[ignore]`-by-default test (`export_index_schema`) walks the
   graph from `ParseResult` and writes `bindings/index.schema.json`
   (draft-2020-12, with all DTOs under `$defs`).
3. `scripts/regen-bindings.sh` (renamed from `regen-ts-bindings.sh`)
   gains two new phases: run the schema export test, then invoke
   `datamodel-codegen --output-model-type pydantic_v2.BaseModel
   --input-file-type jsonschema` to emit `bindings/types.py`. CI's
   `bindings-fresh` job (renamed from `ts-bindings-fresh`) checks all
   three artifacts via `git diff --exit-code`.

### Alternatives ruled out

- **`specta` wholesale migration.** Researched May 2026. Specta is
  still `2.0.0-rc.25` after 14 months, sister crates at `0.0.x`. JSON
  Schema output (`specta-jsonschema`) is **planned but unpublished**;
  Python output is **planned with no crate**. Replacing ts-rs with
  specta-typescript would leave us with the same two missing targets
  plus a beta-stability TS pipeline.
- **`serde-generate` (Diem/Aptos lineage).** Single Rust→Python tool
  with runtime BCS serialization. Hard blocker: doesn't support
  `serde(tag = "...")` tagged enums or `skip_serializing_if`. Our
  `DirectiveJson` is exactly a tagged enum.
- **`pyo3-stub-gen` / `rustantic`.** Both require DTOs to be PyClasses,
  not plain serde-deriving structs. Much bigger commitment than the
  ts-rs ergonomics we have today.
- **`quicktype` TS→Python.** Accepts `.d.ts` as input, but Python
  output has no Pydantic v2 path (open issue glideapps/quicktype#1474).

There is no ts-rs analogue for Python in May 2026 — the hybrid above
is what the ecosystem actually supports.

### Trade-offs

- **`TypedValueJson` narrowing is NOT applied to JSON Schema.** TS
  consumers get the hand-tuned discriminated union (per Phase 1).
  Python consumers get the wide `{type, value}` form. Pydantic v2's
  discriminated-union ergonomics (`Annotated[Union[...],
  Field(discriminator=...)]`) don't map cleanly from a TS literal-union
  override; rather than maintain two narrowings, we ship the wide form
  to Python. JSON Schema consumers can apply their own narrowing if
  needed.
- **One additional derive per DTO.** ~35 lines added, mirroring the
  existing ts-rs derive pattern. schemars respects serde attributes
  natively, so no per-field annotation work was needed.
- **New CI tooling: Python 3.12 + pipx.** Both preinstalled on
  ubuntu-latest. The `datamodel-code-generator` install runs once per
  CI invocation via `pipx run`; no version drift between runs.
- **No specta migration debt accrued.** When specta's Python and JSON
  Schema crates ship and stabilize, the migration consideration
  reopens. For now we're on stable Rust ecosystem tools (ts-rs,
  schemars) plus a stable Python tool (datamodel-code-generator).

## Related

- #1200 — tracking issue this work was split out of (closed).
- #1218 — original design issue (Phase 1 + 2).
- #1232 — Phase 3 design issue (Python + JSON Schema).
- PRs #1209, #1210, #1211, #1212, #1215, #1216 — the audit cascade that motivated this work.
- `crates/rustledger-wasm/examples/tsrs_spike.rs` — the spike code this ADR is based on.
