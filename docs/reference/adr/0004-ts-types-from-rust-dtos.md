# ADR-0004: Generate TypeScript types from Rust DTOs

## Status

Proposed (May 2026) — spike landed in #1218; awaiting decision before implementation.

## Context

`crates/rustledger-wasm/` ships **three hand-maintained TypeScript surfaces**:

- `beancount.d.ts` (494 lines)
- `beancount_wasm.d.ts` (398 lines)
- `typescript_custom_section` block inside `src/lib.rs` (wasm-bindgen embeds it in the generated `.d.ts` that ships with the npm package)

Each gets out of sync with the Rust DTOs independently. PRs #1209, #1210, #1211, #1212, #1215, #1216 all had to update all three surfaces in lockstep. PR #1210 was an audit pass that found 7 directive variants entirely missing from one surface and `Posting.price` missing from another.

#1200's audit cascade (8 PRs over ~3 days) closed the wire-format-drift backlog but didn't solve the *structural* problem: any future wire-format field will need three TS updates and a manual audit to confirm all three actually got updated.

This ADR records the design decision for a structural fix.

## Spike

Prototype landed in PR #1218 via `crates/rustledger-wasm/examples/tsrs_spike.rs`. The four DTOs that matter for the audit (`MetaValueJson`, `TypedValueJson`, `PostingJson`, `DirectiveJson`, plus supporting types) were mirrored verbatim into the spike with `#[derive(TS)]` added. Run with:

```bash
cargo test --example tsrs_spike -p rustledger-wasm --features ts-rs-spike
```

ts-rs writes per-type `.d.ts` files under `crates/rustledger-wasm/bindings/bindings/` (the outer `bindings/` is ts-rs's per-crate output root; the inner one comes from the `export_to = "bindings/"` attribute on each derive).

**The spike is intentionally a snapshot of the production DTOs at the moment of writing.** It does not track future changes to `src/types.rs`. When Phase 1 lands, the production DTOs gain the `#[derive(TS)]` and the spike example is deleted — the spike's job is to inform the design decision, not stay current.

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

## Related

- #1200 — tracking issue this work was split out of (closed).
- #1218 — this design issue.
- PRs #1209, #1210, #1211, #1212, #1215, #1216 — the audit cascade that motivated this work.
- `crates/rustledger-wasm/examples/tsrs_spike.rs` — the spike code this ADR is based on.
