# FFI-WASI → Component Model (WIT) spike

Spike for [#1384](https://github.com/rustledger/rustledger/issues/1384). **Result: it works.** A minimal slice of the embedding surface, defined once in [`wit/world.wit`](wit/world.wit), is built as a **WASI-Preview-2 component** and called from a **wasmtime host** through generated, type-checked bindings — no hand-rolled JSON-RPC. It exercises a `string` *and* a real tagged **variant** (`cost-number`, the exact shape that broke rustfava on v0.16), so the risky part of a real migration — type modeling — is de-risked, not just the plumbing.

```
$ host/.../rustledger-ffi-wit-host guest/.../rustledger_ffi_wit_guest.wasm
component reports api_version = "2.0"
cost kind 0 = CostNumber::PerUnit("100")
cost kind 1 = CostNumber::Total("1500")
cost kind 2 = CostNumber::PerUnitFromTotal(("100", "1500"))
✓ WIT host <-> wasip2 component round-trip works (string + variant)
```

> **Status: a point-in-time artifact, not a maintained crate.** It is *not* part of the workspace and *not* built in CI, so it can bitrot as `wit-bindgen` / `wasmtime` evolve. The committed `Cargo.lock`s pin the exact versions it was proven with (`wit-bindgen` 0.58, `wasmtime` 45). Treat it as evidence for the #1384 decision, to be deleted or promoted once that decision is made.

## What's here

- `wit/world.wit` — the contract: `interface ledger { version: func() -> string; }`.
- `guest/` — implements it as a `cdylib` built for `wasm32-wasip2` (→ a real component; verified by the `\0asm 0d…` component layer byte). Uses the **`wit-bindgen` crate** (macro) — no `cargo-component` CLI needed.
- `host/` — a wasmtime host using `wasmtime::component::bindgen!` over the same WIT. Calls `call_version()` — a generated method, not a JSON string.

## Reproduce

The wasip2 target lives in a dedicated dev shell (it's kept out of the default
toolchain so contributors don't build the wasip2 `rust-std` for nothing):

```bash
nix develop .#spike      # wasm32-wasip2 + wasmtime
# guest → wasip2 component
(cd guest && cargo build --target wasm32-wasip2 --release)
# host → native
(cd host  && cargo build --release)
# run
host/target/release/rustledger-ffi-wit-host \
  guest/target/wasm32-wasip2/release/rustledger_ffi_wit_guest.wasm
```

## Findings (toolchain)

- **`wasm32-wasip2` emits a component directly** — no `cargo-component`. The only build prerequisite is the wasip2 `rust-std` (added to `flake.nix`).
- **`wit-bindgen` is a crate, not a CLI** — `wit_bindgen::generate!` on the guest, `wasmtime::component::bindgen!` on the host, both reading the same `.wit`. The contract is the single source of truth.
- **The host side is already in our tree** — wasmtime 45 (a workspace dep for the plugin/Python-WASI host) has full Component Model support. The reference host is incremental, not net-new.
- Guest component: 64 KB for one method (the std/component machinery dominates at this size; real methods add little).

## Recommendation: **dual-ship**, then migrate rustfava, then deprecate

**Context that decides it:** the *only* known consumer of the wasip1 `rustledger-ffi-wasi-<ver>.wasm` artifact is **rustfava** (`engine.py` downloads it and talks JSON-RPC over wasmtime). rustfava is also the thing that breaks on every release because the JSON wire shape drifts (most recently the v0.16 cost-number change). A typed WIT contract is the structural fix for exactly that class of break — see [#1395](https://github.com/rustledger/rustledger/issues/1395).

So:

1. **Dual-ship.** Keep the wasip1 JSON-RPC module as-is (don't break the current rustfava integration). Add the wasip2 WIT component as a second, parallel release artifact. The spike shows the build/host cost is small and wasmtime is already a dep.
2. **Migrate rustfava** to the component (wasmtime-py has component support), getting generated, type-checked bindings instead of hand-parsing JSON into `Decimal`s. This is what stops the recurring breaks.
3. **Deprecate** the wasip1 JSON-RPC surface once rustfava is on the component, after a deprecation window.

**Effort estimate**

- *Spike (done):* ~half a day — mechanism + one real tagged variant proven.
- *Full WIT:* model the real embedding surface in `.wit` (directives, `amount`, options, errors). The spike proves a flat variant round-trips; the **remaining unknown is the *full* directive graph** — deeply nested records, recursive `meta-value`s, lists of variants — and whether it maps to WIT without awkward flattening. That's the part that could push this past ~1–2 days. The DTOs in `crates/rustledger-ffi-wasi/src/types` are the enumerated shape to translate.
- *Guest impl:* wire the exports to the real loader/query (the logic already exists; this is plumbing) — ~1–2 days.
- *rustfava migration:* swap `engine.py`'s JSON-RPC client for a component client — ~1–2 days, and it deletes hand-written parsing.

Roughly a **week** end to end, dual-shipped so nothing breaks meanwhile.

**Why not "decline":** declining leaves rustfava (and any future embedder) hand-parsing an unversioned JSON wire format that changes between releases — the status quo that just cost a multi-step recovery. **Why not "hard migrate":** a hard cut would break the current rustfava integration on the spot; dual-ship gets the benefit without the break.

**Out of scope (unchanged):** WASI 0.3 / native async buys a synchronous request/response surface nothing; the untrusted WASM plugin sandbox deliberately rejects WASI; the Python-WASI runtime is gated on upstream CPython. (Same as #1384.)
