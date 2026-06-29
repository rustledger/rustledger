# rustledger-ffi-wasi

Slimmed **FFI-support helpers** reused by the rustledger WASI **Component
Model** FFI (`rustledger-ffi-component`).

> **Phase 5 ([#1419](https://github.com/rustledger/rustledger/issues/1419)) is
> complete.** Both the wasip1 JSON-RPC embedding surface (JSON-RPC 2.0 router,
> WASI server binary, round-trip wire-format tests, and the
> `rustledger-ffi-wasi-*.wasm` release artifact) **and** the `Directive → JSON`
> output DTO are gone. The typed **WASI Preview 2 / Component Model** binding,
> [`rustledger-ffi-component`](../rustledger-ffi-component) (a generated WIT
> contract, default in rustfava since Phase 4), is the embedding path and now
> converts core directives straight to WIT — see the
> [Integration Guide](../../docs/guides/integration.md#component-model-wit).

## What this crate is now

A **library only** of FFI-support glue the component reuses:

- `helpers` — loader orchestration (`load_source` / `load_file`: parse + resolve
  includes + book + run plugins → core directives, options, errors), plus
  `apply_plugins` and `expand_pads`.
- `input` types + `input_entry_to_directive` — the WIT-input construction path
  (the component maps `builder` WIT input into core directives through this).
- `hash::compute_directive_hash` — core directive → SHA256 hash (DTO-free), used
  by the component to derive the `meta.hash` field while converting core→WIT.

## Crate fate (decided, #1419 item 6)

This crate is **retained, slimmed** — not relocated, not deleted. The survivors
above are FFI glue (an 864-line WIT-input parser plus wire-shaped option/error
structs) that deliberately stay OUT of the core `rustledger-loader` crate. That
is the "retained … document the decision" outcome of #1419 item 6.
