# rustledger-ffi-wasi

Shared loader/conversion helpers reused by the rustledger WASI **Component
Model** FFI (`rustledger-ffi-component`).

> **The wasip1 JSON-RPC embedding surface was removed in Phase 5
> ([#1419](https://github.com/rustledger/rustledger/issues/1419)).**
> The JSON-RPC 2.0 router, the WASI server binary, the round-trip wire-format
> tests, and the `rustledger-ffi-wasi-*.wasm` release artifact no longer exist.
> The typed **WASI Preview 2 / Component Model** binding,
> [`rustledger-ffi-component`](../rustledger-ffi-component) (a generated WIT
> contract, default in rustfava since Phase 4), is the embedding path — see the
> [Integration Guide](../../docs/guides/integration.md#component-model-wit).

## What this crate is now

A **library only**. After the JSON-RPC surface was removed, what remains is the
shared logic the component reuses:

- `helpers` — loader orchestration (`load_source` / `load_file`: parse + resolve
  includes + book + run plugins → core directives, options, errors), plus
  `apply_plugins` and `expand_pads`.
- `convert` + `types` — the `Directive → JSON` DTO conversion the component
  currently maps to WIT.

## Remaining Phase 5 work

This crate is mid-retirement. The remaining stages of
[#1419](https://github.com/rustledger/rustledger/issues/1419):

1. Switch `rustledger-ffi-component` to convert **core → WIT directly**, dropping
   the DTO layer (this also gives numeric metadata faithful typing).
2. Remove the DTO mirror (`convert` / `types`), then move the surviving loader
   orchestration to its final home — at which point this crate is deleted.
