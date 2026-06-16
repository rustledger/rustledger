//! Parity harness for the WIT / Component-Model surface (#1384).
//!
//! The actual tests live in `tests/parity.rs`, which instantiates the built
//! `rustledger-ffi-component` wasip2 component in a `wasmtime` host and asserts
//! agreement with the `rustledger-ffi-wasi` JSON-RPC path. This empty lib
//! target exists so the crate is a well-formed Cargo package — a `tests/`-only
//! package reports "no targets specified in the manifest" on some toolchains.
