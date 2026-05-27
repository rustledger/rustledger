//! Cross-binding wire-format equivalence tests.
//!
//! This crate has no runtime API. It exists to host integration tests
//! in `tests/` that depend on multiple wire-format bindings
//! (`rustledger-ffi-wasi` and `rustledger-wasm`) and assert their
//! `Directive → JSON` outputs agree on shared fixtures.
//!
//! See issue #1200 for the motivation and audit candidates. Each
//! audit finding lands as an additional fixture row in
//! `tests/equivalence.rs` — so any drift between bindings is caught
//! by CI rather than waiting for a user-filed issue.
