//! Test fixtures for downstream crates that exercise the WASM
//! importer ABI without checking compiled `.wasm` binaries into the
//! repo.
//!
//! Tests in both this crate and `rustledger` (the CLI) need tiny WASM
//! modules that satisfy the importer ABI: `memory`, `alloc`,
//! `metadata`, `identify`, `extract`, `extract_enriched`, plus the
//! `__rustledger_abi_version` handshake export the host now checks at
//! load (issue #1234). Both previously hand-rolled identical WAT
//! strings; this module is the single source of truth so an ABI change
//! updates one place.
//!
//! Marked `#[doc(hidden)]` so the helpers don't show up in published
//! docs — they're a crate-internal convenience for tests, not a
//! stable public API.

#![doc(hidden)]

/// Minimal `.wat` source for a passive WASM importer:
///
/// - `metadata()` returns `MetadataOutput { name: "<name>", description: "tst" }`
///   from pre-baked bytes at memory offset 0.
/// - `identify()` returns `IdentifyOutput { matches: false }` —
///   always says "no, this isn't my file." Use [`identifying_wat`]
///   instead when the test needs WASM to win `identify()`.
/// - `extract` / `extract_enriched` return `(ptr=0, len=0)` which
///   deserializes-fails on the host — fine for tests that exercise
///   load + dispatch but not actual extract output.
///
/// # Panics
///
/// `name` must be exactly 3 ASCII chars (the msgpack fixstr-3
/// prefix `0xa3` is hardcoded). Asserts on violation so a test using
/// a longer name fails fast rather than producing malformed wire bytes.
#[must_use]
pub fn metadata_wat(name: &str) -> String {
    assert_eq!(name.len(), 3, "test fixture only supports 3-char names");
    // Interpolate the host ABI version so the fixture tracks
    // `rustledger_plugin_types::ABI_VERSION` automatically when it's
    // bumped (issue #1234).
    let abi = rustledger_plugin_types::ABI_VERSION;
    format!(
        r#"
        (module
            (memory (export "memory") 1)
            ;; 0x92 fixarray-2, 0xa3 fixstr-3 "<name>", 0xa3 fixstr-3 "tst"
            (data (i32.const 0) "\92\a3{name}\a3tst")
            (global $bump (mut i32) (i32.const 1024))
            (func (export "alloc") (param i32) (result i32) global.get $bump)
            (func (export "metadata") (result i64) i64.const 9)
            (func (export "identify") (param i32 i32) (result i64) i64.const 0)
            (func (export "extract") (param i32 i32) (result i64) i64.const 0)
            (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
            (func (export "__rustledger_abi_version") (result i32) i32.const {abi})
        )
        "#
    )
}

/// Variant of [`metadata_wat`] where `identify()` returns true.
///
/// `IdentifyOutput { matches: true }` for every file. Use this to
/// test precedence ("does WASM win over a builtin for the same
/// file?") — the always-false `identify` in [`metadata_wat`] can't
/// exercise the collision path.
///
/// # Panics
///
/// Same 3-char `name` constraint as [`metadata_wat`].
#[must_use]
pub fn identifying_wat(name: &str) -> String {
    assert_eq!(name.len(), 3, "test fixture only supports 3-char names");
    // Interpolate the host ABI version (see `metadata_wat`).
    let abi = rustledger_plugin_types::ABI_VERSION;
    format!(
        r#"
        (module
            (memory (export "memory") 1)
            ;; Metadata at offset 0 (9 bytes): fixarray-2 + name + "tst"
            (data (i32.const 0) "\92\a3{name}\a3tst")
            ;; IdentifyOutput true at offset 16 (2 bytes): fixarray-1 + true
            (data (i32.const 16) "\91\c3")
            (global $bump (mut i32) (i32.const 1024))
            (func (export "alloc") (param i32) (result i32) global.get $bump)
            (func (export "metadata") (result i64) i64.const 9)
            ;; identify: ptr=16, len=2 — packed (16 << 32) | 2
            (func (export "identify") (param i32 i32) (result i64) i64.const 0x10_0000_0002)
            (func (export "extract") (param i32 i32) (result i64) i64.const 0)
            (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
            (func (export "__rustledger_abi_version") (result i32) i32.const {abi})
        )
        "#
    )
}
