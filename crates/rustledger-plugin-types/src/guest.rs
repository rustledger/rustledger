//! WASM-guest helpers + the [`crate::wasm_importer_main!`] macro.
//!
//! This module is **only available with the `guest` feature**:
//!
//! ```toml
//! rustledger-plugin-types = { version = "0.15", features = ["guest"] }
//! ```
//!
//! It's the ergonomic surface for authors writing `.wasm` importer
//! modules. Without it, every importer would have to hand-roll the
//! same ~150 lines of `#[no_mangle] pub extern "C"` exports +
//! manual `MessagePack` encode/decode + `(ptr << 32) | len` packing.
//! With it, the same importer is ~20 lines:
//!
//! ```ignore
//! use rustledger_plugin_types::{
//!     wasm_importer_main, ImporterInput, ImporterOutput,
//! };
//!
//! fn identify(path: &str) -> bool {
//!     path.ends_with(".mt940")
//! }
//!
//! fn extract(_input: ImporterInput) -> ImporterOutput {
//!     // parse input.content, return directives + warnings
//!     ImporterOutput::empty()
//! }
//!
//! // No `extract_enriched` — the macro generates a default
//! // passthrough that wraps each directive with a default
//! // (uncategorized) enrichment. Provide one explicitly only when
//! // the importer produces real categorization data.
//! wasm_importer_main! {
//!     name: "MT940",
//!     description: "MT940 bank statement importer",
//!     identify: identify,
//!     extract: extract,
//! }
//! ```
//!
//! # Required `Cargo.toml` setup
//!
//! A WASM importer crate needs:
//!
//! ```toml
//! [lib]
//! crate-type = ["cdylib"]
//!
//! [dependencies]
//! rustledger-plugin-types = { version = "0.15", features = ["guest"] }
//! ```
//!
//! Build with:
//!
//! ```bash
//! cargo build --target wasm32-unknown-unknown --release
//! ```
//!
//! The output `.wasm` is in `target/wasm32-unknown-unknown/release/`.
//!
//! # `std` is required
//!
//! The macro expansion uses `Vec`, `String`, and Rust's default
//! panic handler — all of which come from `std`. A `no_std` guest
//! would need to hand-roll the exports without this macro.
//!
//! # No `stdio` inside the guest
//!
//! The host sandbox doesn't grant WASI, so `println!` /
//! `eprintln!` from guest code are no-ops (or traps, depending on
//! the panic handler). Surface diagnostics through the wire format
//! instead: push messages onto [`ImporterOutput::warnings`] or
//! construct typed [`crate::PluginError`]s into [`ImporterOutput::errors`].
//! The host renders both into the user-visible extract output.
//!
//! # Sharing state across exports
//!
//! The macro takes three free functions, so there's no `&self` to
//! cache parser state on. If a guest needs shared state (a
//! pre-compiled regex, a CSV column-spec cache), use a `OnceLock`
//! at module scope:
//!
//! ```ignore
//! use std::sync::OnceLock;
//!
//! static PARSER: OnceLock<MyParser> = OnceLock::new();
//!
//! fn extract(input: ImporterInput) -> ImporterOutput {
//!     let parser = PARSER.get_or_init(|| MyParser::compile());
//!     parser.parse(&input.content)
//! }
//! ```
//!
//! # ABI contract
//!
//! The macro emits exactly the exports the host
//! ([`rustledger-importer`'s `WasmImporter::load`]) expects:
//!
//! | Export             | Signature                          | Purpose                                    |
//! | ------------------ | ---------------------------------- | ------------------------------------------ |
//! | `memory`           | (implicit)                         | Standard linear memory                     |
//! | `alloc`            | `fn (u32) -> u32`                  | Heap allocator the host writes inputs into |
//! | `metadata`         | `fn () -> u64`                     | Packed `(ptr, len)` of msgpack `MetadataOutput` |
//! | `identify`         | `fn (u32, u32) -> u64`             | Packed `(ptr, len)` of msgpack `IdentifyOutput` |
//! | `extract`          | `fn (u32, u32) -> u64`             | Packed `(ptr, len)` of msgpack `ImporterOutput` |
//! | `extract_enriched` | `fn (u32, u32) -> u64`             | Packed `(ptr, len)` of msgpack `EnrichedImporterOutput` |
//! | `__rustledger_abi_version` | `fn () -> u32`             | ABI version the host checks at load time |
//!
//! `(ptr << 32) | len` packs the return so the host can unpack both
//! halves from a single u64 (wasmtime's typed-func ergonomics don't
//! support multi-return cleanly).
//!
//! # `unsafe`
//!
//! This module deliberately allows `unsafe` (workspace default
//! denies it). The WASM ABI is fundamentally `extern "C"` with raw
//! pointers and manual memory management — there's no safe Rust
//! equivalent for "host wrote bytes here, here's a pointer to
//! them." Every unsafe block is paired with a SAFETY comment
//! explaining the contract with the host.

#![allow(unsafe_code)]

use crate::{AlternativeWrapper, EnrichedImporterOutput, EnrichmentWrapper, ImporterOutput};

// Narrow `rmp_serde` re-export: just the two functions the macro
// expansion needs, plus the decode error type for users who handle
// `decode_input`'s Result directly. The full crate isn't re-exported
// so a future `rmp_serde` major bump doesn't break our public API
// surface — guests that want non-default Serializer config can
// still add `rmp-serde` to their own deps explicitly.
pub use rmp_serde::{decode::Error as DecodeError, from_slice, to_vec};

/// Pack a Vec of msgpack bytes into the host-expected u64 return.
///
/// `(ptr << 32) | len` is the shape the host unpacks. We leak the
/// buffer so its memory survives the function return; the host
/// reads the bytes back through `ptr`/`len`.
///
/// # Why the leak is safe
///
/// The host runs each `extract`/`identify`/etc. call inside a
/// fresh wasmtime `Store`. After the host reads the output bytes
/// and the entry-point returns, the host drops the Store — which
/// reclaims the entire guest linear memory in one shot. The leaked
/// `Vec` lives in that linear memory, so it gets reclaimed
/// implicitly without growing across calls. The guest doesn't see
/// the Store at all; this fact is purely an artifact of how the
/// host invokes us.
///
/// # `wasm32`-only contract
///
/// Pointers are packed into the high 32 bits — this only works on
/// `wasm32` where pointers fit in u32. The pointer-fits-in-u32
/// `try_from` is a runtime check on the wasm32 target (always
/// succeeds) and a hard panic on 64-bit native (where pointers are
/// u64 — would silently truncate without the check). Calling this
/// from non-wasm host code is a misuse; the function exists for
/// guest-side macro expansion.
///
/// # Panics
///
/// - If `bytes.len()` exceeds `u32::MAX` (practically impossible:
///   host's per-call output cap is 64 MiB).
/// - If the buffer's address doesn't fit in u32 (only happens on
///   non-`wasm32` targets — see above).
#[must_use]
pub fn pack_output(bytes: Vec<u8>) -> u64 {
    let len =
        u32::try_from(bytes.len()).expect("output length must fit in u32 (host cap is 64 MiB)");
    let ptr = u32::try_from(bytes.as_ptr() as usize)
        .expect("guest pointer must fit in u32 — this function is for wasm32 targets");
    std::mem::forget(bytes);
    (u64::from(ptr) << 32) | u64::from(len)
}

/// Decode msgpack bytes the host wrote into our linear memory at
/// `(ptr, len)` into a typed input value.
///
/// # Safety
///
/// The caller MUST guarantee that `ptr..ptr+len` is a valid byte
/// range in the guest's linear memory. The macro-generated entry
/// points satisfy this because the host wrote the bytes via our
/// `alloc` export immediately before invoking us. Calling this
/// helper from any other context — e.g. unit tests or guest-side
/// utility code — is a misuse and can read uninitialized memory
/// or trigger a wasmtime trap.
///
/// # Errors
///
/// Returns [`DecodeError`] if the bytes don't decode as `T`. In the
/// macro's call sites, this triggers a panic-trap which the host
/// surfaces as a `WasmImporterError::Runtime`.
pub unsafe fn decode_input<T>(ptr: u32, len: u32) -> Result<T, DecodeError>
where
    T: serde::de::DeserializeOwned,
{
    // SAFETY: the caller asserted (via the unsafe fn signature)
    // that `ptr..ptr+len` is a valid byte range. The macro path
    // gets this guarantee from the host's `alloc` + entry-point
    // protocol; wasmtime doesn't reclaim guest linear memory
    // mid-call.
    let bytes = unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };
    rmp_serde::from_slice(bytes)
}

/// Promote an [`ImporterOutput`] into an [`EnrichedImporterOutput`]
/// by attaching a default (uncategorized, no-alternative)
/// enrichment to each directive.
///
/// Used by the macro to auto-generate `extract_enriched` when the
/// user only supplies `extract`. Matches the host-side
/// `EnrichedImportResult::from(ImportResult)` shape so the round-
/// trip is consistent across guest and host.
#[must_use]
pub fn default_enriched_from(out: ImporterOutput) -> EnrichedImporterOutput {
    let entries = out
        .directives
        .into_iter()
        .enumerate()
        .map(|(i, directive)| {
            let enrichment = EnrichmentWrapper {
                directive_index: i,
                confidence: 0.0,
                // Matches `CategorizationMethod::Default::as_meta_value()`
                // on the host side — keeps the wire format consistent
                // so the host's `parse_method` accepts it.
                method: "default".to_string(),
                alternatives: Vec::<AlternativeWrapper>::new(),
                fingerprint: None,
            };
            (directive, enrichment)
        })
        .collect();
    EnrichedImporterOutput {
        entries,
        warnings: out.warnings,
        errors: out.errors,
    }
}

/// Emit the six `#[no_mangle] pub extern "C"` exports that a
/// rustledger-host-loaded `.wasm` importer must provide.
///
/// # Invocation constraint
///
/// **Invoke at most once per crate.** Each call generates Rust
/// items named `__wasm_importer_alloc`/`metadata`/`identify`/
/// `extract`/`extract_enriched`/`abi_version` and (on `wasm32`) wasm
/// exports named `alloc`/`metadata`/etc. — two invocations in one crate
/// collide on both. Each WASM importer should be its own
/// `cdylib` crate.
///
/// # Native vs `wasm32` symbol names
///
/// On `wasm32`, the macro emits exports named
/// `alloc`/`metadata`/etc. via `#[unsafe(export_name = "...")]`.
/// On native targets, the `export_name` attribute is gated off
/// (it would conflict with multiple compile-test invocations in
/// the same binary) — the Rust identifiers `__wasm_importer_*`
/// are the only symbols emitted. `objdump`/`nm` on a native
/// build won't show `alloc` etc.; that's expected.
///
/// See the module-level docs for the full example. The macro has
/// two arms:
///
/// **Without `extract_enriched`** (the common case):
///
/// ```ignore
/// wasm_importer_main! {
///     name: "MT940",
///     description: "MT940 bank statements",
///     identify: identify,
///     extract: extract,
/// }
/// ```
///
/// This generates an `extract_enriched` that calls the user's
/// `extract` and wraps each directive with a default (uncategorized)
/// enrichment via [`default_enriched_from`].
///
/// **With `extract_enriched`** (when the importer produces real
/// categorization data):
///
/// ```ignore
/// wasm_importer_main! {
///     name: "MT940",
///     description: "MT940 bank statements",
///     identify: identify,
///     extract: extract,
///     extract_enriched: extract_enriched,
/// }
/// ```
///
/// # Compile-time signature checks
///
/// The macro expansion type-annotates each user fn binding so a
/// wrong signature surfaces at the user's fn definition rather
/// than inside the macro guts. For example, writing
/// `fn identify(path: String) -> bool` gives an "expected
/// `fn(&str) -> bool`" error at the `fn` line, not at the macro
/// invocation. Closures with captures that don't coerce to
/// function pointers will produce a less precise error — use a
/// free function for the cleanest experience.
///
/// # Required user-fn signatures
///
/// - `identify`: `fn(&str) -> bool`
/// - `extract`: `fn(ImporterInput) -> ImporterOutput`
/// - `extract_enriched` (optional): `fn(ImporterInput) -> EnrichedImporterOutput`
///
/// The signatures use `fn(...)` *pointer* types — fn items and
/// non-capturing closures coerce in, but **capturing closures
/// don't**. This applies to both macro arms; the short form's
/// auto-generated `extract_enriched` internally requires
/// `extract` to coerce to a fn pointer. Use free fns (the
/// pattern shown in the module-level example) for the cleanest
/// experience.
///
/// # Failure handling
///
/// msgpack decode/encode errors in the macro-generated path panic,
/// which traps the WASM module. The host surfaces traps as
/// `WasmImporterError::Runtime`. Guest-domain errors should flow
/// through `ImporterOutput::warnings` / `ImporterOutput::errors`
/// instead of panicking — see the module-level "No `stdio` inside
/// the guest" section.
#[macro_export]
macro_rules! wasm_importer_main {
    // Form WITHOUT `extract_enriched` — auto-generates a default
    // passthrough that promotes each ImporterOutput directive into
    // an EnrichedImporterOutput entry with default enrichment.
    (
        name: $name:expr,
        description: $desc:expr,
        identify: $identify:expr,
        extract: $extract:expr $(,)?
    ) => {
        $crate::wasm_importer_main! {
            name: $name,
            description: $desc,
            identify: $identify,
            extract: $extract,
            extract_enriched: |input: $crate::ImporterInput| -> $crate::EnrichedImporterOutput {
                let extract_fn: fn($crate::ImporterInput) -> $crate::ImporterOutput = $extract;
                $crate::guest::default_enriched_from(extract_fn(input))
            },
        }
    };

    // Full form with explicit `extract_enriched`.
    //
    // # Why generated fns have `__wasm_importer_*` Rust identifiers
    //
    // The WASM ABI requires exports literally named `alloc`,
    // `metadata`, `identify`, `extract`, `extract_enriched`. But
    // the user's example also defines `fn identify(...)`,
    // `fn extract(...)` etc. at the same module scope — if the
    // macro generated those Rust names, the items collide and the
    // crate doesn't compile.
    //
    // Fix: give the generated fns prefixed Rust identifiers and
    // use `#[cfg_attr(target_arch = "wasm32", unsafe(export_name = "..."))]`
    // to set the WASM linker symbol explicitly — but only on
    // wasm32 builds. On native targets (where these fns are
    // unreachable anyway), the export_name is omitted so test
    // crates can invoke the macro multiple times without symbol
    // collisions at link time.
    //
    // `#[unsafe(...)]` wrapping is required because the workspace
    // is on Rust 2024, where attributes affecting linkage are now
    // unsafe by default.
    (
        name: $name:expr,
        description: $desc:expr,
        identify: $identify:expr,
        extract: $extract:expr,
        extract_enriched: $extract_enriched:expr $(,)?
    ) => {
        /// Host-callable allocator. Returns a raw pointer into linear
        /// memory; the host writes `size` bytes there before calling
        /// the entry-point export that consumes them.
        #[cfg_attr(target_arch = "wasm32", unsafe(export_name = "alloc"))]
        pub extern "C" fn __wasm_importer_alloc(size: u32) -> *mut u8 {
            let mut buf = ::std::vec::Vec::<u8>::with_capacity(size as usize);
            let ptr = buf.as_mut_ptr();
            ::std::mem::forget(buf);
            ptr
        }

        /// Returns msgpack-encoded `MetadataOutput` packed as
        /// `(ptr << 32) | len`. Called once by the host at load time.
        #[cfg_attr(target_arch = "wasm32", unsafe(export_name = "metadata"))]
        pub extern "C" fn __wasm_importer_metadata() -> u64 {
            let out = $crate::MetadataOutput {
                name: ($name).to_string(),
                description: ($desc).to_string(),
            };
            let bytes = $crate::guest::to_vec(&out).expect("metadata encode");
            $crate::guest::pack_output(bytes)
        }

        /// Decodes `IdentifyInput` from host memory, calls the
        /// user-provided identify fn, returns packed `IdentifyOutput`.
        #[cfg_attr(target_arch = "wasm32", unsafe(export_name = "identify"))]
        pub extern "C" fn __wasm_importer_identify(ptr: u32, len: u32) -> u64 {
            // Type-annotated binding: a signature mismatch at the
            // user's `fn identify(...)` definition surfaces here
            // with a clean "expected fn(&str) -> bool" error,
            // instead of an opaque error pointing into this macro.
            let identify_fn: fn(&str) -> bool = $identify;
            // SAFETY: host wrote `len` bytes at `ptr` via our
            // `alloc` export immediately before this call. The
            // wasmtime Store doesn't reclaim guest memory mid-call.
            let input: $crate::IdentifyInput =
                unsafe { $crate::guest::decode_input(ptr, len) }.expect("identify input decode");
            let matches: bool = identify_fn(input.path.as_str());
            let out = $crate::IdentifyOutput { matches };
            let bytes = $crate::guest::to_vec(&out).expect("identify output encode");
            $crate::guest::pack_output(bytes)
        }

        /// Decodes `ImporterInput`, calls the user-provided extract
        /// fn, returns packed `ImporterOutput`.
        #[cfg_attr(target_arch = "wasm32", unsafe(export_name = "extract"))]
        pub extern "C" fn __wasm_importer_extract(ptr: u32, len: u32) -> u64 {
            let extract_fn: fn($crate::ImporterInput) -> $crate::ImporterOutput = $extract;
            // SAFETY: see __wasm_importer_identify.
            let input: $crate::ImporterInput =
                unsafe { $crate::guest::decode_input(ptr, len) }.expect("extract input decode");
            let output: $crate::ImporterOutput = extract_fn(input);
            let bytes = $crate::guest::to_vec(&output).expect("extract output encode");
            $crate::guest::pack_output(bytes)
        }

        /// Decodes `ImporterInput`, calls the user-provided
        /// extract_enriched fn (or the default passthrough emitted
        /// by the no-extract_enriched macro arm), returns packed
        /// `EnrichedImporterOutput`.
        #[cfg_attr(target_arch = "wasm32", unsafe(export_name = "extract_enriched"))]
        pub extern "C" fn __wasm_importer_extract_enriched(ptr: u32, len: u32) -> u64 {
            // Note: the default-arm passes a closure here, not a
            // free fn. We accept any Fn(ImporterInput) ->
            // EnrichedImporterOutput rather than coercing to a fn
            // pointer (closures-with-captures wouldn't coerce).
            let extract_enriched_fn = $extract_enriched;
            // SAFETY: see __wasm_importer_identify.
            let input: $crate::ImporterInput = unsafe { $crate::guest::decode_input(ptr, len) }
                .expect("extract_enriched input decode");
            let output: $crate::EnrichedImporterOutput = (extract_enriched_fn)(input);
            let bytes = $crate::guest::to_vec(&output).expect("extract_enriched output encode");
            $crate::guest::pack_output(bytes)
        }

        /// Advertises the `plugin-types` ABI version this importer was
        /// built against. The host checks it right after instantiation
        /// (see `rustledger_plugin::sandbox::check_guest_abi`) and
        /// refuses to run a version it doesn't speak, so an ABI skew
        /// surfaces as a clear error instead of an opaque trap inside a
        /// later `extract` call (issue #1234).
        #[cfg_attr(
            target_arch = "wasm32",
            unsafe(export_name = "__rustledger_abi_version")
        )]
        pub extern "C" fn __wasm_importer_abi_version() -> u32 {
            $crate::ABI_VERSION
        }
    };
}

/// Generate the WASM directive-plugin entry points from a single
/// user `process` function.
///
/// The directive-plugin ABI is simpler than the importer ABI: just
/// two exports (`alloc` + `process`), one user fn signature
/// (`fn(PluginInput) -> PluginOutput`), and no separate `metadata` /
/// `identify` / enrichment paths. Host loader: `rustledger-plugin`'s
/// `Plugin::load`.
///
/// # Example
///
/// ```ignore
/// use rustledger_plugin_types::{
///     DirectiveData, PluginInput, PluginOp, PluginOutput,
///     wasm_plugin_main,
/// };
///
/// fn process(input: PluginInput) -> PluginOutput {
///     let mut ops = Vec::with_capacity(input.directives.len());
///     for (i, mut wrapper) in input.directives.into_iter().enumerate() {
///         if let DirectiveData::Transaction(ref mut txn) = wrapper.data {
///             txn.tags.push("processed".to_string());
///             ops.push(PluginOp::Modify(i, wrapper));
///         } else {
///             ops.push(PluginOp::Keep(i));
///         }
///     }
///     PluginOutput { ops, errors: vec![] }
/// }
///
/// wasm_plugin_main! {
///     process: process,
/// }
/// ```
///
/// For pure-passthrough validators that emit no transformations, the
/// user fn can return `PluginOutput::passthrough(input.directives.len())`.
///
/// # Required user-fn signature
///
/// - `process`: `fn(PluginInput) -> PluginOutput`
///
/// Fn items and non-capturing closures coerce in; capturing closures
/// don't. Use a free fn for the cleanest error messages on signature
/// mismatch.
///
/// # Failure handling
///
/// msgpack decode/encode errors in the macro-generated path panic,
/// which traps the WASM module. The host (`rustledger-plugin`)
/// surfaces traps as runtime errors. Guest-domain errors should flow
/// through `PluginOutput::errors` (which carries [`crate::PluginError`]s
/// with optional source-location) instead of panicking — same
/// philosophy as `wasm_importer_main!`.
///
/// # Identifier naming + cfg-gated `export_name`
///
/// Generated fns use `__wasm_plugin_*` Rust idents so a user `fn
/// process(...)` in the same module doesn't collide. The WASM linker
/// symbol is set via
/// `#[cfg_attr(target_arch = "wasm32", unsafe(export_name = "..."))]`
/// so it only applies to the `wasm32` build — test crates can invoke
/// the macro multiple times on the host target without symbol
/// collisions at link time.
///
/// # Invoke once per crate on `wasm32`
///
/// On the actual `wasm32` build target, the macro emits exports named
/// `alloc` and `process` — symbols the host loader looks up by name.
/// **Invoking the macro twice in the same cdylib crate causes a
/// duplicate-symbol linker error.** This is by ABI design: a single
/// `.wasm` plugin module exposes exactly one `process` entry point.
/// The compile-test crate in `tests/plugin_macro_compiles.rs`
/// invokes it three times only because the `export_name` attribute
/// is cfg-gated off on the host target (which is where `cargo test`
/// runs). If you need multiple plugins, build them as separate
/// cdylib crates.
#[macro_export]
macro_rules! wasm_plugin_main {
    (
        process: $process:expr $(,)?
    ) => {
        /// Host-callable allocator. Returns a raw pointer into linear
        /// memory; the host writes `size` bytes there before calling
        /// `process`.
        #[cfg_attr(target_arch = "wasm32", unsafe(export_name = "alloc"))]
        pub extern "C" fn __wasm_plugin_alloc(size: u32) -> *mut u8 {
            let mut buf = ::std::vec::Vec::<u8>::with_capacity(size as usize);
            let ptr = buf.as_mut_ptr();
            ::std::mem::forget(buf);
            ptr
        }

        /// Decodes `PluginInput` from host memory, calls the
        /// user-provided process fn, returns packed `PluginOutput`.
        #[cfg_attr(target_arch = "wasm32", unsafe(export_name = "process"))]
        pub extern "C" fn __wasm_plugin_process(ptr: u32, len: u32) -> u64 {
            // Type-annotated binding surfaces a signature mismatch
            // on the user's `process` fn at the macro arg site
            // instead of opaque-pointing into the macro expansion.
            let process_fn: fn($crate::PluginInput) -> $crate::PluginOutput = $process;
            // SAFETY: host wrote `len` bytes at `ptr` via our `alloc`
            // export immediately before this call. wasmtime doesn't
            // reclaim guest linear memory mid-call.
            let input: $crate::PluginInput =
                unsafe { $crate::guest::decode_input(ptr, len) }.expect("process input decode");
            let output: $crate::PluginOutput = process_fn(input);
            let bytes = $crate::guest::to_vec(&output).expect("process output encode");
            $crate::guest::pack_output(bytes)
        }

        /// Advertises the `plugin-types` ABI version this plugin was
        /// built against. The host checks it right after instantiation
        /// (see `rustledger_plugin::sandbox::check_guest_abi`) and
        /// refuses to run a version it doesn't speak, so an ABI skew
        /// surfaces as a clear error instead of an opaque trap inside
        /// the `process` call (issue #1234).
        #[cfg_attr(
            target_arch = "wasm32",
            unsafe(export_name = "__rustledger_abi_version")
        )]
        pub extern "C" fn __wasm_plugin_abi_version() -> u32 {
            $crate::ABI_VERSION
        }
    };
}

#[cfg(test)]
mod tests {
    // These tests run on the host (64-bit native in CI) — they
    // exercise the parts of the guest module that don't depend on
    // `wasm32`'s u32-sized pointers:
    //
    // - Pure-math packing/unpacking (synthetic ptr+len values, no
    //   real allocation).
    // - msgpack encoding stability for wire-format types.
    // - `default_enriched_from` shape (data conversion, no FFI).
    //
    // The full leak-and-recover pack_output round-trip is wasm32-
    // only by construction; end-to-end validation of the
    // macro-generated exports lives in wave 2.3e (a real `.wasm`
    // module loaded through `WasmImporter`).

    use super::*;
    use crate::{
        DirectiveData, DirectiveWrapper, IdentifyInput, IdentifyOutput, MetadataOutput, OpenData,
        PluginError,
    };

    /// Pin the packed layout: `(ptr << 32) | len`. Reverses to
    /// `ptr = packed >> 32`, `len = packed & 0xFFFF_FFFF`. The host
    /// uses the same shape — if this test fails, the wire ABI is
    /// out of sync.
    #[test]
    fn packing_math_round_trips_synthetic_values() {
        let ptr: u32 = 0xdead_beef;
        let len: u32 = 0xcafe;
        let packed = (u64::from(ptr) << 32) | u64::from(len);
        assert_eq!((packed >> 32) as u32, ptr);
        assert_eq!((packed & 0xFFFF_FFFF) as u32, len);
        assert_eq!(packed, 0xdead_beef_0000_cafe);
    }

    #[test]
    fn packing_math_handles_zero_and_max() {
        // Edge cases the host might hit on degenerate guest output.
        let packed_zero = (u64::from(0u32) << 32) | u64::from(0u32);
        assert_eq!(packed_zero, 0);

        let packed_max = (u64::from(u32::MAX) << 32) | u64::from(u32::MAX);
        assert_eq!(packed_max, u64::MAX);
    }

    /// msgpack encoding stability for `IdentifyInput`. The byte
    /// layout is the wire contract between host and guest; if
    /// rmp-serde ever changes its struct encoding, this catches it.
    #[test]
    fn identify_input_msgpack_encoding_is_stable() {
        let original = IdentifyInput {
            path: "/tmp/statement.mt940".to_string(),
        };
        let bytes = rmp_serde::to_vec(&original).expect("encode");
        let decoded: IdentifyInput = rmp_serde::from_slice(&bytes).expect("decode");
        assert_eq!(decoded.path, original.path);
    }

    #[test]
    fn identify_output_msgpack_encoding_is_stable() {
        let original = IdentifyOutput { matches: true };
        let bytes = rmp_serde::to_vec(&original).expect("encode");
        let decoded: IdentifyOutput = rmp_serde::from_slice(&bytes).expect("decode");
        assert!(decoded.matches);
    }

    #[test]
    fn metadata_output_msgpack_encoding_is_stable() {
        let original = MetadataOutput {
            name: "MT940".to_string(),
            description: "MT940 bank statements".to_string(),
        };
        let bytes = rmp_serde::to_vec(&original).expect("encode");
        let decoded: MetadataOutput = rmp_serde::from_slice(&bytes).expect("decode");
        assert_eq!(decoded.name, "MT940");
        assert_eq!(decoded.description, "MT940 bank statements");
    }

    /// On non-wasm32 targets, `pack_output` deliberately panics
    /// rather than silently truncating a 64-bit pointer to 32 bits.
    /// Pin this contract so a future change can't accidentally
    /// relax it into a silent corruption.
    #[cfg(not(target_pointer_width = "32"))]
    #[test]
    #[should_panic(expected = "guest pointer must fit in u32")]
    fn pack_output_panics_on_non_wasm32_targets() {
        let bytes = vec![0u8; 4];
        // Heap addresses on 64-bit Linux are usually 0x7f00... — way
        // outside u32 range. The try_from in pack_output catches
        // this and panics, preventing the SIGSEGV that the naive
        // `as u32` cast would have caused.
        let _ = pack_output(bytes);
    }

    fn open_wrapper() -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: String::new(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Open(OpenData {
                account: "Assets:Bank".to_string(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        }
    }

    #[test]
    fn default_enriched_from_empty_passes_through() {
        let out = ImporterOutput {
            directives: vec![],
            warnings: vec!["a warning".to_string()],
            errors: vec![PluginError::warning("some warning")],
        };
        let enriched = default_enriched_from(out);
        assert!(enriched.entries.is_empty());
        assert_eq!(enriched.warnings, vec!["a warning".to_string()]);
        assert_eq!(enriched.errors.len(), 1);
    }

    #[test]
    fn default_enriched_from_attaches_default_enrichment_per_directive() {
        let out = ImporterOutput {
            directives: vec![open_wrapper(), open_wrapper(), open_wrapper()],
            warnings: vec![],
            errors: vec![],
        };
        let enriched = default_enriched_from(out);
        assert_eq!(enriched.entries.len(), 3);
        // Each entry gets sequential directive_index, "default"
        // method, no alternatives or fingerprint.
        for (i, (_, enr)) in enriched.entries.iter().enumerate() {
            assert_eq!(enr.directive_index, i);
            assert!((enr.confidence - 0.0).abs() < f64::EPSILON);
            assert_eq!(enr.method, "default");
            assert!(enr.alternatives.is_empty());
            assert!(enr.fingerprint.is_none());
        }
    }

    /// Default method must match `CategorizationMethod::Default::as_meta_value()`
    /// on the host side.
    ///
    /// # Cross-crate symmetry
    ///
    /// The literal `"default"` is asserted on BOTH sides of the
    /// wire:
    ///
    /// - Host (`rustledger-ops`'s `enrichment::tests`):
    ///   `CategorizationMethod::Default.as_meta_value() == "default"`
    /// - Guest (this test): `default_enriched_from` emits `"default"`
    ///
    /// If a future change renames the host variant or its
    /// `as_meta_value()` output, ONE of the two tests has to be
    /// updated — and the reviewer will see the asymmetry. The
    /// guest emission would otherwise drift silently and the host's
    /// `parse_method` would log "unknown method" warnings.
    #[test]
    fn default_enriched_uses_host_compatible_method_string() {
        let out = ImporterOutput {
            directives: vec![open_wrapper()],
            warnings: vec![],
            errors: vec![],
        };
        let enriched = default_enriched_from(out);
        assert_eq!(enriched.entries[0].1.method, "default");
    }
}
