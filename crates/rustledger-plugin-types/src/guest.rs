//! WASM-guest helpers + the [`wasm_importer_main!`] macro.
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
//!     wasm_importer_main, EnrichedImporterOutput, ImporterInput,
//!     ImporterOutput,
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
//! fn extract_enriched(input: ImporterInput) -> EnrichedImporterOutput {
//!     // optional: produce enrichments inline, or wrap extract output
//!     let _ = extract(input);
//!     EnrichedImporterOutput {
//!         entries: vec![],
//!         warnings: vec![],
//!         errors: vec![],
//!     }
//! }
//!
//! wasm_importer_main! {
//!     name: "MT940",
//!     description: "MT940 bank statement importer",
//!     identify: identify,
//!     extract: extract,
//!     extract_enriched: extract_enriched,
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

// The macro uses helpers from this module, which uses rmp_serde
// internally. Re-export rmp_serde so the guest crate doesn't need to
// add its own dep — `features = ["guest"]` is enough.
pub use rmp_serde;

/// Pack a Vec of msgpack bytes into the host-expected u64 return.
///
/// `(ptr << 32) | len` is the shape the host unpacks. We leak the
/// buffer so its memory survives the function return; the host
/// reads the bytes back through `ptr`/`len`.
///
/// The leak is intentional: the buffer must outlive this WASM call
/// so the host can read it. wasmtime's per-call `Store` is dropped
/// after the extract call, which frees the entire linear memory at
/// once — so we don't actually leak anything beyond a single call.
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
/// The host writes input bytes into our linear memory via the
/// `alloc` export then passes the offset + length. Reading those
/// bytes back is safe under that contract — but only the host
/// should call into the macro-generated exports that route here.
/// Direct calls from guest code are a misuse.
///
/// # Errors
///
/// Returns [`rmp_serde::decode::Error`] if the bytes don't decode
/// as `T`. In the macro's call sites, this triggers a panic-trap
/// which the host surfaces as a `WasmImporterError::Runtime`.
pub fn decode_input<T>(ptr: u32, len: u32) -> Result<T, rmp_serde::decode::Error>
where
    T: serde::de::DeserializeOwned,
{
    // SAFETY: the host wrote `len` bytes at `ptr` via our `alloc`
    // export immediately before invoking the entry point that
    // forwards here. The memory is valid for the duration of this
    // call (wasmtime doesn't reclaim guest linear memory mid-call).
    let bytes = unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };
    rmp_serde::from_slice(bytes)
}

/// Emit the five `#[no_mangle] pub extern "C"` exports that a
/// rustledger-host-loaded `.wasm` importer must provide.
///
/// See the module-level docs for the full example. The macro takes
/// four required fields:
///
/// - `name:` — string constant for `MetadataOutput::name`
/// - `description:` — string constant for `MetadataOutput::description`
/// - `identify:` — `fn(&str) -> bool` (path-by-extension check, etc.)
/// - `extract:` — `fn(ImporterInput) -> ImporterOutput`
/// - `extract_enriched:` — `fn(ImporterInput) -> EnrichedImporterOutput`
///
/// The expansion generates `alloc`, `metadata`, `identify`, `extract`,
/// and `extract_enriched` exports. The required `memory` export is
/// implicit — every Rust `wasm32-unknown-unknown` binary exports its
/// linear memory by default.
///
/// Failures in the macro-generated path (msgpack decode/encode
/// errors) panic, which traps the WASM module. The host surfaces
/// traps as `WasmImporterError::Runtime`.
#[macro_export]
macro_rules! wasm_importer_main {
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
        #[no_mangle]
        pub extern "C" fn alloc(size: u32) -> *mut u8 {
            let mut buf = ::std::vec::Vec::<u8>::with_capacity(size as usize);
            let ptr = buf.as_mut_ptr();
            ::std::mem::forget(buf);
            ptr
        }

        /// Returns msgpack-encoded `MetadataOutput` packed as
        /// `(ptr << 32) | len`. Called once by the host at load time.
        #[no_mangle]
        pub extern "C" fn metadata() -> u64 {
            let out = $crate::MetadataOutput {
                name: ($name).to_string(),
                description: ($desc).to_string(),
            };
            let bytes = $crate::guest::rmp_serde::to_vec(&out).expect("metadata encode");
            $crate::guest::pack_output(bytes)
        }

        /// Decodes `IdentifyInput` from host memory, calls the
        /// user-provided identify fn, returns packed
        /// `IdentifyOutput`.
        #[no_mangle]
        pub extern "C" fn identify(ptr: u32, len: u32) -> u64 {
            let input: $crate::IdentifyInput =
                $crate::guest::decode_input(ptr, len).expect("identify input decode");
            let matches: bool = ($identify)(input.path.as_str());
            let out = $crate::IdentifyOutput { matches };
            let bytes = $crate::guest::rmp_serde::to_vec(&out).expect("identify output encode");
            $crate::guest::pack_output(bytes)
        }

        /// Decodes `ImporterInput`, calls the user-provided extract
        /// fn, returns packed `ImporterOutput`.
        #[no_mangle]
        pub extern "C" fn extract(ptr: u32, len: u32) -> u64 {
            let input: $crate::ImporterInput =
                $crate::guest::decode_input(ptr, len).expect("extract input decode");
            let output: $crate::ImporterOutput = ($extract)(input);
            let bytes = $crate::guest::rmp_serde::to_vec(&output).expect("extract output encode");
            $crate::guest::pack_output(bytes)
        }

        /// Decodes `ImporterInput`, calls the user-provided
        /// extract_enriched fn, returns packed
        /// `EnrichedImporterOutput`.
        #[no_mangle]
        pub extern "C" fn extract_enriched(ptr: u32, len: u32) -> u64 {
            let input: $crate::ImporterInput =
                $crate::guest::decode_input(ptr, len).expect("extract_enriched input decode");
            let output: $crate::EnrichedImporterOutput = ($extract_enriched)(input);
            let bytes =
                $crate::guest::rmp_serde::to_vec(&output).expect("extract_enriched output encode");
            $crate::guest::pack_output(bytes)
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
    // - `decode_input` on bytes we own here, so the addresses fit
    //   in `usize` and `as u32` is lossless on a stack-local Vec
    //   (Rust's heap on Linux x86_64 typically returns addresses
    //   that exceed u32, so this only works for buffers happening
    //   to land in low memory — which is unreliable. So we test
    //   decode via `from_slice` directly instead).
    //
    // The full leak-and-recover pack_output round-trip is wasm32-
    // only by construction; end-to-end validation lives in wave
    // 2.3e (a real `.wasm` module loaded through `WasmImporter`).

    use super::*;
    use crate::{IdentifyInput, IdentifyOutput, MetadataOutput};

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

    /// `decode_input` is testable on native because we can construct
    /// a Vec, encode into it, and pass its address as `u32` — but
    /// only safe for buffers small enough that the address truncates
    /// without underflowing into another allocation. We sidestep the
    /// truncation by skipping `decode_input` and calling
    /// `rmp_serde::from_slice` directly to verify the type encoding;
    /// the unsafe pointer-cast layer is exercised in wave 2.3e via
    /// real WASM modules.
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
}
