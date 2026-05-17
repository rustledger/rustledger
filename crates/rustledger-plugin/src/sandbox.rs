//! Shared wasmtime sandbox configuration.
//!
//! Both the directive-plugin runtime ([`crate::runtime`]) and the WASM
//! importer host (`rustledger-importer/src/wasm.rs`) load untrusted
//! `.wasm` modules into wasmtime. They have the same security model
//! and should agree on:
//!
//! - Which wasm proposals are enabled (attack surface)
//! - Whether fuel metering is on (`DoS` bound)
//! - The cost of `Engine` creation (compilation cache + thread pool)
//!
//! This module is the single source of truth for those decisions.
//! Adding a feature flag here applies it to every WASM-loaded
//! component in rustledger.
//!
//! # Why share the `Engine`?
//!
//! wasmtime's `Engine` owns the JIT compilation cache and the
//! background-compilation thread pool. wasmtime documentation
//! explicitly recommends one `Engine` per process — sharing it
//! across all imported modules lets us amortize that cost. A
//! per-call `Store` still provides isolation; the `Engine` only
//! holds compiled-code state.

use std::sync::{Arc, OnceLock};

use wasmtime::{Config, Engine};

/// Per-process shared wasmtime [`Engine`] with rustledger's security
/// posture. Cheap to clone (`Arc`).
///
/// # Panics
///
/// Panics if wasmtime fails to construct an `Engine` with our config —
/// this is a process-start invariant; if it fires, the binary is
/// fundamentally broken, not a runtime condition worth handling.
#[must_use]
pub fn shared_engine() -> Arc<Engine> {
    static ENGINE: OnceLock<Arc<Engine>> = OnceLock::new();
    ENGINE
        .get_or_init(|| {
            let config = sandbox_config();
            Arc::new(Engine::new(&config).expect("failed to build shared wasmtime engine"))
        })
        .clone()
}

/// Build a wasmtime [`Config`] with rustledger's locked-down security
/// posture. Exposed for tests and embedders who need to construct an
/// `Engine` with the same flags but different lifetimes.
///
/// # Enabled
///
/// - `consume_fuel(true)` — fuel metering for `DoS` bound. Every
///   sandboxed call must `Store::set_fuel(...)` before invoking.
///
/// # Explicitly disabled (security)
///
/// - `wasm_threads` — atomics on shared memory bypass per-call `Store`
///   isolation and enable contention-based `DoS`.
/// - `wasm_shared_everything_threads` — extension of the above.
/// - `wasm_multi_memory` — importers/plugins are designed for exactly
///   one linear memory. Multiple memories would invalidate the single-
///   memory accounting in `ResourceLimiter::memory_growing`.
/// - `wasm_memory64` — our ABIs are u32-addressed. 64-bit memory would
///   silently break offset math.
/// - `wasm_component_model` (and the `_async`/`_threading`/`_gc`/etc.
///   sub-flags) — we use a custom `MessagePack` ABI, not wasmtime
///   components. Disabled to shrink attack surface.
/// - `wasm_gc` / `wasm_function_references` — opt out of the GC and
///   typed-references proposals; not used and add runtime complexity.
/// - `wasm_stack_switching` / `wasm_tail_call` — control-flow features
///   we don't use; disabled to shrink attack surface.
///
/// # Kept enabled (default + we rely on or tolerate)
///
/// - `wasm_simd` — vector instructions; useful for parsing,
///   sandbox-safe.
/// - `wasm_bulk_memory` — `memory.copy`/`memory.fill`; needed by
///   compilers and harmless under our memory cap.
/// - `wasm_reference_types` — `externref`/`funcref`; we cap table
///   growth separately so unbounded ref tables aren't reachable.
/// - `wasm_multi_value` — multi-return functions; sandbox-safe.
#[must_use]
pub fn sandbox_config() -> Config {
    let mut c = Config::new();
    c.consume_fuel(true);

    // Concurrency / shared-state proposals — bypass our per-call
    // `Store` isolation. Off.
    c.wasm_threads(false);
    c.wasm_shared_everything_threads(false);

    // Multi-memory / 64-bit memory — invalidate our single-memory
    // ResourceLimiter accounting and u32-based ABI offset math. Off.
    c.wasm_multi_memory(false);
    c.wasm_memory64(false);

    // Component model — we use a custom MessagePack ABI, not
    // components. Off (shrinks attack surface).
    c.wasm_component_model(false);

    // GC + typed function references — not used; runtime complexity
    // without benefit. Off.
    c.wasm_gc(false);
    c.wasm_function_references(false);

    // Control-flow features we don't use. Off.
    c.wasm_stack_switching(false);
    c.wasm_tail_call(false);

    // Implicitly default-on and we tolerate them:
    //   wasm_simd, wasm_bulk_memory, wasm_reference_types,
    //   wasm_multi_value, wasm_extended_const, wasm_relaxed_simd.

    c
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_engine_is_idempotent() {
        let a = shared_engine();
        let b = shared_engine();
        // Same Arc target (both clones of the OnceLock'd engine).
        assert!(
            Arc::ptr_eq(&a, &b),
            "shared_engine must return the same Arc each call"
        );
    }

    #[test]
    fn sandbox_config_rejects_threads_module() {
        // A module that declares a shared memory (requires
        // `wasm_threads`) must fail to compile under our config.
        let wat = r#"
            (module
                (memory (export "memory") 1 1 shared)
            )
        "#;
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let engine = Engine::new(&sandbox_config()).unwrap();
        let result = wasmtime::Module::new(&engine, &bytes);
        assert!(
            result.is_err(),
            "shared-memory module should be rejected when wasm_threads=false"
        );
    }

    #[test]
    fn sandbox_config_rejects_multi_memory_module() {
        let wat = r#"
            (module
                (memory (export "memory") 1)
                (memory (export "memory2") 1)
            )
        "#;
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let engine = Engine::new(&sandbox_config()).unwrap();
        let result = wasmtime::Module::new(&engine, &bytes);
        assert!(
            result.is_err(),
            "multi-memory module should be rejected when wasm_multi_memory=false"
        );
    }
}
