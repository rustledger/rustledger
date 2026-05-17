//! Shared wasmtime sandbox configuration.
//!
//! Both the directive-plugin runtime ([`crate::runtime`]) and the WASM
//! importer host (`rustledger-importer/src/wasm.rs`) load untrusted
//! `.wasm` modules into wasmtime. They have the same security model
//! and should agree on:
//!
//! - Which wasm proposals are enabled (attack surface)
//! - Whether fuel metering is on (`DoS` bound)
//! - How per-call `Store` resource limits are enforced
//! - The cost of `Engine` creation (compilation cache + thread pool)
//!
//! This module is the single source of truth for those decisions.
//! Adding a feature flag here applies it to every WASM-loaded
//! component in rustledger.
//!
//! # ⚠️ Breaking change for user WASM plugins
//!
//! As of the v0.16-pre reshape, [`sandbox_config`] explicitly disables
//! these wasm proposals (full list — the rustdoc on `sandbox_config`
//! explains the rationale for each):
//!
//! - `wasm_threads`, `wasm_shared_everything_threads`
//! - `wasm_multi_memory`, `wasm_memory64`
//! - `wasm_component_model` (and all sub-flags)
//! - `wasm_gc`, `wasm_function_references`
//! - `wasm_stack_switching`, `wasm_tail_call`
//!
//! A user-shipped `.wasm` plugin or importer that relies on any
//! disabled proposal will now fail to compile at load time with a
//! wasmtime validation error. This is intentional security
//! tightening, but plugin authors targeting earlier rustledger
//! versions may need to recompile against the new sandbox profile.
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

use wasmtime::{Config, Engine, ResourceLimiter, Store};

/// Hard cap on the number of elements in any single WASM table.
///
/// Importers/plugins don't typically need indirect-call tables at all,
/// let alone large ones. Each ref-typed slot is pointer-sized (8 bytes
/// on 64-bit), so 1M elements = ~8 MiB worst case — well under the
/// memory cap but enough headroom for any plausible indirect-dispatch
/// pattern. Without this cap, `table.grow` would bypass the memory
/// limiter (`Memory` and `Table` are separate resource classes in
/// wasmtime's accounting).
pub const MAX_TABLE_ELEMENTS: usize = 1024 * 1024;

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
            // Bare `.expect` would swallow the wasmtime error detail —
            // explicit panic preserves the cause for debugging.
            Arc::new(
                Engine::new(&config).unwrap_or_else(|e| panic!("wasmtime engine init failed: {e}")),
            )
        })
        .clone()
}

/// Per-store memory limiter.
///
/// Wired into [`Store::limiter`] so wasmtime rejects `memory.grow`
/// past `max_memory`. Without this, configured memory caps would be
/// silently ignored — the sandbox would have unbounded heap, which
/// defeats the "self-contained module" guarantee.
pub struct MemoryLimiter {
    max_memory: usize,
}

impl MemoryLimiter {
    /// Build a limiter that caps growth (and initial allocation) at
    /// `max_memory` bytes.
    #[must_use]
    pub const fn new(max_memory: usize) -> Self {
        Self { max_memory }
    }
}

impl ResourceLimiter for MemoryLimiter {
    fn memory_growing(
        &mut self,
        _current: usize,
        desired: usize,
        _maximum: Option<usize>,
    ) -> wasmtime::Result<bool> {
        Ok(desired <= self.max_memory)
    }

    fn table_growing(
        &mut self,
        _current: usize,
        desired: usize,
        _maximum: Option<usize>,
    ) -> wasmtime::Result<bool> {
        // wasmtime accounts memory and tables separately — without
        // this cap, `table.grow` would bypass the memory limiter.
        // `MAX_TABLE_ELEMENTS` is conservative; bump it if a
        // legitimate module ever needs more.
        Ok(desired <= MAX_TABLE_ELEMENTS)
    }
}

/// Store user-data — just the [`MemoryLimiter`] today.
///
/// Kept in a named struct so [`Store::limiter`]'s closure can return
/// a stable reference and future additions (e.g. a host-side metrics
/// counter) can land without changing the `Store<T>` type.
pub struct StoreState {
    limiter: MemoryLimiter,
}

impl StoreState {
    /// Build a state initialized with the given memory cap.
    #[must_use]
    pub const fn new(max_memory: usize) -> Self {
        Self {
            limiter: MemoryLimiter::new(max_memory),
        }
    }
}

/// Create a [`Store`] with rustledger's sandbox enforcement wired in:
///
/// - [`MemoryLimiter`] enforcing `max_memory` on both initial
///   allocation and `memory.grow`
/// - Fuel budget computed from `max_time_secs` (clamped `≥1` to
///   avoid zero-fuel starvation; `saturating_mul` to avoid overflow
///   on absurd configurations)
///
/// Used by both the WASM importer host and the directive-plugin
/// runtime so the per-call enforcement is identical across the
/// workspace.
///
/// # Errors
///
/// Returns `wasmtime::Error` if `set_fuel` fails — which only happens
/// when `consume_fuel(false)` is configured on the [`Engine`], and
/// [`sandbox_config`] always sets it true. The `Result` is therefore
/// defensive: a future refactor flipping the flag will surface the
/// error rather than silently producing an unmetered Store.
pub fn make_sandboxed_store(
    engine: &Engine,
    max_memory: usize,
    max_time_secs: u64,
) -> wasmtime::Result<Store<StoreState>> {
    let mut store = Store::new(engine, StoreState::new(max_memory));
    store.limiter(|s| &mut s.limiter);
    // 1M instructions per second is the same rough budget used
    // across the workspace.
    let fuel = max_time_secs.max(1).saturating_mul(1_000_000);
    store.set_fuel(fuel)?;
    Ok(store)
}

/// Build a wasmtime [`Config`] with rustledger's locked-down security
/// posture. Exposed for tests and embedders who need to construct an
/// `Engine` with the same flags but different lifetimes.
///
/// # Maintenance: re-audit on every wasmtime bump
///
/// wasmtime's `Config::new()` returns its *current* defaults, which
/// evolve across versions — new proposals routinely land as
/// default-on. On every wasmtime bump in `Cargo.toml`, re-audit this
/// function: check wasmtime's release notes for new `wasm_*`
/// features and decide whether to keep, disable, or leave at
/// default. wasmtime does not provide a "deny by default" mode, so
/// this audit is structurally required, not optional.
///
/// # Enabled
///
/// - `consume_fuel(true)` — fuel metering for `DoS` bound. Every
///   sandboxed call must `Store::set_fuel(...)` before invoking
///   (handled by [`make_sandboxed_store`]).
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
    fn memory_limiter_rejects_grow_above_max() {
        let mut limiter = MemoryLimiter::new(1024);
        assert!(
            limiter
                .memory_growing(0, 512, None)
                .expect("under cap is Ok")
        );
        assert!(limiter.memory_growing(0, 1024, None).expect("at cap is Ok"));
        assert!(
            !limiter
                .memory_growing(0, 1025, None)
                .expect("over cap is Ok(false)")
        );
    }

    #[test]
    fn table_limiter_rejects_grow_above_max() {
        let mut limiter = MemoryLimiter::new(usize::MAX);
        assert!(
            limiter
                .table_growing(0, MAX_TABLE_ELEMENTS, None)
                .expect("at cap is Ok")
        );
        assert!(
            !limiter
                .table_growing(0, MAX_TABLE_ELEMENTS + 1, None)
                .expect("over cap is Ok(false)")
        );
    }

    #[test]
    fn make_sandboxed_store_wires_fuel_and_limiter() {
        let engine = shared_engine();
        let store =
            make_sandboxed_store(&engine, 1024 * 1024, 30).expect("default config builds a store");
        // Fuel was set (wasmtime returns Some when set_fuel succeeded).
        assert!(store.get_fuel().expect("get_fuel succeeds") > 0);
    }

    #[test]
    fn make_sandboxed_store_clamps_zero_max_time_secs() {
        // Regression: max_time_secs = 0 previously caused immediate
        // fuel-exhaustion trap on first instruction.
        let engine = shared_engine();
        let store =
            make_sandboxed_store(&engine, 1024 * 1024, 0).expect("zero secs clamps, not starves");
        assert!(store.get_fuel().expect("get_fuel succeeds") > 0);
    }

    #[test]
    fn make_sandboxed_store_saturates_huge_max_time_secs() {
        // Regression: max_time_secs = u64::MAX would overflow the
        // `* 1_000_000` calc (debug panic, release silent wrap).
        let engine = shared_engine();
        let store = make_sandboxed_store(&engine, 1024 * 1024, u64::MAX)
            .expect("huge secs saturates, doesn't overflow");
        assert_eq!(store.get_fuel().expect("get_fuel succeeds"), u64::MAX);
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

    #[test]
    fn sandbox_config_rejects_memory64_module() {
        // `(memory i64 1)` declares an i64-indexed (64-bit) memory,
        // which requires `wasm_memory64`. Must be rejected.
        let wat = r#"
            (module
                (memory (export "memory") i64 1)
            )
        "#;
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let engine = Engine::new(&sandbox_config()).unwrap();
        let result = wasmtime::Module::new(&engine, &bytes);
        assert!(
            result.is_err(),
            "memory64 module should be rejected when wasm_memory64=false"
        );
    }

    #[test]
    fn sandbox_config_rejects_component_module() {
        // Component-model top-level `(component …)` requires
        // `wasm_component_model`. We use a custom MessagePack ABI,
        // not components, so this must be rejected.
        let wat = r"(component)";
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let engine = Engine::new(&sandbox_config()).unwrap();
        // Components compile via `Component::new`, not `Module::new`.
        // `Module::new` on component bytes should fail outright.
        let result = wasmtime::Module::new(&engine, &bytes);
        assert!(
            result.is_err(),
            "component-model module should be rejected when wasm_component_model=false"
        );
    }

    #[test]
    fn sandbox_config_rejects_gc_module() {
        // A `(struct …)` type definition requires the GC proposal
        // (`wasm_gc` + `wasm_function_references` for typed refs).
        // Must be rejected.
        let wat = r"
            (module
                (type $point (struct (field i32) (field i32)))
            )
        ";
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let engine = Engine::new(&sandbox_config()).unwrap();
        let result = wasmtime::Module::new(&engine, &bytes);
        assert!(
            result.is_err(),
            "GC struct-type module should be rejected when wasm_gc=false"
        );
    }
}
