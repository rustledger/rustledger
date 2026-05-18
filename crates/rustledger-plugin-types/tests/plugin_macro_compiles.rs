//! Compile-only test that `wasm_plugin_main!` expands into valid
//! Rust at the same module scope as a user `fn process(...)` of the
//! same name as the WASM ABI export.
//!
//! Sibling to `guest_macro_compiles.rs` which covers the importer
//! macro. Same rationale: PR #1134 caught a class of macro bugs where
//! the expansion generated `fn process` etc. and collided with the
//! user's fns; this test catches a regression on the directive-plugin
//! side. If the macro ever drops the `__wasm_plugin_*` prefix or the
//! cfg-gated `unsafe(export_name = ...)` wrapper, this crate fails to
//! compile.
//!
//! Only built with `--features guest`.

#![cfg(feature = "guest")]
// `needless_pass_by_value`: the macro requires the user `process` fn
// to coerce to `fn(PluginInput) -> PluginOutput` — a fn pointer with
// `PluginInput` by value. Taking `&PluginInput` would break the
// coercion and the whole point of this test. Disable the lint
// crate-wide rather than per-fn.
#![allow(clippy::needless_pass_by_value)]

use rustledger_plugin_types::{
    DirectiveData, PluginInput, PluginOp, PluginOutput, wasm_plugin_main,
};

mod free_fn {
    use super::*;

    // User's `fn process` at the same module scope as the macro
    // invocation — must NOT collide with the generated export name.
    fn process(input: PluginInput) -> PluginOutput {
        let mut ops = Vec::with_capacity(input.directives.len());
        for (i, wrapper) in input.directives.into_iter().enumerate() {
            if let DirectiveData::Transaction(_) = wrapper.data {
                ops.push(PluginOp::Modify(i, wrapper));
            } else {
                ops.push(PluginOp::Keep(i));
            }
        }
        PluginOutput {
            ops,
            errors: vec![],
        }
    }

    wasm_plugin_main! {
        process: process,
    }
}

mod closure_form {
    use super::*;

    // Non-capturing closure should coerce to fn pointer. The
    // importer macro's `with_closures`/`all_closures` cases verify
    // this for that ABI; mirror it here for completeness.
    wasm_plugin_main! {
        process: |input: PluginInput| PluginOutput::passthrough(input.directives.len()),
    }
}

mod passthrough_form {
    use super::*;

    // A pure-passthrough validator that emits no transformations.
    // This is the simplest possible plugin shape — exercising it
    // ensures the macro doesn't accidentally require user-supplied
    // ops in the output (which would block validator-style plugins).
    fn process(input: PluginInput) -> PluginOutput {
        PluginOutput::passthrough(input.directives.len())
    }

    wasm_plugin_main! {
        process: process,
    }
}

// The mere act of `cargo test` compiling this crate validates the
// three macro invocations above. The fn-pointer coercions below
// pin the exact `extern "C"` signatures — if the macro ever
// regenerates with a different shape (e.g. `*const u8` instead of
// `*mut u8` on alloc), the test fails to compile.
//
// The generated fns are never called at runtime — they'd panic on
// non-wasm32 targets by `pack_output`'s contract.

#[test]
fn free_fn_emits_expected_signatures() {
    let _: extern "C" fn(u32) -> *mut u8 = free_fn::__wasm_plugin_alloc;
    let _: extern "C" fn(u32, u32) -> u64 = free_fn::__wasm_plugin_process;
}

#[test]
fn closure_form_emits_expected_signatures() {
    let _: extern "C" fn(u32) -> *mut u8 = closure_form::__wasm_plugin_alloc;
    let _: extern "C" fn(u32, u32) -> u64 = closure_form::__wasm_plugin_process;
}

#[test]
fn passthrough_form_emits_expected_signatures() {
    let _: extern "C" fn(u32) -> *mut u8 = passthrough_form::__wasm_plugin_alloc;
    let _: extern "C" fn(u32, u32) -> u64 = passthrough_form::__wasm_plugin_process;
}
