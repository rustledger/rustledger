//! Stub WASM directive plugin for the host's end-to-end integration test.
//!
//! This is the smallest possible plugin that exercises the
//! `wasm_plugin_main!` macro's exports on a real wasm32 target:
//!
//! - `process` reads `PluginInput`, tags every transaction it sees
//!   with `"stub-processed"`, keeps non-transactions unchanged.
//! - The host's e2e test (`tests/wasm_plugin_e2e.rs`) loads this via
//!   `PluginManager::load_bytes`, asserts the tag round-trips, and
//!   asserts a non-transaction directive passes through untouched.
//!
//! Not a real plugin — exists only to load through `Plugin::load_bytes`
//! and prove the macro's wasm32 export-name + symbol contract actually
//! works end to end.

use rustledger_plugin_types::{
    DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput, wasm_plugin_main,
};

fn process(input: PluginInput) -> PluginOutput {
    let mut ops = Vec::with_capacity(input.directives.len());
    for (i, wrapper) in input.directives.into_iter().enumerate() {
        match wrapper.data {
            DirectiveData::Transaction(mut txn) => {
                // Tag every transaction so the host can assert the
                // round-trip preserves directive content.
                txn.tags.push("stub-processed".to_string());
                let new_wrapper = DirectiveWrapper {
                    directive_type: wrapper.directive_type,
                    date: wrapper.date,
                    filename: wrapper.filename,
                    lineno: wrapper.lineno,
                    data: DirectiveData::Transaction(txn),
                };
                ops.push(PluginOp::Modify(i, new_wrapper));
            }
            _ => ops.push(PluginOp::Keep(i)),
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
