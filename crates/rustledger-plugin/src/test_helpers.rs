//! Helpers shared between in-crate tests and integration tests.
//!
//! These are kept in a public module (rather than `#[cfg(test)]`) so
//! the `tests/` integration tests can reach them without duplicating
//! materialization logic.

use crate::types::{DirectiveWrapper, PluginOp, PluginOutput};

/// Materialize a plugin's `ops` against its input directive list,
/// producing the resulting flat list of wrappers.
///
/// Used by tests that want to inspect a plugin's effective output
/// without going through the loader's `apply_plugin_ops`. The mapping
/// is:
/// - `Keep(i)` → `input[i].clone()`
/// - `Modify(_, w)` and `Insert(w)` → `w.clone()`
/// - `Delete(_)` → omitted
///
/// Note that, unlike the loader's `apply_plugin_ops`, this helper
/// does **not** validate the ops protocol invariants — it's purely a
/// materialization shortcut for assertions.
#[must_use]
pub fn materialize_ops(input: &[DirectiveWrapper], output: &PluginOutput) -> Vec<DirectiveWrapper> {
    let mut out = Vec::with_capacity(output.ops.len());
    for op in &output.ops {
        match op {
            PluginOp::Keep(i) => {
                if let Some(w) = input.get(*i) {
                    out.push(w.clone());
                }
            }
            PluginOp::Modify(_, w) | PluginOp::Insert(w) => out.push(w.clone()),
            PluginOp::Delete(_) => {}
        }
    }
    out
}
