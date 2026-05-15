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
/// Unlike the loader's `apply_plugin_ops` — which emits a plugin
/// error and bails on protocol violations — this helper panics in
/// debug builds if the ops set isn't a complete partition over
/// `input` (each input index appears exactly once across Keep /
/// Modify / Delete). The assert is debug-only so release builds and
/// fuzz targets don't pay for it; it's there to make plugin-author
/// mistakes loud in unit tests instead of silently producing
/// surprising materialization.
#[must_use]
pub fn materialize_ops(input: &[DirectiveWrapper], output: &PluginOutput) -> Vec<DirectiveWrapper> {
    #[cfg(debug_assertions)]
    {
        let n = input.len();
        let mut seen = vec![false; n];
        for op in &output.ops {
            let idx = match op {
                PluginOp::Keep(i) | PluginOp::Modify(i, _) | PluginOp::Delete(i) => Some(*i),
                PluginOp::Insert(_) => None,
            };
            if let Some(i) = idx {
                assert!(
                    i < n,
                    "materialize_ops: out-of-bounds index {i} (input len {n})"
                );
                assert!(
                    !seen[i],
                    "materialize_ops: index {i} referenced more than once"
                );
                seen[i] = true;
            }
        }
        for (i, was_seen) in seen.iter().enumerate() {
            assert!(
                *was_seen,
                "materialize_ops: input index {i} not accounted for (must be Keep/Modify/Delete)"
            );
        }
    }

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
