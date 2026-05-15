//! Hash-based duplicate transaction detection.
//!
//! Thin wrapper around [`rustledger_ops::dedup::find_structural_duplicates`].
//! The core hashing and dedup logic lives in `rustledger-ops`; this plugin
//! adapts it to the `NativePlugin` interface.
//!
//! Mirrors Python beancount's `beancount.plugins.noduplicates`.

use crate::types::{PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that detects duplicate transactions based on structural hash.
pub struct NoDuplicatesPlugin;

impl NativePlugin for NoDuplicatesPlugin {
    fn name(&self) -> &'static str {
        "noduplicates"
    }

    fn description(&self) -> &'static str {
        "Hash-based duplicate transaction detection"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let duplicates = rustledger_ops::dedup::find_structural_duplicates(&input.directives);
        let errors = duplicates
            .iter()
            .map(rustledger_ops::dedup::StructuralDuplicate::to_plugin_error)
            .collect();

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}
