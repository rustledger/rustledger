//! Hash-based duplicate transaction detection.
//!
//! Thin wrapper around [`rustledger_ops::dedup::find_structural_duplicates`].
//! The core hashing and dedup logic lives in `rustledger-ops`; this plugin
//! adapts it to the `NativePlugin` interface.
//!
//! Mirrors Python beancount's `beancount.plugins.noduplicates`.

use crate::types::{PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::at_entry;

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
        // Each located at the later copy, as beancount's `noduplicates`
        // locates it (#2539; before, unlocated).
        let errors = duplicates
            .iter()
            .map(|d| at_entry(d.to_plugin_error(), &input.directives[d.index]))
            .collect();

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for NoDuplicatesPlugin {}
