//! Enable all strict validation rules.

use crate::types::{PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;
use super::check_commodity::CheckCommodityPlugin;
use super::leaf_only::LeafOnlyPlugin;
use super::no_duplicates::NoDuplicatesPlugin;
use super::one_commodity::OneCommodityPlugin;

/// Meta-plugin that enables all strict validation plugins.
///
/// This plugin runs multiple validation checks:
/// - leafonly: No postings to parent accounts
/// - onecommodity: Single currency per account
/// - `check_commodity`: All currencies must be declared
/// - noduplicates: No duplicate transactions
pub struct PedanticPlugin;

impl NativePlugin for PedanticPlugin {
    fn name(&self) -> &'static str {
        "pedantic"
    }

    fn description(&self) -> &'static str {
        "Enable all strict validation rules"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut all_errors = Vec::new();

        // Run leafonly checks
        let leafonly = LeafOnlyPlugin;
        let result = leafonly.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        // Run onecommodity checks
        let onecommodity = OneCommodityPlugin;
        let result = onecommodity.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        // Run noduplicates checks
        let noduplicates = NoDuplicatesPlugin;
        let result = noduplicates.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        // Run check_commodity checks
        let check_commodity = CheckCommodityPlugin;
        let result = check_commodity.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors: all_errors,
        }
    }
}
