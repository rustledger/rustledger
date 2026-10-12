//! Enable all strict validation rules.

use crate::types::{PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::check_commodity::CheckCommodityPlugin;
use super::check_drained::CheckDrainedPlugin;
use super::coherent_cost::CoherentCostPlugin;
use super::leaf_only::LeafOnlyPlugin;
use super::no_duplicates::NoDuplicatesPlugin;
use super::no_unused::NoUnusedPlugin;
use super::one_commodity::OneCommodityPlugin;
use super::sell_gains::SellGainsPlugin;
use super::unique_prices::UniquePricesPlugin;

/// Meta-plugin that runs every pedantic plugin, as beancount's does.
///
/// They run in beancount's order: `check_commodity`, `coherent_cost`,
/// `leafonly`, `noduplicates`, `nounused`, `onecommodity`, `sellgains`,
/// `unique_prices`, then `check_drained`. Each runs without a config.
///
/// It ran only four of the nine before (#2600): `coherent_cost`, `nounused`,
/// `sellgains`, `unique_prices` and `check_drained` were missing.
pub struct PedanticPlugin;

impl NativePlugin for PedanticPlugin {
    fn name(&self) -> &'static str {
        "pedantic"
    }

    fn description(&self) -> &'static str {
        "Enable all strict validation rules"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let run = |plugin: &dyn NativePlugin| {
            plugin.process(PluginInput {
                directives: input.directives.clone(),
                options: input.options.clone(),
                config: None,
            })
        };
        let validators: [&dyn NativePlugin; 8] = [
            &CheckCommodityPlugin,
            &CoherentCostPlugin,
            &LeafOnlyPlugin,
            &NoDuplicatesPlugin,
            &NoUnusedPlugin,
            &OneCommodityPlugin,
            &SellGainsPlugin,
            &UniquePricesPlugin,
        ];
        let mut errors = Vec::new();
        for plugin in validators {
            let output = run(plugin);
            // beancount chains the plugins, each fed the entries the one
            // before returned. These eight keep every entry as it is, so each
            // sees the input unchanged, and only `check_drained`, last,
            // changes anything.
            debug_assert!(
                output
                    .ops
                    .iter()
                    .enumerate()
                    .all(|(i, op)| matches!(op, PluginOp::Keep(k) if *k == i)),
                "{} must keep every entry",
                plugin.name()
            );
            errors.extend(output.errors);
        }
        let drained = run(&CheckDrainedPlugin);
        errors.extend(drained.errors);

        PluginOutput {
            ops: drained.ops,
            errors,
        }
    }
}

impl RegularPlugin for PedanticPlugin {}
