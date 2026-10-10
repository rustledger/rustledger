//! A currency is held at cost everywhere or nowhere.

use crate::types::{
    DirectiveData, DirectiveWrapper, PluginError, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::at_entry;

/// Plugin that checks every currency is held either always at cost or
/// never at cost.
///
/// As beancount's `coherent_cost` (#2539): a currency some posting holds at
/// cost (`{...}`) and another holds without one is an error, located at the
/// first transaction holding it without cost. Before, only a posting with a
/// price and no cost counted as "without cost", so `10 HOOL {5 USD}` next to
/// a plain `1 HOOL` passed, where bean-check reports it.
pub struct CoherentCostPlugin;

impl NativePlugin for CoherentCostPlugin {
    fn name(&self) -> &'static str {
        "coherent_cost"
    }

    fn description(&self) -> &'static str {
        "Enforce consistent cost tracking per currency"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashMap;

        // Each currency's first transaction with and without cost.
        let mut with_cost: HashMap<&str, &DirectiveWrapper> = HashMap::new();
        let mut without_cost: HashMap<&str, &DirectiveWrapper> = HashMap::new();
        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        let target = if posting.cost.is_some() {
                            &mut with_cost
                        } else {
                            &mut without_cost
                        };
                        target.entry(units.currency.as_str()).or_insert(wrapper);
                    }
                }
            }
        }

        // Sorted by currency: beancount iterates a set, whose order varies
        // from run to run.
        let mut inconsistent: Vec<(&str, &DirectiveWrapper)> = without_cost
            .into_iter()
            .filter(|(currency, _)| with_cost.contains_key(currency))
            .collect();
        inconsistent.sort_unstable_by_key(|(currency, _)| *currency);
        let errors = inconsistent
            .into_iter()
            .map(|(currency, wrapper)| {
                at_entry(
                    PluginError::error(format!(
                        "Currency '{currency}' is used both with and without cost"
                    )),
                    wrapper,
                )
            })
            .collect();

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for CoherentCostPlugin {}
