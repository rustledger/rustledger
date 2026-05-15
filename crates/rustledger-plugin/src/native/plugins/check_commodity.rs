//! Plugin that checks all used commodities are declared.

use std::collections::HashSet;

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that checks all used commodities are declared.
pub struct CheckCommodityPlugin;

impl NativePlugin for CheckCommodityPlugin {
    fn name(&self) -> &'static str {
        "check_commodity"
    }

    fn description(&self) -> &'static str {
        "Verify all commodities are declared"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut declared_commodities: HashSet<String> = HashSet::new();
        let mut used_commodities: HashSet<String> = HashSet::new();
        let mut errors = Vec::new();

        // First pass: collect declared commodities
        for wrapper in &input.directives {
            if wrapper.directive_type == "commodity"
                && let DirectiveData::Commodity(ref comm) = wrapper.data
            {
                declared_commodities.insert(comm.currency.clone());
            }
        }

        // Second pass: collect used commodities and check
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        if let Some(ref units) = posting.units {
                            used_commodities.insert(units.currency.clone());
                        }
                        if let Some(ref cost) = posting.cost
                            && let Some(ref currency) = cost.currency
                        {
                            used_commodities.insert(currency.clone());
                        }
                    }
                }
                DirectiveData::Balance(bal) => {
                    used_commodities.insert(bal.amount.currency.clone());
                }
                DirectiveData::Price(price) => {
                    used_commodities.insert(price.currency.clone());
                    used_commodities.insert(price.amount.currency.clone());
                }
                _ => {}
            }
        }

        // Report undeclared commodities
        for currency in &used_commodities {
            if !declared_commodities.contains(currency) {
                errors.push(PluginError::warning(format!(
                    "commodity '{currency}' used but not declared"
                )));
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}
