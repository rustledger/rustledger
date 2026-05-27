//! Enforce single commodity per account.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin that enforces single commodity per account.
pub struct OneCommodityPlugin;

impl NativePlugin for OneCommodityPlugin {
    fn name(&self) -> &'static str {
        "onecommodity"
    }

    fn description(&self) -> &'static str {
        "Enforce single commodity per account"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashMap;

        // Track currencies used per account
        let mut account_currencies: HashMap<String, String> = HashMap::new();
        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        if let Some(existing) = account_currencies.get(&posting.account) {
                            if existing != &units.currency {
                                errors.push(PluginError::error(format!(
                                    "Account '{}' uses multiple currencies: {} and {}",
                                    posting.account, existing, units.currency
                                )));
                            }
                        } else {
                            account_currencies
                                .insert(posting.account.clone(), units.currency.clone());
                        }
                    }
                }
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for OneCommodityPlugin {}
