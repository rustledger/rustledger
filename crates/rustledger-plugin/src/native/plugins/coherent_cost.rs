//! Enforce consistent cost tracking per currency.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that ensures currencies are tracked consistently with cost or price-only.
///
/// If a currency is used with cost notation `{...}` in some postings, it should
/// not be used with price-only notation `@` (without cost) in other postings,
/// as this indicates inconsistent tracking.
///
/// Note: Having BOTH cost AND price on the same posting is valid and common
/// when selling positions (cost = acquisition price, price = sale price).
pub struct CoherentCostPlugin;

impl NativePlugin for CoherentCostPlugin {
    fn name(&self) -> &'static str {
        "coherent_cost"
    }

    fn description(&self) -> &'static str {
        "Enforce consistent cost tracking per currency"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        // Track currencies used with cost (with or without price)
        // Use references to avoid cloning currency strings
        let mut currencies_with_cost: HashSet<&str> = HashSet::new();
        // Track currencies used with price-only (no cost)
        let mut currencies_with_price_only: HashSet<&str> = HashSet::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        let currency = units.currency.as_str();

                        // Check if this posting has cost
                        if posting.cost.is_some() {
                            currencies_with_cost.insert(currency);
                        } else if posting.price.is_some() {
                            // Price-only (no cost) - this is the problematic case
                            currencies_with_price_only.insert(currency);
                        }
                    }
                }
            }
        }

        // Find currencies used with cost in some places and price-only in others
        // Collect and sort for deterministic error ordering
        let mut inconsistent: Vec<_> = currencies_with_cost
            .intersection(&currencies_with_price_only)
            .copied()
            .collect();
        inconsistent.sort_unstable();

        let errors: Vec<_> = inconsistent
            .into_iter()
            .map(|currency| {
                PluginError::error(format!(
                    "Currency '{currency}' is used with both cost and price-only notation - this may cause inconsistencies"
                ))
            })
            .collect();

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}
