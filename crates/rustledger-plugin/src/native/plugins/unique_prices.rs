//! One price per day per currency pair.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that enforces unique prices (one per commodity pair per day).
pub struct UniquePricesPlugin;

impl NativePlugin for UniquePricesPlugin {
    fn name(&self) -> &'static str {
        "unique_prices"
    }

    fn description(&self) -> &'static str {
        "One price per day per currency pair"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        // Track (date, base_currency, quote_currency) tuples
        let mut seen: HashSet<(String, String, String)> = HashSet::new();
        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Price(price) = &wrapper.data {
                let key = (
                    wrapper.date.clone(),
                    price.currency.clone(),
                    price.amount.currency.clone(),
                );
                if !seen.insert(key.clone()) {
                    errors.push(PluginError::error(format!(
                        "Duplicate price for {}/{} on {}",
                        price.currency, price.amount.currency, wrapper.date
                    )));
                }
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}
