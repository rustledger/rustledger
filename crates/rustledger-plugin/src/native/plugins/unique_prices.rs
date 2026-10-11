//! One price per day per currency pair.

use crate::types::{
    DirectiveData, DirectiveWrapper, PluginError, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::at_entry;

/// Plugin that enforces unique prices (one per commodity pair per day).
///
/// As beancount's `unique_prices` (#2539): prices of one pair on one day
/// that disagree are one error, "Disagreeing price entries", located as
/// beancount locates it (the last entry holding the first number given).
/// Prices that agree are allowed, as in beancount: before, a repeated,
/// identical price was an error.
pub struct UniquePricesPlugin;

impl NativePlugin for UniquePricesPlugin {
    fn name(&self) -> &'static str {
        "unique_prices"
    }

    fn description(&self) -> &'static str {
        "One price per day per currency pair"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashMap;

        // (date, base, quote) -> its prices, keys in first-seen order.
        let mut order: Vec<(&str, &str, &str)> = Vec::new();
        let mut prices: HashMap<(&str, &str, &str), Vec<&DirectiveWrapper>> = HashMap::new();
        for wrapper in &input.directives {
            if let DirectiveData::Price(price) = &wrapper.data {
                let key = (
                    wrapper.date.as_str(),
                    price.currency.as_str(),
                    price.amount.currency.as_str(),
                );
                prices
                    .entry(key)
                    .or_insert_with(|| {
                        order.push(key);
                        Vec::new()
                    })
                    .push(wrapper);
            }
        }

        let number = |w: &DirectiveWrapper| match &w.data {
            DirectiveData::Price(p) => p.amount.number.parse::<rust_decimal::Decimal>().ok(),
            _ => None,
        };
        let mut errors = Vec::new();
        for key in order {
            let entries = &prices[&key];
            let Some(first) = entries.first().map(|w| number(w)) else {
                continue;
            };
            if entries.iter().all(|w| number(w) == first) {
                continue;
            }
            // beancount maps number -> entry, the last entry with that
            // number winning, and reports the first number's entry.
            let located = entries
                .iter()
                .rev()
                .find(|w| number(w) == first)
                .copied()
                .unwrap_or(entries[0]);
            errors.push(at_entry(
                PluginError::error("Disagreeing price entries"),
                located,
            ));
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for UniquePricesPlugin {}
