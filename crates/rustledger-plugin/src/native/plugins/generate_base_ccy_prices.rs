//! Generate base currency prices plugin.
//!
//! This plugin generates additional price entries in a base currency by applying
//! exchange rates to existing prices. For example, if you have:
//! - `2024-01-01 price ETH 2000 EUR`
//! - `2024-01-01 price EUR 1.10 USD`
//!
//! And the base currency is USD, it will generate:
//! - `2024-01-01 price ETH 2200 USD` (2000 * 1.10)
//!
//! Usage:
//! ```beancount
//! plugin "beancount_lazy_plugins.generate_base_ccy_prices" "USD"
//! ```

use std::collections::HashMap;

use rust_decimal::Decimal;

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput, PriceData,
};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin for generating base currency prices.
pub struct GenerateBaseCcyPricesPlugin;

impl NativePlugin for GenerateBaseCcyPricesPlugin {
    fn name(&self) -> &'static str {
        "generate_base_ccy_prices"
    }

    fn description(&self) -> &'static str {
        "Generate base currency prices by applying exchange rates"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Get the base currency from config
        let base_ccy = match &input.config {
            Some(config) => config
                .trim()
                .trim_matches('"')
                .trim_matches('\'')
                .to_string(),
            None => {
                // If no config, just return unchanged
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors: Vec::new(),
                };
            }
        };

        // Build price map: (currency, quote_currency) -> Vec<(date, rate)>
        let price_map = build_price_map(&input.directives);

        // Find additional entries to generate
        let mut additional_entries = Vec::new();

        for directive in &input.directives {
            if directive.directive_type != "price" {
                continue;
            }

            if let DirectiveData::Price(price) = &directive.data {
                // Skip if price is already in base currency
                if price.amount.currency == base_ccy || price.currency == base_ccy {
                    continue;
                }

                // Try to find FX rate from price currency to base currency
                let fx_tuple = (price.amount.currency.clone(), base_ccy.clone());
                if let Some(fx_rate) = get_price(&price_map, &fx_tuple, &directive.date) {
                    // Check if price in base currency already exists
                    let target_tuple = (price.currency.clone(), base_ccy.clone());
                    if already_existing_price(&price_map, &target_tuple, &directive.date) {
                        continue;
                    }

                    // Calculate price in base currency
                    if let Ok(price_number) = price.amount.number.parse::<Decimal>() {
                        let price_in_base = price_number * fx_rate;

                        additional_entries.push(DirectiveWrapper {
                            directive_type: "price".to_string(),
                            date: directive.date.clone(),
                            filename: directive.filename.clone(),
                            lineno: directive.lineno,
                            data: DirectiveData::Price(PriceData {
                                currency: price.currency.clone(),
                                amount: AmountData {
                                    number: format_decimal(price_in_base),
                                    currency: base_ccy.clone(),
                                },
                                metadata: vec![],
                            }),
                        });
                    }
                }
            }
        }

        // Keep all original directives, then insert generated price entries.
        let mut ops: Vec<PluginOp> = (0..input.directives.len()).map(PluginOp::Keep).collect();
        for w in additional_entries {
            ops.push(PluginOp::Insert(w));
        }

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

impl RegularPlugin for GenerateBaseCcyPricesPlugin {}

/// Build a price map from directives.
/// Returns a map from (currency, `quote_currency`) to Vec<(date, rate)>
fn build_price_map(
    directives: &[DirectiveWrapper],
) -> HashMap<(String, String), Vec<(String, Decimal)>> {
    let mut price_map: HashMap<(String, String), Vec<(String, Decimal)>> = HashMap::new();

    for directive in directives {
        if directive.directive_type != "price" {
            continue;
        }

        if let DirectiveData::Price(price) = &directive.data
            && let Ok(rate) = price.amount.number.parse::<Decimal>()
        {
            let key = (price.currency.clone(), price.amount.currency.clone());
            price_map
                .entry(key)
                .or_default()
                .push((directive.date.clone(), rate));
        }
    }

    price_map
}

/// Get price for a currency pair on a specific date.
fn get_price(
    price_map: &HashMap<(String, String), Vec<(String, Decimal)>>,
    pair: &(String, String),
    date: &str,
) -> Option<Decimal> {
    let prices = price_map.get(pair)?;

    // Find exact date match or closest date before
    let mut best_match: Option<(&str, Decimal)> = None;

    for (price_date, rate) in prices {
        if price_date.as_str() <= date {
            match &best_match {
                None => best_match = Some((price_date.as_str(), *rate)),
                Some((best_date, _)) => {
                    if price_date.as_str() > *best_date {
                        best_match = Some((price_date.as_str(), *rate));
                    }
                }
            }
        }
    }

    best_match.map(|(_, rate)| rate)
}

/// Check if a price already exists for the given pair on the given date.
fn already_existing_price(
    price_map: &HashMap<(String, String), Vec<(String, Decimal)>>,
    pair: &(String, String),
    date: &str,
) -> bool {
    if let Some(prices) = price_map.get(pair) {
        for (price_date, _) in prices {
            if price_date == date {
                return true;
            }
        }
    }
    false
}

/// Format a decimal number, trimming trailing zeros.
fn format_decimal(d: Decimal) -> String {
    let s = d.to_string();
    // If it has a decimal point, trim trailing zeros
    if s.contains('.') {
        let trimmed = s.trim_end_matches('0').trim_end_matches('.');
        trimmed.to_string()
    } else {
        s
    }
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_price(
        date: &str,
        currency: &str,
        number: &str,
        quote_currency: &str,
    ) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "price".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Price(PriceData {
                currency: currency.to_string(),
                amount: AmountData {
                    number: number.to_string(),
                    currency: quote_currency.to_string(),
                },
                metadata: vec![],
            }),
        }
    }

    #[test]
    fn test_generate_base_ccy_price() {
        let plugin = GenerateBaseCcyPricesPlugin;

        // Create test data:
        // ETH priced in EUR
        // EUR priced in USD (base currency)
        let input = PluginInput {
            directives: vec![
                create_price("2024-01-01", "EUR", "1.10", "USD"),
                create_price("2024-01-01", "ETH", "2000", "EUR"),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("USD".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Should have original 2 prices + 1 generated (ETH in USD)
        assert_eq!(directives.len(), 3);

        // Find the generated price
        let generated_prices: Vec<_> = directives
            .iter()
            .filter(|d| {
                if let DirectiveData::Price(p) = &d.data {
                    p.currency == "ETH" && p.amount.currency == "USD"
                } else {
                    false
                }
            })
            .collect();

        assert_eq!(generated_prices.len(), 1);

        if let DirectiveData::Price(p) = &generated_prices[0].data {
            // 2000 EUR * 1.10 USD/EUR = 2200 USD
            assert_eq!(p.amount.number, "2200");
        } else {
            panic!("Expected Price directive");
        }
    }

    #[test]
    fn test_no_generation_when_already_in_base() {
        let plugin = GenerateBaseCcyPricesPlugin;

        // ETH directly priced in USD (base currency) - no generation needed
        let input = PluginInput {
            directives: vec![create_price("2024-01-01", "ETH", "2200", "USD")],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("USD".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);
        // Should have only the original price
        assert_eq!(directives.len(), 1);
    }

    #[test]
    fn test_no_generation_when_price_exists() {
        let plugin = GenerateBaseCcyPricesPlugin;

        // ETH priced in EUR and also directly in USD
        let input = PluginInput {
            directives: vec![
                create_price("2024-01-01", "EUR", "1.10", "USD"),
                create_price("2024-01-01", "ETH", "2000", "EUR"),
                create_price("2024-01-01", "ETH", "2200", "USD"), // Already exists
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("USD".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);
        // Should have only original 3 prices
        assert_eq!(directives.len(), 3);
    }

    #[test]
    fn test_no_config_unchanged() {
        let plugin = GenerateBaseCcyPricesPlugin;

        let input = PluginInput {
            directives: vec![create_price("2024-01-01", "ETH", "2000", "EUR")],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 1);
    }
}
