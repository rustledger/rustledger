//! Calculate unrealized gains/losses.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin that calculates unrealized gains on positions.
///
/// For each position held at cost, this plugin can generate unrealized
/// gain/loss entries based on current market prices from the price database.
pub struct UnrealizedPlugin {
    /// Account to book unrealized gains to.
    pub gains_account: String,
}

impl UnrealizedPlugin {
    /// Create a new plugin with the default gains account.
    pub fn new() -> Self {
        Self {
            gains_account: "Income:Unrealized".to_string(),
        }
    }

    /// Create with a custom gains account.
    pub const fn with_account(account: String) -> Self {
        Self {
            gains_account: account,
        }
    }
}

impl Default for UnrealizedPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for UnrealizedPlugin {
    fn name(&self) -> &'static str {
        "unrealized"
    }

    fn description(&self) -> &'static str {
        "Calculate unrealized gains/losses"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use rust_decimal::Decimal;
        use std::collections::HashMap;
        use std::str::FromStr;

        // Build price database from Price directives
        let mut prices: HashMap<(String, String), (String, Decimal)> = HashMap::new(); // (base, quote) -> (date, price)

        for wrapper in &input.directives {
            if let DirectiveData::Price(price) = &wrapper.data {
                let key = (price.currency.clone(), price.amount.currency.clone());
                let price_val = Decimal::from_str(&price.amount.number).unwrap_or_default();

                // Keep the most recent price
                if let Some((existing_date, _)) = prices.get(&key) {
                    if &wrapper.date > existing_date {
                        prices.insert(key, (wrapper.date.clone(), price_val));
                    }
                } else {
                    prices.insert(key, (wrapper.date.clone(), price_val));
                }
            }
        }

        // Track positions by account
        let mut positions: HashMap<String, HashMap<String, (Decimal, Decimal)>> = HashMap::new(); // account -> currency -> (units, cost_basis)

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        let units_num = Decimal::from_str(&units.number).unwrap_or_default();

                        // Unrealized-gains operates on post-booking
                        // transactions. Prefer the preserved total
                        // when available (PerUnitFromTotal) for exact
                        // cost basis; fall back to per_unit * |units|
                        // for source `{...}` per-unit costs.
                        let cost_basis = posting
                            .cost
                            .as_ref()
                            .and_then(|c| c.number.as_ref())
                            .map_or(Decimal::ZERO, |cn| match cn.total() {
                                Some(s) => Decimal::from_str(s).unwrap_or_default(),
                                None => cn
                                    .per_unit()
                                    .map(|s| {
                                        Decimal::from_str(s).unwrap_or_default() * units_num.abs()
                                    })
                                    .unwrap_or_default(),
                            });

                        let account_positions =
                            positions.entry(posting.account.clone()).or_default();

                        let (existing_units, existing_cost) = account_positions
                            .entry(units.currency.clone())
                            .or_insert((Decimal::ZERO, Decimal::ZERO));

                        *existing_units += units_num;
                        *existing_cost += cost_basis;
                    }
                }
            }
        }

        // Calculate unrealized gains for positions with known prices
        for (account, currencies) in &positions {
            for (currency, (units, cost_basis)) in currencies {
                if *units == Decimal::ZERO {
                    continue;
                }

                // Look for a price to the operating currency (assume USD for now)
                if let Some((_, market_price)) = prices.get(&(currency.clone(), "USD".to_string()))
                {
                    let market_value = *units * market_price;
                    let unrealized_gain = market_value - cost_basis;

                    if unrealized_gain.abs() > Decimal::new(1, 2) {
                        // More than $0.01
                        errors.push(PluginError::warning(format!(
                            "Unrealized gain on {units} {currency} in {account}: {unrealized_gain} USD"
                        )));
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

impl RegularPlugin for UnrealizedPlugin {}
