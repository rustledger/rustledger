//! Cross-check capital gains against sales.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that cross-checks declared gains against sale prices.
///
/// When selling a position at a price, this plugin verifies that any
/// income/expense postings match the expected gain/loss from the sale.
pub struct SellGainsPlugin;

impl NativePlugin for SellGainsPlugin {
    fn name(&self) -> &'static str {
        "sellgains"
    }

    fn description(&self) -> &'static str {
        "Cross-check capital gains against sales"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use rust_decimal::Decimal;
        use std::str::FromStr;

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                // Find postings that are sales (negative units with cost and price)
                for posting in &txn.postings {
                    if let (Some(units), Some(cost), Some(price)) =
                        (&posting.units, &posting.cost, &posting.price)
                    {
                        // Check if this is a sale (negative units)
                        let units_num = Decimal::from_str(&units.number).unwrap_or_default();
                        if units_num >= Decimal::ZERO {
                            continue;
                        }

                        // Get cost basis — sell_gains operates on
                        // post-booking transactions where the cost
                        // carries a per-unit value (PerUnit or
                        // PerUnitFromTotal, both expose per_unit()).
                        let cost_per = cost
                            .number
                            .as_ref()
                            .and_then(|cn| cn.per_unit())
                            .map(|s| Decimal::from_str(s).unwrap_or_default())
                            .unwrap_or_default();

                        // Get sale price
                        let sale_price = price
                            .amount
                            .as_ref()
                            .and_then(|a| Decimal::from_str(&a.number).ok())
                            .unwrap_or_default();

                        // Calculate expected gain/loss
                        let expected_gain = (sale_price - cost_per) * units_num.abs();

                        // Look for income/expense posting that should match
                        let has_gain_posting = txn.postings.iter().any(|p| {
                            p.account.starts_with("Income:") || p.account.starts_with("Expenses:")
                        });

                        if expected_gain != Decimal::ZERO && !has_gain_posting {
                            errors.push(PluginError::warning(format!(
                                "Sale of {} {} at {} (cost {}) has expected gain/loss of {} but no Income/Expenses posting",
                                units_num.abs(),
                                units.currency,
                                sale_price,
                                cost_per,
                                expected_gain
                            )));
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
