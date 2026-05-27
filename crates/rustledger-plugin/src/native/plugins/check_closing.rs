//! Zero balance assertion on account closing.

use crate::types::{
    AmountData, BalanceData, DirectiveData, DirectiveWrapper, MetaValueData, PluginInput, PluginOp,
    PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::increment_date;

/// Plugin that inserts zero balance assertion when posting has `closing: TRUE` metadata.
///
/// When a posting has metadata `closing: TRUE`, this plugin adds a balance assertion
/// for that account with zero balance on the next day.
pub struct CheckClosingPlugin;

impl NativePlugin for CheckClosingPlugin {
    fn name(&self) -> &'static str {
        "check_closing"
    }

    fn description(&self) -> &'static str {
        "Zero balance assertion on account closing"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut ops: Vec<PluginOp> = Vec::new();

        // Default currency for auto-balanced (units=None) closing postings:
        // prefer the user's first operating currency, falling back to "USD"
        // when none is configured. Closes #1039.
        let default_currency = input
            .options
            .operating_currencies
            .first()
            .cloned()
            .unwrap_or_else(|| "USD".to_string());

        for (i, wrapper) in input.directives.iter().enumerate() {
            ops.push(PluginOp::Keep(i));

            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    // Check for closing: TRUE metadata
                    let has_closing = posting.metadata.iter().any(|(key, val)| {
                        key == "closing" && matches!(val, MetaValueData::Bool(true))
                    });

                    if has_closing {
                        // Parse the date and add one day
                        if let Some(next_date) = increment_date(&wrapper.date) {
                            // Use the posting's units currency if present,
                            // otherwise the resolved default (operating
                            // currency or "USD" fallback).
                            let currency = posting
                                .units
                                .as_ref()
                                .map_or_else(|| default_currency.clone(), |u| u.currency.clone());

                            // Add zero balance assertion
                            ops.push(PluginOp::Insert(DirectiveWrapper {
                                directive_type: "balance".to_string(),
                                date: next_date,
                                filename: None, // Plugin-generated
                                lineno: None,
                                data: DirectiveData::Balance(BalanceData {
                                    account: posting.account.clone(),
                                    amount: AmountData {
                                        number: "0".to_string(),
                                        currency,
                                    },
                                    tolerance: None,
                                    metadata: vec![],
                                }),
                            }));
                        }
                    }
                }
            }
        }

        // Final ordering is the loader's responsibility — it re-sorts
        // directives after the plugin pass.
        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

impl RegularPlugin for CheckClosingPlugin {}
