//! Zero balance assertion on account closing.

use crate::types::{
    AmountData, BalanceData, DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput,
    PostingData,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::{falsy, increment_date};

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
        let mut inserts: Vec<PluginOp> = Vec::new();

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
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                ops.push(PluginOp::Keep(i));
                continue;
            };
            // As beancount's plugin: any truthy `closing` value marks the
            // posting (it read only `TRUE`), and the marker is removed from
            // the posting once expanded (#2600).
            let closing = |posting: &PostingData| {
                posting
                    .metadata
                    .iter()
                    .any(|(key, val)| key == "closing" && !falsy(val))
            };
            if !txn.postings.iter().any(closing) {
                ops.push(PluginOp::Keep(i));
                continue;
            }
            let mut modified = txn.clone();
            for posting in &mut modified.postings {
                if !closing(posting) {
                    continue;
                }
                posting.metadata.retain(|(key, _)| key != "closing");
                if let Some(next_date) = increment_date(&wrapper.date) {
                    let currency = posting
                        .units
                        .as_ref()
                        .map_or_else(|| default_currency.clone(), |u| u.currency.clone());

                    inserts.push(PluginOp::Insert(DirectiveWrapper {
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
            ops.push(PluginOp::Modify(
                i,
                DirectiveWrapper {
                    data: DirectiveData::Transaction(modified),
                    ..wrapper.clone()
                },
            ));
        }
        ops.extend(inserts);

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

impl RegularPlugin for CheckClosingPlugin {}
