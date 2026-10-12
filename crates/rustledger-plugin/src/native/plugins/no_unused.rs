//! Report unused accounts.

use crate::types::{
    DirectiveData, DirectiveWrapper, MetaValueData, PluginError, PluginInput, PluginOp,
    PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::at_entry;

/// Plugin that identifies accounts that are opened but never used.
///
/// Reports an error, at its `open`, for each account that has an Open
/// directive but is never referenced in any transaction, balance, pad, or
/// other directive.
pub struct NoUnusedPlugin;

impl NativePlugin for NoUnusedPlugin {
    fn name(&self) -> &'static str {
        "nounused"
    }

    fn description(&self) -> &'static str {
        "Warn about unused accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        // Each opened account with its `open`, in the order accounts are first
        // opened; a repeated `open` replaces the entry and keeps the position,
        // as beancount's `open_map` dict does.
        let mut opens: Vec<(&str, &DirectiveWrapper)> = Vec::new();
        let mut used_accounts: HashSet<&str> = HashSet::new();

        // Collect all opened accounts and used accounts in one pass
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Open(data) => {
                    if let Some(entry) = opens.iter_mut().find(|(a, _)| *a == data.account) {
                        entry.1 = wrapper;
                    } else {
                        opens.push((&data.account, wrapper));
                    }
                }
                DirectiveData::Close(data) => {
                    // Closing an account counts as using it
                    used_accounts.insert(&data.account);
                }
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        used_accounts.insert(&posting.account);
                    }
                }
                DirectiveData::Balance(data) => {
                    used_accounts.insert(&data.account);
                }
                DirectiveData::Pad(data) => {
                    used_accounts.insert(&data.account);
                    used_accounts.insert(&data.source_account);
                }
                DirectiveData::Note(data) => {
                    used_accounts.insert(&data.account);
                }
                DirectiveData::Document(data) => {
                    used_accounts.insert(&data.account);
                }
                // Deliberate divergence: beancount's `getters` reads no
                // account from a `custom` directive, so an account only a
                // `custom` names (a budget, say) is reported unused there.
                // It is used, so it is not reported here.
                DirectiveData::Custom(data) => {
                    for value in &data.values {
                        if let MetaValueData::Account(account) = value {
                            used_accounts.insert(account);
                        }
                    }
                }
                _ => {}
            }
        }

        // As beancount reports it (#2600): its message, an error, at the
        // account's `open`. It was a warning of rledger's own words with no
        // location.
        let errors = opens
            .into_iter()
            .filter(|(account, _)| !used_accounts.contains(account))
            .map(|(account, open)| {
                at_entry(
                    PluginError::error(format!("Unused account '{account}'")),
                    open,
                )
            })
            .collect();

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for NoUnusedPlugin {}

#[cfg(test)]
mod nounused_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_nounused_reports_unused_account() {
        let plugin = NoUnusedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Unused".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Test".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        // beancount's message, as an error (#2600).
        assert_eq!(output.errors[0].message, "Unused account 'Assets:Unused'");
        assert_eq!(
            output.errors[0].severity,
            crate::types::PluginErrorSeverity::Error
        );
    }

    #[test]
    fn test_nounused_no_warning_for_used_accounts() {
        let plugin = NoUnusedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Test".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_nounused_close_counts_as_used() {
        let plugin = NoUnusedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:OldAccount".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Close(CloseData {
                        account: "Assets:OldAccount".to_string(),
                        metadata: vec![],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let output = plugin.process(input);
        // Close counts as usage, so no warning
        assert_eq!(output.errors.len(), 0);
    }
}
