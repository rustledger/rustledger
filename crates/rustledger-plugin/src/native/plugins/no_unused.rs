//! Warn about unused accounts.

use crate::types::{
    DirectiveData, MetaValueData, PluginError, PluginInput, PluginOp, PluginOutput,
};

use super::super::NativePlugin;

/// Plugin that identifies accounts that are opened but never used.
///
/// Reports a warning for each account that has an Open directive but is never
/// referenced in any transaction, balance, pad, or other directive.
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

        let mut opened_accounts: HashSet<String> = HashSet::new();
        let mut used_accounts: HashSet<String> = HashSet::new();

        // Collect all opened accounts and used accounts in one pass
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Open(data) => {
                    opened_accounts.insert(data.account.clone());
                }
                DirectiveData::Close(data) => {
                    // Closing an account counts as using it
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        used_accounts.insert(posting.account.clone());
                    }
                }
                DirectiveData::Balance(data) => {
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Pad(data) => {
                    used_accounts.insert(data.account.clone());
                    used_accounts.insert(data.source_account.clone());
                }
                DirectiveData::Note(data) => {
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Document(data) => {
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Custom(data) => {
                    // Check custom directive values for account references
                    for value in &data.values {
                        if let MetaValueData::Account(account) = value {
                            used_accounts.insert(account.clone());
                        }
                    }
                }
                _ => {}
            }
        }

        // Find unused accounts (opened but never used)
        let mut errors = Vec::new();
        let mut unused: Vec<_> = opened_accounts
            .difference(&used_accounts)
            .cloned()
            .collect();
        unused.sort(); // Consistent ordering for output

        for account in unused {
            errors.push(PluginError::warning(format!(
                "Account '{account}' is opened but never used"
            )));
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

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
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("Assets:Unused"));
        assert!(output.errors[0].message.contains("never used"));
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
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
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
            },
            config: None,
        };

        let output = plugin.process(input);
        // Close counts as usage, so no warning
        assert_eq!(output.errors.len(), 0);
    }
}
