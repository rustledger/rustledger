//! Plugin for Regular Expected Transactions (beanahead).
//!
//! Sets default metadata values for transactions tagged with `#rx_txn`.
//! This is used by the beanahead tool for managing recurring transactions.

use crate::types::{DirectiveData, MetaValueData, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Tag used to identify Regular Expected Transactions.
const TAG_RX: &str = "rx_txn";

/// Plugin for Regular Expected Transactions.
///
/// For transactions tagged with `#rx_txn`, this plugin sets default
/// metadata values:
/// - `final`: None (null)
/// - `roll`: True
pub struct RxTxnPlugin;

impl NativePlugin for RxTxnPlugin {
    fn name(&self) -> &'static str {
        "rx_txn_plugin"
    }

    fn description(&self) -> &'static str {
        "Set default metadata for Regular Expected Transactions (beanahead)"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());
        for (i, mut wrapper) in input.directives.into_iter().enumerate() {
            let needs_change = matches!(&wrapper.data, DirectiveData::Transaction(t)
                if t.tags.contains(&TAG_RX.to_string())
                    && (!t.metadata.iter().any(|(k, _)| k == "final")
                        || !t.metadata.iter().any(|(k, _)| k == "roll")));

            if !needs_change {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            if let DirectiveData::Transaction(ref mut txn) = wrapper.data {
                let has_final = txn.metadata.iter().any(|(k, _)| k == "final");
                let has_roll = txn.metadata.iter().any(|(k, _)| k == "roll");

                if !has_final {
                    txn.metadata.push((
                        "final".to_string(),
                        MetaValueData::String("None".to_string()),
                    ));
                }
                if !has_roll {
                    txn.metadata.push((
                        "roll".to_string(),
                        MetaValueData::String("True".to_string()),
                    ));
                }
            }
            ops.push(PluginOp::Modify(i, wrapper));
        }

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_test_transaction(tags: Vec<&str>, metadata: Vec<(&str, &str)>) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: Some("Test".to_string()),
                narration: "Test transaction".to_string(),
                tags: tags.into_iter().map(String::from).collect(),
                links: vec![],
                metadata: metadata
                    .into_iter()
                    .map(|(k, v)| (k.to_string(), MetaValueData::String(v.to_string())))
                    .collect(),
                postings: vec![
                    PostingData {
                        account: "Assets:Cash".to_string(),
                        units: Some(AmountData {
                            number: "-100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    },
                    PostingData {
                        account: "Expenses:Test".to_string(),
                        units: Some(AmountData {
                            number: "100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    },
                ],
            }),
        }
    }

    #[test]
    fn test_rx_txn_adds_default_metadata() {
        let plugin = RxTxnPlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction(vec!["rx_txn"], vec![])],
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

        if let DirectiveData::Transaction(txn) = &directives[0].data {
            let has_final = txn.metadata.iter().any(|(k, _)| k == "final");
            let has_roll = txn.metadata.iter().any(|(k, _)| k == "roll");
            assert!(has_final, "Should have 'final' metadata");
            assert!(has_roll, "Should have 'roll' metadata");
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_rx_txn_preserves_existing_metadata() {
        let plugin = RxTxnPlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction(
                vec!["rx_txn"],
                vec![("final", "2024-12-31"), ("roll", "False")],
            )],
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

        if let DirectiveData::Transaction(txn) = &directives[0].data {
            // Should only have 2 metadata items (the original ones)
            assert_eq!(txn.metadata.len(), 2);
            let final_meta = txn.metadata.iter().find(|(k, _)| k == "final").unwrap();
            if let MetaValueData::String(v) = &final_meta.1 {
                assert_eq!(v, "2024-12-31");
            } else {
                panic!("Expected string metadata value");
            }
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_rx_txn_ignores_untagged_transactions() {
        let plugin = RxTxnPlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction(vec![], vec![])],
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

        if let DirectiveData::Transaction(txn) = &directives[0].data {
            // Should have no metadata added
            assert!(txn.metadata.is_empty());
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_rx_txn_ignores_other_tags() {
        let plugin = RxTxnPlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction(vec!["other_tag"], vec![])],
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

        if let DirectiveData::Transaction(txn) = &directives[0].data {
            // Should have no metadata added
            assert!(txn.metadata.is_empty());
        } else {
            panic!("Expected transaction");
        }
    }
}
