//! Plugin that automatically adds tags based on account patterns.

use crate::types::{DirectiveData, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that automatically adds tags based on account patterns.
///
/// This is an example plugin showing how to implement custom tagging logic.
/// It can be configured with rules like:
/// - "Expenses:Food" -> #food
/// - "Expenses:Travel" -> #travel
/// - "Assets:Bank" -> #banking
pub struct AutoTagPlugin {
    /// Rules mapping account prefixes to tags.
    rules: Vec<(String, String)>,
}

impl AutoTagPlugin {
    /// Create with default rules.
    pub fn new() -> Self {
        Self {
            rules: vec![
                ("Expenses:Food".to_string(), "food".to_string()),
                ("Expenses:Travel".to_string(), "travel".to_string()),
                ("Expenses:Transport".to_string(), "transport".to_string()),
                ("Income:Salary".to_string(), "income".to_string()),
            ],
        }
    }

    /// Create with custom rules.
    pub const fn with_rules(rules: Vec<(String, String)>) -> Self {
        Self { rules }
    }
}

impl Default for AutoTagPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for AutoTagPlugin {
    fn name(&self) -> &'static str {
        "auto_tag"
    }

    fn description(&self) -> &'static str {
        "Auto-tag transactions by account patterns"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut ops = Vec::with_capacity(input.directives.len());
        for (i, wrapper) in input.directives.into_iter().enumerate() {
            // Only transactions can be transformed; other directives pass through.
            if let DirectiveData::Transaction(ref txn) = wrapper.data {
                // Determine which tags would be added by the rules.
                let mut new_tags: Vec<String> = Vec::new();
                for posting in &txn.postings {
                    for (prefix, tag) in &self.rules {
                        if posting.account.starts_with(prefix)
                            && !txn.tags.contains(tag)
                            && !new_tags.contains(tag)
                        {
                            new_tags.push(tag.clone());
                        }
                    }
                }

                if new_tags.is_empty() {
                    ops.push(PluginOp::Keep(i));
                } else {
                    let mut modified = wrapper;
                    if let DirectiveData::Transaction(ref mut txn_mut) = modified.data {
                        txn_mut.tags.extend(new_tags);
                    }
                    ops.push(PluginOp::Modify(i, modified));
                }
            } else {
                ops.push(PluginOp::Keep(i));
            }
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

    #[test]
    fn test_auto_tag_adds_tag() {
        let plugin = AutoTagPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Lunch".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Expenses:Food:Restaurants".to_string(),
                            units: Some(AmountData {
                                number: "25.00".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                        PostingData {
                            account: "Assets:Cash".to_string(),
                            units: Some(AmountData {
                                number: "-25.00".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                    ],
                }),
            }],
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
            assert!(txn.tags.contains(&"food".to_string()));
        } else {
            panic!("Expected transaction");
        }
    }
}
