//! Error on postings to non-leaf accounts.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that errors when posting to non-leaf (parent) accounts.
pub struct LeafOnlyPlugin;

impl NativePlugin for LeafOnlyPlugin {
    fn name(&self) -> &'static str {
        "leafonly"
    }

    fn description(&self) -> &'static str {
        "Error on postings to non-leaf accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        // Collect all accounts used
        let mut all_accounts: HashSet<String> = HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    all_accounts.insert(posting.account.clone());
                }
            }
        }

        // Find parent accounts (accounts that are prefixes of others)
        let parent_accounts: HashSet<&String> = all_accounts
            .iter()
            .filter(|acc| {
                all_accounts
                    .iter()
                    .any(|other| other != *acc && other.starts_with(&format!("{acc}:")))
            })
            .collect();

        // Check for postings to parent accounts
        let mut errors = Vec::new();
        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if parent_accounts.contains(&posting.account) {
                        errors.push(PluginError::error(format!(
                            "Posting to non-leaf account '{}' - has child accounts",
                            posting.account
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
