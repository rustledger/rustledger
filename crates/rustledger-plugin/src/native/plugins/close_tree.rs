//! Close descendant accounts automatically.

use crate::types::{
    CloseData, DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput,
};

use super::super::NativePlugin;

/// Plugin that closes all descendant accounts when a parent account closes.
///
/// When an account like `Assets:Bank` is closed, this plugin also generates
/// close directives for all sub-accounts like `Assets:Bank:Checking`.
pub struct CloseTreePlugin;

impl NativePlugin for CloseTreePlugin {
    fn name(&self) -> &'static str {
        "close_tree"
    }

    fn description(&self) -> &'static str {
        "Close descendant accounts automatically"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        // Collect all accounts that are used
        let mut all_accounts: HashSet<String> = HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Open(data) = &wrapper.data {
                all_accounts.insert(data.account.clone());
            }
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    all_accounts.insert(posting.account.clone());
                }
            }
        }

        // Collect accounts that are explicitly closed
        let mut closed_parents: Vec<(String, String)> = Vec::new(); // (account, date)
        for wrapper in &input.directives {
            if let DirectiveData::Close(data) = &wrapper.data {
                closed_parents.push((data.account.clone(), wrapper.date.clone()));
            }
        }

        // Collect accounts that are already closed in input.
        let mut already_closed: HashSet<String> = HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Close(data) = &wrapper.data {
                already_closed.insert(data.account.clone());
            }
        }

        // Start with Keep ops for every input directive.
        let mut ops: Vec<PluginOp> = (0..input.directives.len()).map(PluginOp::Keep).collect();

        // Track close directives we will insert so the same descendant
        // doesn't get inserted twice when multiple parent prefixes apply.
        let mut inserted_closes: HashSet<String> = HashSet::new();

        for (parent, close_date) in &closed_parents {
            let prefix = format!("{parent}:");
            for account in &all_accounts {
                if account.starts_with(&prefix)
                    && !already_closed.contains(account)
                    && !inserted_closes.contains(account)
                {
                    inserted_closes.insert(account.clone());
                    ops.push(PluginOp::Insert(DirectiveWrapper {
                        directive_type: "close".to_string(),
                        date: close_date.clone(),
                        filename: None, // Plugin-generated
                        lineno: None,
                        data: DirectiveData::Close(CloseData {
                            account: account.clone(),
                            metadata: vec![],
                        }),
                    }));
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
