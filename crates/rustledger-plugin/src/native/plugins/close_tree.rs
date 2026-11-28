//! Close descendant accounts automatically.

use crate::types::{
    CloseData, DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin that closes all descendant accounts when a parent account closes.
///
/// When an account like `Assets:Bank` is closed, this plugin also generates
/// close directives for all sub-accounts like `Assets:Bank:Checking`.
///
/// As beancount 3.2.3's `close_tree` does:
///
/// - the descendants it closes are the accounts an `open` directive opens,
///   not every account a posting names (a posting to an account never opened
///   is the validator's error, and closing it would add a second one);
/// - a `close` of an account that no `open` opens is dropped, after its
///   descendants are closed. Closing a parent that was never opened is how
///   the plugin is used to close a whole tree (`close Assets:Bank` with only
///   `Assets:Bank:Checking` opened), and kept, it was reported as closing an
///   account that was never opened (`E1001`), where `bean-check` reports
///   nothing.
pub struct CloseTreePlugin;

/// The location of each close the plugin inserts, line 0, as beancount's
/// `close_tree` gives it (#2713).
const CLOSE_TREE_LOCATION: &str = "<beancount.plugins.close_tree>";

impl NativePlugin for CloseTreePlugin {
    fn name(&self) -> &'static str {
        "close_tree"
    }

    fn description(&self) -> &'static str {
        "Close descendant accounts automatically"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::{BTreeSet, HashSet};

        // Collect the accounts an `open` opens: the only ones closed, and the
        // only ones whose own `close` is kept (see the type's docs). Sorted,
        // so the closes it inserts come out in the same order every run: a
        // `HashSet` here emitted them in hash order (#2625). Beancount's own
        // plugin walks a `set`, whose order varies from run to run, so there
        // is no order of its to match.
        let mut opened: BTreeSet<String> = BTreeSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Open(data) = &wrapper.data {
                opened.insert(data.account.clone());
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

        // Keep every input directive but the `close` of an account no `open`
        // opens.
        let mut ops: Vec<PluginOp> = input
            .directives
            .iter()
            .enumerate()
            .map(|(i, wrapper)| match &wrapper.data {
                DirectiveData::Close(data) if !opened.contains(&data.account) => {
                    PluginOp::Delete(i)
                }
                _ => PluginOp::Keep(i),
            })
            .collect();

        // Track close directives we will insert so the same descendant
        // doesn't get inserted twice when multiple parent prefixes apply.
        let mut inserted_closes: HashSet<String> = HashSet::new();

        for (parent, close_date) in &closed_parents {
            let prefix = format!("{parent}:");
            for account in &opened {
                if account.starts_with(&prefix)
                    && !already_closed.contains(account)
                    && !inserted_closes.contains(account)
                {
                    inserted_closes.insert(account.clone());
                    ops.push(PluginOp::Insert(DirectiveWrapper {
                        directive_type: "close".to_string(),
                        date: close_date.clone(),
                        // Beancount's placeholder location
                        // (`new_metadata("<beancount.plugins.close_tree>",
                        // 0)`), so an error on the close is reported there
                        // (#2713).
                        filename: Some(CLOSE_TREE_LOCATION.to_string()),
                        lineno: Some(0),
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

impl RegularPlugin for CloseTreePlugin {}
