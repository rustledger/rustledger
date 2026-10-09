//! Error on postings to non-leaf accounts.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};

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

        // Every account the ledger names, as beancount's realization does:
        // posted to, or named by an open, close, balance, pad, note or
        // document. An account whose child is only opened is a parent all
        // the same (#2500 review: counting only posted accounts missed it,
        // where bean-check reports it).
        fn add_ancestors<'a>(parents: &mut HashSet<&'a str>, account: &'a str) {
            let mut end = account.len();
            while let Some(colon) = account[..end].rfind(':') {
                if !parents.insert(&account[..colon]) {
                    break; // its ancestors are in already
                }
                end = colon;
            }
        }
        let mut parent_accounts: HashSet<&str> = HashSet::new();
        for wrapper in &input.directives {
            let accounts: &[&String] = match &wrapper.data {
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        add_ancestors(&mut parent_accounts, &posting.account);
                    }
                    &[]
                }
                DirectiveData::Open(d) => &[&d.account],
                DirectiveData::Close(d) => &[&d.account],
                DirectiveData::Balance(d) => &[&d.account],
                DirectiveData::Note(d) => &[&d.account],
                DirectiveData::Document(d) => &[&d.account],
                DirectiveData::Pad(d) => &[&d.account, &d.source_account],
                _ => &[],
            };
            for account in accounts {
                add_ancestors(&mut parent_accounts, account);
            }
        }

        // Check for postings to parent accounts
        let mut errors = Vec::new();
        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if parent_accounts.contains(posting.account.as_str()) {
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

impl RegularPlugin for LeafOnlyPlugin {}
