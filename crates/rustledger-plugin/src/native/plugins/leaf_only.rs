//! Error on postings to non-leaf accounts.

use std::collections::{BTreeSet, HashMap};

use crate::types::{
    DirectiveData, DirectiveWrapper, PluginError, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::at_entry;

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

        // A parent account is reported once, at its `open`, when something
        // puts amounts on it: a posting, or a `pad` (its padding posts to
        // both accounts). As beancount's `leafonly` reports it (#2539):
        // before, every posting was reported, with no location.
        //
        // Deliberate divergence: beancount's realization also counts a
        // `note`, `document`, `close` or `custom` naming the account, so
        // bean-check reports "Non-leaf account ... has postings on it" for
        // a note on a parent account. None of those posts anything, so they
        // are not counted here (nor in the `python:leafonly` built-in,
        // `LEAFONLY_PLUGIN` in `python/runtime.rs`, which says the same).
        let mut posted: BTreeSet<Vec<&str>> = BTreeSet::new();
        let mut opens: HashMap<&str, &DirectiveWrapper> = HashMap::new();
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        if parent_accounts.contains(posting.account.as_str()) {
                            posted.insert(posting.account.split(':').collect());
                        }
                    }
                }
                DirectiveData::Pad(pad) => {
                    for account in [&pad.account, &pad.source_account] {
                        if parent_accounts.contains(account.as_str()) {
                            posted.insert(account.split(':').collect());
                        }
                    }
                }
                DirectiveData::Open(open) => {
                    opens.entry(open.account.as_str()).or_insert(wrapper);
                }
                _ => {}
            }
        }
        // In beancount's order: the account tree depth-first, children by
        // name, which is the order of the accounts' components.
        let errors = posted
            .into_iter()
            .map(|components| {
                let account = components.join(":");
                let error =
                    PluginError::error(format!("Non-leaf account '{account}' has postings on it"));
                match opens.get(account.as_str()) {
                    Some(open) => at_entry(error, open),
                    None => error,
                }
            })
            .collect();

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for LeafOnlyPlugin {}
