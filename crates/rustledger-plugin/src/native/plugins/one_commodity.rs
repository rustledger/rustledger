//! Enforce single commodity per account.
//!
//! As beancount's `onecommodity` (#2539): an account's units (from
//! postings and `balance` assertions) in more than one currency are an
//! error, and so are its costs in more than one currency, each located at
//! the last entry that added a currency once there were two. Skipped: an
//! account whose `open` lists more than one currency, one whose `open` has
//! `onecommodity: FALSE`, and, when the config holds a regular expression,
//! one it does not match at the start. Before, the config, the opt-out,
//! costs and balances were ignored, and every further posting was
//! reported again.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::types::{
    DirectiveData, DirectiveWrapper, PluginError, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::{at_entry, falsy, python_match, python_match_regex};

/// Plugin that enforces single commodity per account.
pub struct OneCommodityPlugin;

/// Currencies seen per account, in first-seen account order, with the
/// entry to locate an error at.
#[derive(Default)]
struct Seen<'a> {
    order: Vec<&'a str>,
    currencies: HashMap<&'a str, BTreeSet<&'a str>>,
    source: HashMap<&'a str, &'a DirectiveWrapper>,
}

impl<'a> Seen<'a> {
    fn add(&mut self, account: &'a str, currency: &'a str, wrapper: &'a DirectiveWrapper) {
        let currencies = self.currencies.entry(account).or_insert_with(|| {
            self.order.push(account);
            BTreeSet::new()
        });
        currencies.insert(currency);
        if currencies.len() > 1 {
            self.source.insert(account, wrapper);
        }
    }

    fn errors(&self, what: &str, skip: &HashSet<&str>, errors: &mut Vec<PluginError>) {
        for account in &self.order {
            let currencies = &self.currencies[account];
            if skip.contains(account) || currencies.len() < 2 {
                continue;
            }
            // Sorted: beancount joins a set, whose order varies from run to
            // run.
            let joined = currencies.iter().copied().collect::<Vec<_>>().join(",");
            errors.push(at_entry(
                PluginError::error(format!(
                    "More than one {what} in account '{account}': {joined}"
                )),
                self.source[account],
            ));
        }
    }
}

impl NativePlugin for OneCommodityPlugin {
    fn name(&self) -> &'static str {
        "onecommodity"
    }

    fn description(&self) -> &'static str {
        "Enforce single commodity per account"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();
        let accounts_re = match input.config.as_deref().filter(|c| !c.is_empty()) {
            None => None,
            Some(pattern) => match python_match_regex(pattern) {
                Ok(re) => Some(re),
                Err(e) => {
                    return PluginOutput {
                        ops,
                        errors: vec![PluginError::error(format!(
                            "Invalid regular expression for onecommodity: '{pattern}': {e}"
                        ))],
                    };
                }
            },
        };

        let mut skip: HashSet<&str> = HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Open(open) = &wrapper.data {
                let opted_out = open
                    .metadata
                    .iter()
                    .any(|(k, v)| k == "onecommodity" && falsy(v));
                let unmatched = accounts_re
                    .as_ref()
                    .is_some_and(|re| !python_match(re, &open.account));
                if opted_out || unmatched || open.currencies.len() > 1 {
                    skip.insert(&open.account);
                }
            }
        }

        let mut units = Seen::default();
        let mut costs = Seen::default();
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        let account = posting.account.as_str();
                        if skip.contains(account) {
                            continue;
                        }
                        if let Some(amount) = &posting.units {
                            units.add(account, &amount.currency, wrapper);
                        }
                        if let Some(currency) =
                            posting.cost.as_ref().and_then(|c| c.currency.as_ref())
                        {
                            costs.add(account, currency, wrapper);
                        }
                    }
                }
                DirectiveData::Balance(bal) if !skip.contains(bal.account.as_str()) => {
                    units.add(&bal.account, &bal.amount.currency, wrapper);
                }
                _ => {}
            }
        }

        let mut errors = Vec::new();
        units.errors("currency", &skip, &mut errors);
        costs.errors("cost currency", &skip, &mut errors);
        PluginOutput { ops, errors }
    }
}

impl RegularPlugin for OneCommodityPlugin {}
