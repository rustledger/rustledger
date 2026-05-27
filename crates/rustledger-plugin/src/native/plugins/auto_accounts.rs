//! Auto-generate Open directives for accounts used without explicit open.

use crate::types::{
    DirectiveData, DirectiveWrapper, OpenData, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, SynthPlugin};

/// Plugin that auto-generates Open directives for accounts used without explicit open.
pub struct AutoAccountsPlugin;

/// Name used by the registry, the loader (when emitting the implicit
/// synth-pass entry for `options.auto_accounts`), and external callers.
/// Kept as a constant so the three sites stay in sync.
pub const AUTO_ACCOUNTS_NAME: &str = "auto_accounts";

impl NativePlugin for AutoAccountsPlugin {
    fn name(&self) -> &'static str {
        AUTO_ACCOUNTS_NAME
    }

    fn description(&self) -> &'static str {
        "Auto-generate Open directives for used accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::{HashMap, HashSet};

        let mut opened_accounts: HashSet<String> = HashSet::new();
        let mut account_first_use: HashMap<String, String> = HashMap::new(); // account -> earliest date

        // First pass: find all open directives and EARLIEST use of each account
        // (directives may not be in date order in the input)
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Open(data) => {
                    opened_accounts.insert(data.account.clone());
                }
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        account_first_use
                            .entry(posting.account.clone())
                            .and_modify(|existing| {
                                if wrapper.date < *existing {
                                    existing.clone_from(&wrapper.date);
                                }
                            })
                            .or_insert_with(|| wrapper.date.clone());
                    }
                }
                DirectiveData::Balance(data) => {
                    account_first_use
                        .entry(data.account.clone())
                        .and_modify(|existing| {
                            if wrapper.date < *existing {
                                existing.clone_from(&wrapper.date);
                            }
                        })
                        .or_insert_with(|| wrapper.date.clone());
                }
                DirectiveData::Pad(data) => {
                    account_first_use
                        .entry(data.account.clone())
                        .and_modify(|existing| {
                            if wrapper.date < *existing {
                                existing.clone_from(&wrapper.date);
                            }
                        })
                        .or_insert_with(|| wrapper.date.clone());
                    account_first_use
                        .entry(data.source_account.clone())
                        .and_modify(|existing| {
                            if wrapper.date < *existing {
                                existing.clone_from(&wrapper.date);
                            }
                        })
                        .or_insert_with(|| wrapper.date.clone());
                }
                _ => {}
            }
        }

        // Generate open directives for accounts without explicit open
        // Sort accounts for deterministic ordering (matches Python beancount behavior)
        let mut accounts_to_open: Vec<_> = account_first_use
            .iter()
            .filter(|(account, _)| !opened_accounts.contains(*account))
            .collect();
        accounts_to_open.sort_by_key(|(account, _)| *account);

        // Start with Keep ops for every input directive (preserves spans).
        let mut ops: Vec<PluginOp> = (0..input.directives.len()).map(PluginOp::Keep).collect();

        // Insert synthesized Open directives for accounts without explicit open.
        for (index, (account, date)) in accounts_to_open.into_iter().enumerate() {
            ops.push(PluginOp::Insert(DirectiveWrapper {
                directive_type: "open".to_string(),
                date: date.clone(),
                filename: Some("<auto_accounts>".to_string()),
                lineno: Some(index as u32), // Use index as lineno for deterministic sorting
                data: DirectiveData::Open(OpenData {
                    account: account.clone(),
                    currencies: vec![],
                    booking: None,
                    metadata: vec![],
                }),
            }));
        }

        // Final ordering is the loader's responsibility — it re-sorts
        // directives after the plugin pass.
        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

/// Synthesizes `Open` directives the early validator needs to see —
/// must run pre-booking to suppress spurious E1001 errors on accounts
/// the plugin will auto-create.
impl SynthPlugin for AutoAccountsPlugin {}
