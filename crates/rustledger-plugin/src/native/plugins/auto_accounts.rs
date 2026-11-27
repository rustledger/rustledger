//! Auto-generate Open directives for accounts used without explicit open.

use crate::types::{
    BalanceData, CloseData, DirectiveData, DirectiveWrapper, DocumentData, NoteData, OpenData,
    PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin that auto-generates Open directives for accounts used without explicit open.
pub struct AutoAccountsPlugin;

/// Name used by the registry, the loader (for `options.auto_accounts`, and
/// for the provisional opens its Early validation reads), and external
/// callers.
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
                    // Named, as beancount's `get_accounts_use_map` counts an
                    // `open`: it takes a place in the numbering below.
                    account_first_use
                        .entry(data.account.clone())
                        .or_insert_with(|| wrapper.date.clone());
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
                // Every directive naming one account, as beancount's
                // `getters.get_accounts_use_map` counts them: a `note`,
                // `document` or `close` on an account nothing else names
                // opened it there; here it was left unopened (E1001, #2600).
                DirectiveData::Balance(BalanceData { account, .. })
                | DirectiveData::Note(NoteData { account, .. })
                | DirectiveData::Document(DocumentData { account, .. })
                | DirectiveData::Close(CloseData { account, .. }) => {
                    account_first_use
                        .entry(account.clone())
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

        // Generate open directives for accounts without explicit open, in
        // sorted order. Each is numbered by the account's place among ALL
        // the accounts the ledger names, opened ones included, as
        // beancount's `enumerate(sorted(accounts_first.items()))` numbers
        // it: the number is its `lineno`, which beancount's entry order reads
        // (#2901).
        let mut accounts: Vec<_> = account_first_use.iter().collect();
        accounts.sort_by_key(|(account, _)| *account);
        let accounts_to_open = accounts
            .into_iter()
            .enumerate()
            .filter(|(_, (account, _))| !opened_accounts.contains(*account));

        // Start with Keep ops for every input directive (preserves spans).
        let mut ops: Vec<PluginOp> = (0..input.directives.len()).map(PluginOp::Keep).collect();

        // Insert synthesized Open directives for accounts without explicit open.
        for (index, (account, date)) in accounts_to_open {
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

/// A regular plugin, run where it is declared, after booking, as beancount
/// runs it: a plugin declared before it does not see the accounts it opens
/// (`close_tree` drops the `close` of an account nothing opened before it
/// runs), and it opens nothing for a transaction booking refused, which is
/// no longer in the stream. It used to run in the pre-booking synth pass,
/// ahead of every other plugin whatever the declared order.
///
/// The Early validator's provisional account table still needs its opens
/// (a posting to an account it will open is not "never opened"): the loader
/// gives Early a view with them, `rustledger_loader::early_validation_view`,
/// which nothing downstream sees.
impl RegularPlugin for AutoAccountsPlugin {}
