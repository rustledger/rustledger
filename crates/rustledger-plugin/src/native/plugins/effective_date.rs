//! Effective date plugin - move postings to their effective dates.
//!
//! When a posting has an `effective_date` metadata, this plugin:
//! 1. Moves the original posting to a holding account on the transaction date
//! 2. Creates a new transaction on the effective date
//!
//! Configuration (optional):
//! ```text
//! plugin "beancount_reds_plugins.effective_date.effective_date" "{
//!   'Expenses': {'earlier': 'Liabilities:Hold:Expenses', 'later': 'Assets:Hold:Expenses'},
//!   'Income': {'earlier': 'Assets:Hold:Income', 'later': 'Liabilities:Hold:Income'},
//! }"
//! ```

use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::sync::LazyLock;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Regex for parsing holding account configuration entries.
/// Format: `'Prefix': {'earlier': 'Account1', 'later': 'Account2'}`
static HOLDING_ACCOUNT_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"'([^']+)'\s*:\s*\{\s*'earlier'\s*:\s*'([^']+)'\s*,\s*'later'\s*:\s*'([^']+)'\s*\}")
        .expect("HOLDING_ACCOUNT_RE: invalid regex pattern")
});

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, MetaValueData, OpenData, PluginInput, PluginOp,
    PluginOutput, PostingData, TransactionData,
};

use super::super::NativePlugin;

/// Plugin for handling effective dates on postings.
pub struct EffectiveDatePlugin;

/// Default holding accounts configuration.
fn default_holding_accounts() -> HashMap<String, (String, String)> {
    let mut map = HashMap::new();
    map.insert(
        "Expenses".to_string(),
        (
            "Liabilities:Hold:Expenses".to_string(),
            "Assets:Hold:Expenses".to_string(),
        ),
    );
    map.insert(
        "Income".to_string(),
        (
            "Assets:Hold:Income".to_string(),
            "Liabilities:Hold:Income".to_string(),
        ),
    );
    map
}

impl NativePlugin for EffectiveDatePlugin {
    fn name(&self) -> &'static str {
        "effective_date"
    }

    fn description(&self) -> &'static str {
        "Move postings to their effective dates using holding accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Parse configuration or use defaults
        let holding_accounts = match &input.config {
            Some(config) => parse_config(config).unwrap_or_else(|_| default_holding_accounts()),
            None => default_holding_accounts(),
        };

        let mut new_accounts: HashSet<String> = HashSet::new();
        let mut earliest_date: Option<String> = None;
        // Accounts already opened by the user; suppress duplicate Opens
        // for holding accounts the user has pre-declared (else Late
        // validation emits E1002 AccountAlreadyOpen). Mirrors the
        // pattern in `zerosum`, `currency_accounts`, `split_expenses`,
        // and `capital_gains_classifier`.
        let mut existing_opens: HashSet<String> = HashSet::new();

        // Compute earliest date AND record existing opens in one pass.
        for directive in &input.directives {
            if earliest_date.is_none() || directive.date < *earliest_date.as_ref().unwrap() {
                earliest_date = Some(directive.date.clone());
            }
            if let DirectiveData::Open(open) = &directive.data {
                existing_opens.insert(open.account.clone());
            }
        }

        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());
        // Inserted new transactions (one per posting with effective_date),
        // accumulated into ops after the main loop so the Modify(i, ...)
        // entries stay paired with their input indices in input-order.
        let mut inserted_txns: Vec<DirectiveWrapper> = Vec::new();

        for (i, mut directive) in input.directives.into_iter().enumerate() {
            let is_interesting = matches!(&directive.data, DirectiveData::Transaction(t) if has_effective_date_posting(t));
            if !is_interesting {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            // Generate a random link for this set of entries
            let link = generate_link(&directive.date);

            if let DirectiveData::Transaction(ref mut txn) = directive.data {
                // Add link to original transaction
                if !txn.links.contains(&link) {
                    txn.links.push(link.clone());
                }

                let entry_date = directive.date.clone();
                let mut modified_postings = Vec::new();

                for posting in &txn.postings {
                    if let Some(effective_date) = get_effective_date(posting) {
                        // Find the holding account for this posting's account type
                        let (hold_account, _is_later) = find_holding_account(
                            &posting.account,
                            &effective_date,
                            &entry_date,
                            &holding_accounts,
                        );

                        if let Some(hold_acct) = hold_account {
                            // Create modified posting with holding account
                            let new_account = posting.account.replace(
                                &find_account_prefix(&posting.account, &holding_accounts),
                                &hold_acct,
                            );
                            new_accounts.insert(new_account.clone());

                            let mut modified_posting = posting.clone();
                            modified_posting.account.clone_from(&new_account);
                            // Remove effective_date from metadata
                            modified_posting
                                .metadata
                                .retain(|(k, _)| k != "effective_date");

                            // Create hold posting (opposite of modified) before moving
                            let hold_posting = create_opposite_posting(&modified_posting);

                            modified_postings.push(modified_posting);

                            // Create new entry at effective date
                            let mut cleaned_original = posting.clone();
                            cleaned_original
                                .metadata
                                .retain(|(k, _)| k != "effective_date");

                            let new_txn = TransactionData {
                                flag: txn.flag.clone(),
                                payee: txn.payee.clone(),
                                narration: txn.narration.clone(),
                                tags: txn.tags.clone(),
                                links: vec![link.clone()],
                                metadata: vec![(
                                    "original_date".to_string(),
                                    MetaValueData::Date(entry_date.clone()),
                                )],
                                postings: vec![hold_posting, cleaned_original],
                            };

                            inserted_txns.push(DirectiveWrapper {
                                directive_type: "transaction".to_string(),
                                date: effective_date,
                                filename: directive.filename.clone(),
                                lineno: directive.lineno,
                                data: DirectiveData::Transaction(new_txn),
                            });
                        } else {
                            // No matching holding account, keep original
                            modified_postings.push(posting.clone());
                        }
                    } else {
                        // No effective_date, keep original
                        modified_postings.push(posting.clone());
                    }
                }

                txn.postings = modified_postings;
            }

            ops.push(PluginOp::Modify(i, directive));
        }

        // Append all inserted new-date transactions.
        for w in inserted_txns {
            ops.push(PluginOp::Insert(w));
        }

        // Insert Open directives for newly synthesized holding accounts
        // the user hasn't already opened.
        if let Some(date) = &earliest_date {
            for account in &new_accounts {
                if existing_opens.contains(account) {
                    continue;
                }
                ops.push(PluginOp::Insert(DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: date.clone(),
                    filename: Some("<effective_date>".to_string()),
                    lineno: Some(0),
                    data: DirectiveData::Open(OpenData {
                        account: account.clone(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                }));
            }
        }

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

/// Check if a transaction has any posting with `effective_date` metadata.
fn has_effective_date_posting(txn: &TransactionData) -> bool {
    txn.postings.iter().any(|p| {
        p.metadata
            .iter()
            .any(|(k, v)| k == "effective_date" && matches!(v, MetaValueData::Date(_)))
    })
}

/// Get the `effective_date` from a posting's metadata.
fn get_effective_date(posting: &PostingData) -> Option<String> {
    for (key, value) in &posting.metadata {
        if key == "effective_date"
            && let MetaValueData::Date(d) = value
        {
            return Some(d.clone());
        }
    }
    None
}

/// Find the appropriate holding account for a posting.
fn find_holding_account(
    account: &str,
    effective_date: &str,
    entry_date: &str,
    holding_accounts: &HashMap<String, (String, String)>,
) -> (Option<String>, bool) {
    for (prefix, (earlier, later)) in holding_accounts {
        if account.starts_with(prefix) {
            let is_later = effective_date > entry_date;
            let hold_acct = if is_later { later } else { earlier };
            return (Some(hold_acct.clone()), is_later);
        }
    }
    (None, false)
}

/// Find the account prefix that matches the holding accounts config.
fn find_account_prefix(
    account: &str,
    holding_accounts: &HashMap<String, (String, String)>,
) -> String {
    for prefix in holding_accounts.keys() {
        if account.starts_with(prefix) {
            return prefix.clone();
        }
    }
    String::new()
}

/// Create a posting with the opposite amount.
fn create_opposite_posting(posting: &PostingData) -> PostingData {
    let mut opposite = posting.clone();
    if let Some(ref units) = opposite.units {
        let number = if units.number.starts_with('-') {
            units.number[1..].to_string()
        } else {
            format!("-{}", units.number)
        };
        opposite.units = Some(AmountData {
            number,
            currency: units.currency.clone(),
        });
    }
    opposite
}

/// Counter for generating unique links.
static LINK_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Generate a unique link for effective date entries.
fn generate_link(date: &str) -> String {
    let date_short = date.replace('-', "");
    let date_short = if date_short.len() > 6 {
        &date_short[2..]
    } else {
        &date_short
    };
    let counter = LINK_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("edate-{}-{:03x}", date_short, counter % 4096)
}

/// Parse the configuration string.
fn parse_config(config: &str) -> Result<HashMap<String, (String, String)>, String> {
    let mut result = HashMap::new();

    // Parse format: {'Prefix': {'earlier': 'Account1', 'later': 'Account2'}, ...}
    for cap in HOLDING_ACCOUNT_RE.captures_iter(config) {
        let prefix = cap[1].to_string();
        let earlier = cap[2].to_string();
        let later = cap[3].to_string();
        result.insert(prefix, (earlier, later));
    }

    if result.is_empty() {
        return Err("No holding accounts found in config".to_string());
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_test_transaction_with_effective_date(
        date: &str,
        effective_date: &str,
    ) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Test with effective date".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
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
                        account: "Expenses:Food".to_string(),
                        units: Some(AmountData {
                            number: "100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![(
                            "effective_date".to_string(),
                            MetaValueData::Date(effective_date.to_string()),
                        )],
                    },
                ],
            }),
        }
    }

    #[test]
    fn test_effective_date_later() {
        let plugin = EffectiveDatePlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction_with_effective_date(
                "2024-01-15",
                "2024-02-01",
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

        // Should have: open directives + original modified + new at effective date
        assert!(directives.len() >= 2);

        // Check that we have a transaction at the effective date
        let effective_txn_count = directives
            .iter()
            .filter(|d| d.date == "2024-02-01" && matches!(d.data, DirectiveData::Transaction(_)))
            .count();
        assert_eq!(effective_txn_count, 1);
    }

    #[test]
    fn test_effective_date_earlier() {
        let plugin = EffectiveDatePlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction_with_effective_date(
                "2024-02-01",
                "2024-01-15",
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

        // Check that we have a transaction at the earlier effective date
        let effective_txn_count = directives
            .iter()
            .filter(|d| d.date == "2024-01-15" && matches!(d.data, DirectiveData::Transaction(_)))
            .count();
        assert_eq!(effective_txn_count, 1);
    }

    #[test]
    fn test_no_effective_date_unchanged() {
        let plugin = EffectiveDatePlugin;

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Regular transaction".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
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
                            account: "Expenses:Food".to_string(),
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
        // Should have exactly 1 transaction (unchanged)
        let txn_count = directives
            .iter()
            .filter(|d| matches!(d.data, DirectiveData::Transaction(_)))
            .count();
        assert_eq!(txn_count, 1);
    }
}
