//! Rename accounts plugin.
//!
//! This plugin renames accounts using regex patterns. It takes a configuration
//! dict mapping regex patterns to replacement strings.
//!
//! Usage:
//! ```beancount
//! plugin "beancount_reds_plugins.rename_accounts.rename_accounts" "{'Expenses:Taxes': 'Income:Taxes'}"
//! ```
//!
//! The configuration is a Python-style dict where keys are regex patterns and
//! values are replacement strings. All accounts matching a pattern will be
//! renamed using the corresponding replacement.

use regex::Regex;
use std::sync::LazyLock;

use crate::types::{
    DirectiveData, DirectiveWrapper, PadData, PluginInput, PluginOp, PluginOutput, PostingData,
};

use super::super::NativePlugin;

/// Regex for parsing config key-value pairs.
/// Format: `'pattern': 'replacement'`
static CONFIG_KV_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"'([^']+)'\s*:\s*'([^']*)'").expect("CONFIG_KV_RE: invalid regex pattern")
});

/// Plugin for renaming accounts using regex patterns.
pub struct RenameAccountsPlugin;

impl NativePlugin for RenameAccountsPlugin {
    fn name(&self) -> &'static str {
        "rename_accounts"
    }

    fn description(&self) -> &'static str {
        "Rename accounts using regex patterns"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Parse configuration to get renames
        let renames = match &input.config {
            Some(config) => match parse_config(config) {
                Ok(r) => r,
                Err(_) => {
                    // If config parsing fails, return unchanged
                    return PluginOutput {
                        ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                        errors: Vec::new(),
                    };
                }
            },
            None => {
                // No config, return unchanged
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors: Vec::new(),
                };
            }
        };

        // Process entries — emit Modify when an account name changed,
        // Keep otherwise. We compare before/after rename to avoid emitting
        // a Modify wrapper for directives the rename rules didn't touch.
        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());
        for (i, directive) in input.directives.iter().enumerate() {
            let renamed = rename_in_directive(directive.clone(), &renames);
            if directive_has_same_accounts(directive, &renamed) {
                ops.push(PluginOp::Keep(i));
            } else {
                ops.push(PluginOp::Modify(i, renamed));
            }
        }

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

/// Cheap structural check — only compares the account name fields the
/// rename plugin can touch. Avoids a full `PartialEq` requirement and
/// keeps the check tight to what changed.
fn directive_has_same_accounts(a: &DirectiveWrapper, b: &DirectiveWrapper) -> bool {
    match (&a.data, &b.data) {
        (DirectiveData::Transaction(ta), DirectiveData::Transaction(tb)) => {
            ta.postings.len() == tb.postings.len()
                && ta
                    .postings
                    .iter()
                    .zip(tb.postings.iter())
                    .all(|(pa, pb)| pa.account == pb.account)
        }
        (DirectiveData::Open(a), DirectiveData::Open(b)) => a.account == b.account,
        (DirectiveData::Close(a), DirectiveData::Close(b)) => a.account == b.account,
        (DirectiveData::Balance(a), DirectiveData::Balance(b)) => a.account == b.account,
        (DirectiveData::Pad(a), DirectiveData::Pad(b)) => {
            a.account == b.account && a.source_account == b.source_account
        }
        (DirectiveData::Note(a), DirectiveData::Note(b)) => a.account == b.account,
        (DirectiveData::Document(a), DirectiveData::Document(b)) => a.account == b.account,
        // Other directive types don't carry account references.
        _ => true,
    }
}

/// A rename rule: compiled regex and replacement string.
struct RenameRule {
    pattern: Regex,
    replacement: String,
}

/// Apply renames to an account name.
fn rename_account(account: &str, renames: &[RenameRule]) -> String {
    let mut result = account.to_string();
    for rule in renames {
        if rule.pattern.is_match(&result) {
            result = rule
                .pattern
                .replace_all(&result, &rule.replacement)
                .to_string();
        }
    }
    result
}

/// Apply renames to a posting.
fn rename_in_posting(mut posting: PostingData, renames: &[RenameRule]) -> PostingData {
    posting.account = rename_account(&posting.account, renames);
    posting
}

/// Apply renames to a directive.
fn rename_in_directive(
    mut directive: DirectiveWrapper,
    renames: &[RenameRule],
) -> DirectiveWrapper {
    match &mut directive.data {
        DirectiveData::Transaction(txn) => {
            txn.postings = txn
                .postings
                .drain(..)
                .map(|p| rename_in_posting(p, renames))
                .collect();
        }
        DirectiveData::Open(open) => {
            open.account = rename_account(&open.account, renames);
        }
        DirectiveData::Close(close) => {
            close.account = rename_account(&close.account, renames);
        }
        DirectiveData::Balance(balance) => {
            balance.account = rename_account(&balance.account, renames);
        }
        DirectiveData::Pad(pad) => {
            let account = rename_account(&pad.account, renames);
            let source_account = rename_account(&pad.source_account, renames);
            *pad = PadData {
                account,
                source_account,
                metadata: std::mem::take(&mut pad.metadata),
            };
        }
        DirectiveData::Note(note) => {
            note.account = rename_account(&note.account, renames);
        }
        DirectiveData::Document(doc) => {
            doc.account = rename_account(&doc.account, renames);
        }
        // Price, Commodity, Event, Query, Custom don't have accounts
        DirectiveData::Price(_)
        | DirectiveData::Commodity(_)
        | DirectiveData::Event(_)
        | DirectiveData::Query(_)
        | DirectiveData::Custom(_) => {}
    }
    directive
}

/// Parse configuration string into rename rules.
/// Format: "{'pattern1': 'replacement1', 'pattern2': 'replacement2'}"
fn parse_config(config: &str) -> Result<Vec<RenameRule>, String> {
    let mut rules = Vec::new();

    // Parse Python-style dict: {'key': 'value', ...}
    // Use cached regex to extract key-value pairs
    for cap in CONFIG_KV_RE.captures_iter(config) {
        let pattern_str = &cap[1];
        let replacement = cap[2].to_string();

        let pattern = Regex::new(pattern_str).map_err(|e| e.to_string())?;

        rules.push(RenameRule {
            pattern,
            replacement,
        });
    }

    if rules.is_empty() {
        return Err("No rename rules found in config".to_string());
    }

    Ok(rules)
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_open(account: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "open".to_string(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Open(OpenData {
                account: account.to_string(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        }
    }

    fn create_transaction(postings: Vec<(&str, &str, &str)>) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Test".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: postings
                    .into_iter()
                    .map(|(account, number, currency)| PostingData {
                        account: account.to_string(),
                        units: Some(AmountData {
                            number: number.to_string(),
                            currency: currency.to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    })
                    .collect(),
            }),
        }
    }

    #[test]
    fn test_simple_rename() {
        let plugin = RenameAccountsPlugin;

        let input = PluginInput {
            directives: vec![
                create_open("Expenses:Taxes"),
                create_transaction(vec![
                    ("Assets:Cash", "-100", "USD"),
                    ("Expenses:Taxes", "100", "USD"),
                ]),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'Expenses:Taxes': 'Income:Taxes'}".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Check Open directive was renamed
        if let DirectiveData::Open(open) = &directives[0].data {
            assert_eq!(open.account, "Income:Taxes");
        } else {
            panic!("Expected Open directive");
        }

        // Check Transaction posting was renamed
        if let DirectiveData::Transaction(txn) = &directives[1].data {
            assert_eq!(txn.postings[1].account, "Income:Taxes");
        } else {
            panic!("Expected Transaction directive");
        }
    }

    #[test]
    fn test_regex_rename() {
        let plugin = RenameAccountsPlugin;

        let input = PluginInput {
            directives: vec![
                create_open("Expenses:Food:Groceries"),
                create_open("Expenses:Food:Restaurant"),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            // Rename all Food sub-accounts to Dining
            // In Rust regex, backreferences use $1 syntax
            config: Some("{'Expenses:Food:(.*)': 'Expenses:Dining:$1'}".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        if let DirectiveData::Open(open) = &directives[0].data {
            assert_eq!(open.account, "Expenses:Dining:Groceries");
        }

        if let DirectiveData::Open(open) = &directives[1].data {
            assert_eq!(open.account, "Expenses:Dining:Restaurant");
        }
    }

    #[test]
    fn test_no_config_unchanged() {
        let plugin = RenameAccountsPlugin;

        let input = PluginInput {
            directives: vec![create_open("Expenses:Taxes")],
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

        if let DirectiveData::Open(open) = &directives[0].data {
            assert_eq!(open.account, "Expenses:Taxes");
        }
    }
}
