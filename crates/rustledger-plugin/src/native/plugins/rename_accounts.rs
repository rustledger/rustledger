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
//! The configuration is a Python dict where keys are regex patterns and
//! values are replacement strings, as Python's `re.sub` takes them: every
//! match of a pattern anywhere in an account name is replaced, and the
//! replacement refers to groups as `\1` or `\g<name>` (`$1` is literal text).

use regex::Regex;

use crate::types::{
    DirectiveData, DirectiveWrapper, PadData, PluginError, PluginInput, PluginOp, PluginOutput,
    PostingData,
};

use super::super::{NativePlugin, RegularPlugin};
use super::py_literal::{self, PyValue};
use super::py_regex;

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
                Err(message) => {
                    // A config the plugin cannot use renames nothing, and
                    // says why: beancount's plugin raises on one.
                    return PluginOutput {
                        ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                        errors: vec![PluginError::error(message)],
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

impl RegularPlugin for RenameAccountsPlugin {}

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

/// A rename rule: compiled regex and replacement string, the replacement in
/// `regex`'s syntax (translated from Python's by
/// [`py_regex::translate_replacement`]).
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

/// Parse configuration string into rename rules, as upstream reads it:
/// `literal_eval` (so a repeated pattern keeps its first position and takes
/// its last replacement), `re.compile` on each pattern, and `re.subn` with
/// each replacement.
/// Format: "{'pattern1': 'replacement1', 'pattern2': 'replacement2'}"
fn parse_config(config: &str) -> Result<Vec<RenameRule>, String> {
    let invalid = |why: &str| format!("Invalid configuration for rename_accounts: {why}");
    let Ok(PyValue::Dict(entries)) = py_literal::parse(config) else {
        return Err(invalid("expected a dict of pattern to replacement"));
    };
    let mut merged: Vec<(String, String)> = Vec::with_capacity(entries.len());
    for (key, value) in entries {
        let (PyValue::Str(pattern), PyValue::Str(replacement)) = (key, value) else {
            return Err(invalid("patterns and replacements must be strings"));
        };
        if let Some(entry) = merged.iter_mut().find(|(p, _)| *p == pattern) {
            entry.1 = replacement;
        } else {
            merged.push((pattern, replacement));
        }
    }

    let mut rules = Vec::with_capacity(merged.len());
    for (pattern_str, replacement) in merged {
        let pattern = py_regex::compile_search(&pattern_str).map_err(|e| {
            format!("rename_accounts: the pattern '{pattern_str}' cannot be used: {e}")
        })?;
        let replacement = py_regex::translate_replacement(&replacement, &pattern).map_err(|e| {
            format!(
                "rename_accounts: the replacement '{replacement}' for '{pattern_str}' cannot be used: {e}"
            )
        })?;
        rules.push(RenameRule {
            pattern,
            replacement,
        });
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
                        span: None,
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
                ..Default::default()
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
                ..Default::default()
            },
            // Rename all Food sub-accounts to Dining. The replacement is
            // Python's `re.sub` syntax: `\1` is group 1 (the Python literal
            // `'\\1'` is the two characters `\1`).
            config: Some(r"{'Expenses:Food:(.*)': 'Expenses:Dining:\\1'}".to_string()),
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
                ..Default::default()
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
