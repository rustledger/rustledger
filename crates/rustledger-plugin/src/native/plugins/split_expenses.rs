//! Split expenses between multiple people.
//!
//! This plugin splits expense postings between multiple members.
//! Any expense account that doesn't already contain a member's name
//! will be split into multiple postings, one per member.
//!
//! Configuration: Space-separated list of member names, e.g., "Martin Caroline"
//!
//! Example:
//! ```beancount
//! plugin "beancount.plugins.split_expenses" "Martin Caroline"
//!
//! 2015-02-01 * "Aqua Viva Tulum"
//!    Income:Caroline:CreditCard  -269.00 USD
//!    Expenses:Accommodation
//! ```
//!
//! Becomes:
//! ```beancount
//! 2015-02-01 * "Aqua Viva Tulum"
//!   Income:Caroline:CreditCard       -269.00 USD
//!   Expenses:Accommodation:Martin     134.50 USD
//!   Expenses:Accommodation:Caroline   134.50 USD
//! ```

use rust_decimal::Decimal;
use std::collections::HashSet;
use std::str::FromStr;

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, MetaValueData, OpenData, PluginInput, PluginOp,
    PluginOutput, PostingData,
};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin for splitting expenses between multiple people.
pub struct SplitExpensesPlugin;

impl NativePlugin for SplitExpensesPlugin {
    fn name(&self) -> &'static str {
        "split_expenses"
    }

    fn description(&self) -> &'static str {
        "Split expense postings between multiple members"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Parse configuration to get member names
        let members: Vec<String> = match &input.config {
            Some(config) => config.split_whitespace().map(String::from).collect(),
            None => {
                // No config provided, return unchanged
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors: Vec::new(),
                };
            }
        };

        if members.is_empty() {
            return PluginOutput {
                ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                errors: Vec::new(),
            };
        }

        let num_members = Decimal::from(members.len());
        let mut new_accounts: HashSet<String> = HashSet::new();
        let mut earliest_date: Option<String> = None;
        // Accounts already opened by the user; we must not synthesize
        // a duplicate Open for any of these or Late validation will
        // emit E1002 (AccountAlreadyOpen).
        let mut existing_opens: HashSet<String> = HashSet::new();

        // Compute earliest date AND record existing opens in one pass.
        for d in &input.directives {
            if earliest_date.as_ref().is_none_or(|e| d.date < *e) {
                earliest_date = Some(d.date.clone());
            }
            if let DirectiveData::Open(open) = &d.data {
                existing_opens.insert(open.account.clone());
            }
        }

        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());

        for (i, mut wrapper) in input.directives.into_iter().enumerate() {
            if wrapper.directive_type != "transaction" {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            let mut changed = false;
            if let DirectiveData::Transaction(ref mut txn) = wrapper.data {
                let mut new_postings = Vec::new();

                for posting in &txn.postings {
                    // Check if this is an expense account
                    let is_expense = posting.account.starts_with("Expenses:");

                    // Check if account already contains a member name
                    let has_member = members.iter().any(|m| posting.account.contains(m.as_str()));

                    if is_expense && !has_member {
                        // Split this posting among members
                        if let Some(ref units) = posting.units {
                            // Parse the amount
                            if let Ok(amount) = Decimal::from_str(&units.number) {
                                let split_amount = amount / num_members;

                                for member in &members {
                                    // Create subaccount with member name
                                    let subaccount = format!("{}:{}", posting.account, member);
                                    new_accounts.insert(subaccount.clone());

                                    // Create new posting for this member
                                    let mut new_metadata = posting.metadata.clone();
                                    // Mark as automatically calculated
                                    new_metadata.push((
                                        "__automatic__".to_string(),
                                        MetaValueData::String("True".to_string()),
                                    ));

                                    new_postings.push(PostingData {
                                        account: subaccount,
                                        units: Some(AmountData {
                                            number: split_amount.to_string(),
                                            currency: units.currency.clone(),
                                        }),
                                        cost: posting.cost.clone(),
                                        price: posting.price.clone(),
                                        flag: posting.flag.clone(),
                                        metadata: new_metadata,
                                        span: None,
                                    });
                                }
                                changed = true;
                            } else {
                                // Couldn't parse amount, keep original
                                new_postings.push(posting.clone());
                            }
                        } else {
                            // No units, keep original
                            new_postings.push(posting.clone());
                        }
                    } else {
                        // Keep posting as is
                        new_postings.push(posting.clone());
                    }
                }

                if changed {
                    txn.postings = new_postings;
                }
            }

            if changed {
                ops.push(PluginOp::Modify(i, wrapper));
            } else {
                ops.push(PluginOp::Keep(i));
            }
        }

        // Insert Open directives for newly synthesized member sub-accounts
        // that the user hasn't already opened.
        if let Some(date) = earliest_date {
            let mut accounts: Vec<String> = new_accounts
                .into_iter()
                .filter(|a| !existing_opens.contains(a))
                .collect();
            accounts.sort();
            for account in accounts {
                ops.push(PluginOp::Insert(DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: date.clone(),
                    filename: Some("<split_expenses>".to_string()),
                    lineno: Some(0),
                    data: DirectiveData::Open(OpenData {
                        account,
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

impl RegularPlugin for SplitExpensesPlugin {}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_test_transaction(postings: Vec<PostingData>) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: Some("Test".to_string()),
                narration: "Test transaction".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings,
            }),
        }
    }

    #[test]
    fn test_split_expenses_basic() {
        let plugin = SplitExpensesPlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction(vec![
                PostingData {
                    account: "Income:Caroline:CreditCard".to_string(),
                    units: Some(AmountData {
                        number: "-269.00".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Expenses:Accommodation".to_string(),
                    units: Some(AmountData {
                        number: "269.00".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ])],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("Martin Caroline".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Should have 2 open directives + 1 transaction
        assert_eq!(directives.len(), 3);

        // Find the transaction
        let txn = directives
            .iter()
            .find(|d| matches!(d.data, DirectiveData::Transaction(_)))
            .unwrap();

        if let DirectiveData::Transaction(txn_data) = &txn.data {
            // Should have 3 postings: 1 income (unchanged) + 2 expenses (split)
            assert_eq!(txn_data.postings.len(), 3);

            // Check the split postings
            let expense_postings: Vec<_> = txn_data
                .postings
                .iter()
                .filter(|p| p.account.starts_with("Expenses:"))
                .collect();

            assert_eq!(expense_postings.len(), 2);
            assert!(
                expense_postings
                    .iter()
                    .any(|p| p.account == "Expenses:Accommodation:Martin")
            );
            assert!(
                expense_postings
                    .iter()
                    .any(|p| p.account == "Expenses:Accommodation:Caroline")
            );

            // Each should have half the amount (134.50)
            for p in expense_postings {
                if let Some(units) = &p.units {
                    assert_eq!(units.number, "134.50");
                }
            }
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_split_expenses_preserves_member_accounts() {
        let plugin = SplitExpensesPlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction(vec![
                PostingData {
                    account: "Income:Martin:Cash".to_string(),
                    units: Some(AmountData {
                        number: "-100.00".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Expenses:Food:Martin".to_string(),
                    units: Some(AmountData {
                        number: "100.00".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ])],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("Martin Caroline".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);

        // Should have only 1 directive (no new open directives since account already has member)
        assert_eq!(directives.len(), 1);

        if let DirectiveData::Transaction(txn_data) = &directives[0].data {
            // Postings should be unchanged
            assert_eq!(txn_data.postings.len(), 2);
            assert!(
                txn_data
                    .postings
                    .iter()
                    .any(|p| p.account == "Expenses:Food:Martin")
            );
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_split_expenses_no_config() {
        let plugin = SplitExpensesPlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction(vec![PostingData {
                account: "Expenses:Food".to_string(),
                units: Some(AmountData {
                    number: "100.00".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: None,
                flag: None,
                metadata: vec![],
                span: None,
            }])],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);

        // Should return unchanged
        assert_eq!(directives.len(), 1);
        if let DirectiveData::Transaction(txn_data) = &directives[0].data {
            assert_eq!(txn_data.postings.len(), 1);
            assert_eq!(txn_data.postings[0].account, "Expenses:Food");
        } else {
            panic!("Expected transaction");
        }
    }
}
