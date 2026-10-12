//! Zero balance assertion on balance sheet account close.

use crate::types::{DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::increment_date;

/// Plugin that inserts zero balance assertions when balance sheet accounts are closed.
///
/// When a Close directive is encountered for an account (Assets, Liabilities, or Equity),
/// this plugin generates Balance directives with zero amounts for all currencies that
/// were used in that account. The assertions are dated one day after the close date.
pub struct CheckDrainedPlugin;

impl NativePlugin for CheckDrainedPlugin {
    fn name(&self) -> &'static str {
        "check_drained"
    }

    fn description(&self) -> &'static str {
        "Zero balance assertion on balance sheet account close"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use crate::types::{AmountData, BalanceData};
        use std::collections::{BTreeSet, HashMap};

        // The currencies each account has used so far, as beancount's plugin
        // accumulates them walking the entries in order: a posting's, and an
        // `open`'s declared ones. Not a `balance`'s (beancount's does not
        // count one), and not a posting after the close (it had not been
        // seen yet), both of which rledger used to insert a check for
        // (#2600). Sorted, so the checks come out in one order.
        let mut account_currencies: HashMap<&str, BTreeSet<&str>> = HashMap::new();
        let mut ops: Vec<PluginOp> = Vec::new();

        for (i, wrapper) in input.directives.iter().enumerate() {
            ops.push(PluginOp::Keep(i));
            match &wrapper.data {
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        if let Some(units) = &posting.units {
                            account_currencies
                                .entry(posting.account.as_str())
                                .or_default()
                                .insert(units.currency.as_str());
                        }
                    }
                }
                DirectiveData::Open(data) => {
                    let currencies = account_currencies.entry(data.account.as_str()).or_default();
                    currencies.extend(data.currencies.iter().map(String::as_str));
                }
                DirectiveData::Close(data) => {
                    // Only balance sheet accounts (Assets, Liabilities,
                    // Equity), under THIS ledger's configured root names —
                    // `account_type` hardcodes the English ones, so a renamed
                    // ledger classified every close as off-balance-sheet and
                    // silently skipped it (#1964). Root-component match, so
                    // both `Assets:...` and a bare `Assets` qualify.
                    if !input.options.account_types.is_balance_sheet(&data.account) {
                        continue;
                    }
                    let (Some(currencies), Some(next_date)) = (
                        account_currencies.get(data.account.as_str()),
                        increment_date(&wrapper.date),
                    ) else {
                        continue;
                    };
                    // A zero balance assertion per currency, the day after
                    // the close. Deliberately not skipped when an explicit
                    // `balance` for the currency sits on the close date, as
                    // beancount's plugin skips it: that assertion runs at the
                    // start of the day and misses the day's own postings,
                    // which this one does not.
                    for currency in currencies {
                        ops.push(PluginOp::Insert(DirectiveWrapper {
                            directive_type: "balance".to_string(),
                            date: next_date.clone(),
                            // The close's location, as beancount gives the
                            // balance the close's meta: a failure points at
                            // the close.
                            filename: wrapper.filename.clone(),
                            lineno: wrapper.lineno,
                            data: DirectiveData::Balance(BalanceData {
                                account: data.account.clone(),
                                amount: AmountData {
                                    number: "0".to_string(),
                                    currency: (*currency).to_string(),
                                },
                                tolerance: None,
                                metadata: vec![],
                            }),
                        }));
                    }
                }
                _ => {}
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

impl RegularPlugin for CheckDrainedPlugin {}

#[cfg(test)]
mod check_drained_tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    #[test]
    fn test_check_drained_adds_balance_assertion() {
        let plugin = CheckDrainedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec!["USD".to_string()],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-06-15".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Deposit".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Close(CloseData {
                        account: "Assets:Bank".to_string(),
                        metadata: vec![],
                    }),
                },
            ],
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
        // Should have 4 directives: open, transaction, close, balance
        assert_eq!(directives.len(), 4);

        // Find the balance directive
        let balance = directives
            .iter()
            .find(|d| matches!(d.data, DirectiveData::Balance(_)))
            .expect("Should have balance directive");

        assert_eq!(balance.date, "2025-01-01"); // Day after close
        if let DirectiveData::Balance(b) = &balance.data {
            assert_eq!(b.account, "Assets:Bank");
            assert_eq!(b.amount.number, "0");
            assert_eq!(b.amount.currency, "USD");
        } else {
            panic!("Expected Balance directive");
        }
    }

    #[test]
    fn test_check_drained_ignores_income_expense() {
        let plugin = CheckDrainedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Income:Salary".to_string(),
                        currencies: vec!["USD".to_string()],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Close(CloseData {
                        account: "Income:Salary".to_string(),
                        metadata: vec![],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        // Should not add balance assertions for income/expense accounts
        assert_eq!(directives.len(), 2);
        assert!(
            !directives
                .iter()
                .any(|d| matches!(d.data, DirectiveData::Balance(_)))
        );
    }

    #[test]
    fn test_check_drained_multiple_currencies() {
        let plugin = CheckDrainedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-06-15".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "USD Deposit".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-07-15".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "EUR Deposit".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "50".to_string(),
                                currency: "EUR".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Close(CloseData {
                        account: "Assets:Bank".to_string(),
                        metadata: vec![],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        // Should have 6 directives: open, 2 transactions, close, 2 balance assertions
        assert_eq!(directives.len(), 6);

        let balances: Vec<_> = directives
            .iter()
            .filter(|d| matches!(d.data, DirectiveData::Balance(_)))
            .collect();
        assert_eq!(balances.len(), 2);

        // Both should be dated 2025-01-01
        for b in &balances {
            assert_eq!(b.date, "2025-01-01");
        }
    }
}
