//! Validate that reducing postings use the average cost for accounts
//! opened with the NONE booking method.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOutput};

use super::super::NativePlugin;

/// Plugin that validates reducing postings against the running average cost
/// for accounts opened with the `NONE` booking method.
///
/// When an account is opened with `NONE` booking, the ledger author is responsible
/// for lot matching — there is no booker to enforce it. This plugin is a safety net
/// for that case: it verifies that the cost basis used on any reducing leg is within
/// tolerance of the running average cost basis in the account.
///
/// Accounts opened with any other booking method (`STRICT`, `STRICT_WITH_SIZE`,
/// `FIFO`, `LIFO`, `HIFO`, `AVERAGE`, …) are skipped — their booker already validates
/// lot matching, so re-checking here would produce false positives (see issue #907).
/// This matches Python beancount's `beancount.plugins.check_average_cost` behavior.
pub struct CheckAverageCostPlugin {
    /// Tolerance for cost comparison (default: 0.01 = 1%).
    tolerance: rust_decimal::Decimal,
}

impl CheckAverageCostPlugin {
    /// Create with default tolerance (1%).
    pub fn new() -> Self {
        Self {
            tolerance: rust_decimal::Decimal::new(1, 2), // 0.01 = 1%
        }
    }

    /// Create with custom tolerance.
    pub const fn with_tolerance(tolerance: rust_decimal::Decimal) -> Self {
        Self { tolerance }
    }
}

impl Default for CheckAverageCostPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for CheckAverageCostPlugin {
    fn name(&self) -> &'static str {
        "check_average_cost"
    }

    fn description(&self) -> &'static str {
        "Validate reducing postings match average cost"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use rust_decimal::Decimal;
        use std::collections::{HashMap, HashSet};
        use std::str::FromStr;

        // Parse optional tolerance from config
        let tolerance = if let Some(config) = &input.config {
            Decimal::from_str(config.trim()).unwrap_or(self.tolerance)
        } else {
            self.tolerance
        };

        // First pass: collect accounts opened with the NONE booking method.
        // Only these accounts are subject to the average-cost check — see the
        // type-level docstring and issue #907 for rationale.
        let none_booking_accounts: HashSet<&str> = input
            .directives
            .iter()
            .filter_map(|w| match &w.data {
                DirectiveData::Open(o) => o
                    .booking
                    .as_deref()
                    .filter(|b| b.eq_ignore_ascii_case("NONE"))
                    .map(|_| o.account.as_str()),
                _ => None,
            })
            .collect();

        // Track average cost per account per commodity
        // Key: (account, commodity) -> (total_units, total_cost)
        let mut inventory: HashMap<(String, String), (Decimal, Decimal)> = HashMap::new();

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    // Only process accounts opened with NONE booking (issue #907).
                    if !none_booking_accounts.contains(posting.account.as_str()) {
                        continue;
                    }

                    // Only process postings with units and cost
                    let Some(units) = &posting.units else {
                        continue;
                    };
                    let Some(cost) = &posting.cost else {
                        continue;
                    };

                    let units_num = Decimal::from_str(&units.number).unwrap_or_default();
                    let Some(cost_currency) = &cost.currency else {
                        continue;
                    };

                    let key = (posting.account.clone(), units.currency.clone());

                    if units_num > Decimal::ZERO {
                        // Acquisition: add to inventory
                        let cost_per = cost
                            .number_per
                            .as_ref()
                            .and_then(|s| Decimal::from_str(s).ok())
                            .unwrap_or_default();

                        let entry = inventory
                            .entry(key)
                            .or_insert((Decimal::ZERO, Decimal::ZERO));
                        entry.0 += units_num; // total units
                        entry.1 += units_num * cost_per; // total cost
                    } else if units_num < Decimal::ZERO {
                        // Reduction: check against average cost
                        let entry = inventory.get(&key);

                        if let Some((total_units, total_cost)) = entry
                            && *total_units > Decimal::ZERO
                        {
                            let avg_cost = *total_cost / *total_units;

                            // Get the cost used in this posting
                            let used_cost = cost
                                .number_per
                                .as_ref()
                                .and_then(|s| Decimal::from_str(s).ok())
                                .unwrap_or_default();

                            // Calculate relative difference
                            let diff = (used_cost - avg_cost).abs();
                            let relative_diff = if avg_cost == Decimal::ZERO {
                                diff
                            } else {
                                diff / avg_cost
                            };

                            if relative_diff > tolerance {
                                errors.push(PluginError::warning(format!(
                                        "Sale of {} {} in {} uses cost {} {} but average cost is {} {} (difference: {:.2}%)",
                                        units_num.abs(),
                                        units.currency,
                                        posting.account,
                                        used_cost,
                                        cost_currency,
                                        avg_cost.round_dp(4),
                                        cost_currency,
                                        relative_diff * Decimal::from(100)
                                    )));
                            }

                            // Update inventory
                            let entry = inventory.get_mut(&key).unwrap();
                            let units_sold = units_num.abs();
                            let cost_removed = units_sold * avg_cost;
                            entry.0 -= units_sold;
                            entry.1 -= cost_removed;
                        }
                    }
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

#[cfg(test)]
mod check_average_cost_tests {
    use super::*;
    use crate::types::*;

    fn open_with_none_booking(account: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "open".to_string(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Open(OpenData {
                account: account.to_string(),
                currencies: vec![],
                booking: Some("NONE".to_string()),
                metadata: vec![],
            }),
        }
    }

    #[test]
    fn test_check_average_cost_matching() {
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                open_with_none_booking("Assets:Broker"),
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at avg cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()), // Matches average
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_check_average_cost_mismatch() {
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                open_with_none_booking("Assets:Broker"),
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at wrong cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("90.00".to_string()), // 10% different from avg
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("average cost"));
    }

    #[test]
    fn test_check_average_cost_multiple_buys() {
        let plugin = CheckAverageCostPlugin::new();

        // Buy 10 at $100, then 10 at $120 -> avg = $110
        let input = PluginInput {
            directives: vec![
                open_with_none_booking("Assets:Broker"),
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 120".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("120.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at avg cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("110.00".to_string()), // Matches average
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_non_none_booking_is_skipped() {
        // Regression test for issue #907: accounts opened with any booking
        // method other than NONE (including the default, an unspecified
        // booking, or explicit STRICT/FIFO/etc.) must be skipped entirely.
        // The booker is responsible for lot matching in those cases, so
        // re-checking here produces false positives like the reporter's
        // "500 USD vs. avg 566.67 USD" error.
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                // No booking specified (booking: None). Whatever the effective
                // default is — STRICT unless overridden by `option
                // "booking_method"` or a loader setting — it is NOT `NONE`,
                // so the plugin MUST skip this account.
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Broker".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at way-off cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                // 50% off the average — would fire for NONE,
                                // but must be silent for STRICT/default.
                                number_per: Some("50.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert!(
            output.errors.is_empty(),
            "non-NONE accounts must be skipped; got errors: {:?}",
            output.errors
        );
    }
}
