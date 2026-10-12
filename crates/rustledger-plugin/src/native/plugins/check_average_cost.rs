//! Validate that reducing postings use the average cost for accounts
//! opened with the NONE booking method.

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::py_literal::{self, PyValue};
use super::utils::at_entry;

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

        let keep = || (0..input.directives.len()).map(PluginOp::Keep).collect();
        // The tolerance, a Python float, as beancount's `eval`s it; anything
        // else is an error there too.
        let tolerance = match input.config.as_deref().map(str::trim) {
            None | Some("") => self.tolerance,
            Some(config) => match parse_float(config) {
                Some(t) => t,
                None => {
                    return PluginOutput {
                        ops: keep(),
                        errors: vec![PluginError::error(
                            "Invalid configuration for check_average_cost: must be a float",
                        )],
                    };
                }
            },
        };
        // Deliberate divergence: beancount computes `D(1 - tolerance)` from
        // the binary float, so with `0.1` its lower bound is 0.9000000000000000222
        // and a cost of exactly 90% of the average fails there. The bounds
        // here are exact decimals, so a cost exactly at a bound passes.
        let min_tolerance = Decimal::ONE - tolerance;
        let max_tolerance = Decimal::ONE + tolerance;

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

        // The account's inventory, as beancount keeps it: per (account,
        // currency, cost currency), every posting added at the cost it was
        // booked at, a reduction included. Under NONE booking a sale is a
        // negative lot at its own cost, so the average after it is the
        // average of what the account actually holds (#2600: rledger removed
        // a sale at the average cost instead, and its average drifted from
        // the ledger's from the first off-average sale on).
        // Key -> (total units, total cost).
        let mut inventory: HashMap<(&str, &str, &str), (Decimal, Decimal)> = HashMap::new();

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                continue;
            };
            for posting in &txn.postings {
                // Only process accounts opened with NONE booking (issue #907).
                if !none_booking_accounts.contains(posting.account.as_str()) {
                    continue;
                }
                // Only postings held at cost. (beancount's own plugin fails
                // outright on a reduction without one.)
                let (Some(units), Some(cost)) = (&posting.units, &posting.cost) else {
                    continue;
                };
                let Some(cost_currency) = &cost.currency else {
                    continue;
                };
                let Ok(units_num) = Decimal::from_str(&units.number) else {
                    continue;
                };
                // `per_unit()` covers both PerUnit and PerUnitFromTotal.
                let Some(cost_text) = cost.number.as_ref().and_then(|cn| cn.per_unit()) else {
                    continue;
                };
                let Ok(cost_number) = Decimal::from_str(cost_text) else {
                    continue;
                };
                // The cost as beancount prints it: a `{{total}}` cost is
                // booked as `total / units` at Python's 28 digits, where
                // `rust_decimal` keeps 29.
                let shown_cost = match &cost.number {
                    Some(rustledger_plugin_types::CostNumberData::PerUnitFromTotal {
                        total,
                        ..
                    }) => Decimal::from_str(total).map_or_else(
                        |_| cost_text.to_string(),
                        |t| python_quotient(t, units_num.abs()),
                    ),
                    _ => cost_text.to_string(),
                };

                let key = (
                    posting.account.as_str(),
                    units.currency.as_str(),
                    cost_currency.as_str(),
                );
                let (total_units, total_cost) = inventory
                    .entry(key)
                    .or_insert((Decimal::ZERO, Decimal::ZERO));

                // A reduction is checked against the average before it, when
                // the account holds any (beancount skips a zero total).
                if units_num < Decimal::ZERO
                    && !total_units.is_zero()
                    && let Some(average) = total_cost.checked_div(*total_units)
                {
                    let min_valid = average * min_tolerance;
                    let max_valid = average * max_tolerance;
                    if !(min_valid <= cost_number && cost_number <= max_valid) {
                        errors.push(at_entry(
                            PluginError::error(format!(
                                "Cost basis on reducing posting is too far from the average cost ({} vs. {})",
                                shown_cost,
                                python_quotient(*total_cost, *total_units)
                            )),
                            wrapper,
                        ));
                    }
                }

                *total_units += units_num;
                *total_cost += units_num * cost_number;
            }
        }

        PluginOutput {
            ops: keep(),
            errors,
        }
    }
}

/// `config` as a Python float literal (`0.01`, `1e-2`), as beancount's
/// `eval` must find one; `None` for anything else, an integer included.
/// beancount `eval`s the config with builtins, so an expression such as
/// `float('0.1')` also works there; only a literal does here.
fn parse_float(config: &str) -> Option<rust_decimal::Decimal> {
    use std::str::FromStr;
    let Ok(PyValue::Number { text, .. }) = py_literal::parse(config) else {
        return None;
    };
    let text = text.replace('_', "");
    if !text.contains(['.', 'e', 'E']) {
        return None;
    }
    rust_decimal::Decimal::from_str(&text)
        .or_else(|_| rust_decimal::Decimal::from_scientific(&text))
        .ok()
}

/// `a / b` printed as Python's `decimal` prints it in its default context: an
/// exact quotient at its ideal scale, an inexact one rounded half-even to 28
/// significant digits (`rust_decimal` keeps one more).
fn python_quotient(a: rust_decimal::Decimal, b: rust_decimal::Decimal) -> String {
    use bigdecimal::{BigDecimal, RoundingMode};
    use rustledger_core::decimal::{checked_div_python_scale, to_bigdecimal};
    let Some(quotient) = checked_div_python_scale(a, b) else {
        return String::new();
    };
    let (a, b_big) = (to_bigdecimal(a), to_bigdecimal(b));
    // Exact only if it multiplies back exactly: `Decimal`'s own product
    // rounds, and would call 16.666...667 × 15 exactly 250.
    if to_bigdecimal(quotient) * &b_big == a {
        return quotient.to_string();
    }
    let exact: BigDecimal = a / b_big;
    exact
        .with_precision_round(
            std::num::NonZeroU64::new(28).expect("28"),
            RoundingMode::HalfEven,
        )
        .to_plain_string()
}

impl RegularPlugin for CheckAverageCostPlugin {}

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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }), // Matches average
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "90.00".to_string(),
                                }), // 10% different from avg
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "120.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "110.00".to_string(),
                                }), // Matches average
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "100.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
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
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                    value: "50.00".to_string(),
                                }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        }],
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

        let output = plugin.process(input);
        assert!(
            output.errors.is_empty(),
            "non-NONE accounts must be skipped; got errors: {:?}",
            output.errors
        );
    }
}
