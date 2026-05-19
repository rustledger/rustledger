//! Box accrual plugin - splits capital losses across multiple years.
//!
//! This plugin looks for transactions with `synthetic_loan_expiry` metadata
//! and splits Capital-Losses postings proportionally across years.
//!
//! Usage:
//! ```text
//! plugin "beancount_reds_plugins.box_accrual.box_accrual"
//!
//! 2024-01-15 * "Sell synthetic"
//!   synthetic_loan_expiry: 2026-06-30
//!   Assets:Broker        1000 USD
//!   Income:Capital-Losses  -500 USD
//! ```

use rust_decimal::Decimal;
use rust_decimal::prelude::*;
use rustledger_core::NaiveDate;

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, MetaValueData, PluginInput, PluginOp,
    PluginOutput, PostingData, TransactionData,
};

use super::super::NativePlugin;

/// Plugin for splitting capital losses across multiple years.
pub struct BoxAccrualPlugin;

impl NativePlugin for BoxAccrualPlugin {
    fn name(&self) -> &'static str {
        "box_accrual"
    }

    fn description(&self) -> &'static str {
        "Split capital losses across multiple years based on expiry date"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());

        for (i, directive) in input.directives.into_iter().enumerate() {
            if directive.directive_type != "transaction" {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            if let DirectiveData::Transaction(txn) = &directive.data {
                // Look for synthetic_loan_expiry in metadata
                let expiry_date = txn
                    .metadata
                    .iter()
                    .find(|(k, _)| k == "synthetic_loan_expiry")
                    .and_then(|(_, v)| match v {
                        MetaValueData::Date(d) => d.parse::<NaiveDate>().ok(),
                        MetaValueData::String(s) => s.parse::<NaiveDate>().ok(),
                        _ => None,
                    });

                let expiry_date = if let Some(d) = expiry_date {
                    d
                } else {
                    ops.push(PluginOp::Keep(i));
                    continue;
                };

                // Find Capital-Losses posting
                let losses: Vec<&PostingData> = txn
                    .postings
                    .iter()
                    .filter(|p| p.account.ends_with(":Capital-Losses"))
                    .collect();

                if losses.len() != 1 {
                    ops.push(PluginOp::Keep(i));
                    continue;
                }

                let loss_posting = losses[0];
                let (total_loss, currency) = if let Some(units) = &loss_posting.units {
                    let number = if let Ok(n) = Decimal::from_str(&units.number) {
                        n
                    } else {
                        ops.push(PluginOp::Keep(i));
                        continue;
                    };
                    (number, units.currency.clone())
                } else {
                    ops.push(PluginOp::Keep(i));
                    continue;
                };

                let start_date = if let Ok(d) = directive.date.parse::<NaiveDate>() {
                    d
                } else {
                    ops.push(PluginOp::Keep(i));
                    continue;
                };

                // If same year, no splitting needed
                if start_date.year() == expiry_date.year() {
                    ops.push(PluginOp::Keep(i));
                    continue;
                }

                // Calculate total days (inclusive)
                let total_days =
                    i64::from(expiry_date.since(start_date).unwrap_or_default().get_days()) + 1;
                if total_days <= 0 {
                    ops.push(PluginOp::Keep(i));
                    continue;
                }

                // Build year splits
                let mut fractions: Vec<(i32, i64, NaiveDate)> = Vec::new();
                for year in i32::from(start_date.year())..=i32::from(expiry_date.year()) {
                    let seg_start = if year == i32::from(start_date.year()) {
                        start_date
                    } else {
                        rustledger_core::naive_date(year, 1, 1).unwrap()
                    };
                    let seg_end = if year == i32::from(expiry_date.year()) {
                        expiry_date
                    } else {
                        rustledger_core::naive_date(year, 12, 31).unwrap()
                    };
                    let seg_days = i64::from(seg_end.since(seg_start).unwrap().get_days()) + 1;
                    if seg_days > 0 {
                        fractions.push((year, seg_days, seg_end));
                    }
                }

                // Calculate and round each year's loss
                let mut splits: Vec<PostingData> = Vec::new();
                let mut rounded_sum = Decimal::ZERO;
                let total_days_dec = Decimal::from(total_days);

                for (i, (_year, seg_days, seg_end)) in fractions.iter().enumerate() {
                    let frac = Decimal::from(*seg_days) / total_days_dec;
                    let mut seg_amt = total_loss * frac;

                    if i < fractions.len() - 1 {
                        // Round to 2 decimal places
                        seg_amt = seg_amt
                            .round_dp_with_strategy(2, RoundingStrategy::MidpointAwayFromZero);
                        rounded_sum += seg_amt;
                    } else {
                        // Final segment = remainder
                        seg_amt = total_loss - rounded_sum;
                        seg_amt = seg_amt
                            .round_dp_with_strategy(2, RoundingStrategy::MidpointAwayFromZero);
                    }

                    splits.push(PostingData {
                        account: loss_posting.account.clone(),
                        units: Some(AmountData {
                            number: format_decimal(seg_amt),
                            currency: currency.clone(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![(
                            "effective_date".to_string(),
                            MetaValueData::Date(seg_end.to_string()),
                        )],
                        span: None,
                    });
                }

                // Build new postings: all except the original loss posting + splits
                let mut new_postings: Vec<PostingData> = txn
                    .postings
                    .iter()
                    .filter(|p| !p.account.ends_with(":Capital-Losses"))
                    .cloned()
                    .collect();
                new_postings.extend(splits);

                ops.push(PluginOp::Modify(
                    i,
                    DirectiveWrapper {
                        directive_type: "transaction".to_string(),
                        date: directive.date.clone(),
                        filename: directive.filename.clone(),
                        lineno: directive.lineno,
                        data: DirectiveData::Transaction(TransactionData {
                            flag: txn.flag.clone(),
                            payee: txn.payee.clone(),
                            narration: txn.narration.clone(),
                            tags: txn.tags.clone(),
                            links: txn.links.clone(),
                            metadata: txn.metadata.clone(),
                            postings: new_postings,
                        }),
                    },
                ));
            } else {
                ops.push(PluginOp::Keep(i));
            }
        }

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

/// Format a decimal number with 2 decimal places.
fn format_decimal(d: Decimal) -> String {
    let s = d.to_string();
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    } else {
        s
    }
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    #[test]
    fn test_box_accrual_splits_across_years() {
        let plugin = BoxAccrualPlugin;

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-07-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Sell synthetic".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![(
                        "synthetic_loan_expiry".to_string(),
                        MetaValueData::Date("2025-06-30".to_string()),
                    )],
                    postings: vec![
                        PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "1000".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        },
                        PostingData {
                            account: "Income:Capital-Losses".to_string(),
                            units: Some(AmountData {
                                number: "-365".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
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

        // Find the transaction
        let txn = directives
            .iter()
            .find(|d| matches!(d.data, DirectiveData::Transaction(_)));
        assert!(txn.is_some());

        if let DirectiveData::Transaction(t) = &txn.unwrap().data {
            // Should have multiple Capital-Losses postings (split across years)
            let loss_postings: Vec<_> = t
                .postings
                .iter()
                .filter(|p| p.account.ends_with(":Capital-Losses"))
                .collect();

            // Should have 2 splits (2024 and 2025)
            assert_eq!(loss_postings.len(), 2);

            // Each should have effective_date metadata
            for posting in &loss_postings {
                assert!(posting.metadata.iter().any(|(k, _)| k == "effective_date"));
            }
        }
    }

    #[test]
    fn test_box_accrual_same_year_unchanged() {
        let plugin = BoxAccrualPlugin;

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Sell".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![(
                        "synthetic_loan_expiry".to_string(),
                        MetaValueData::Date("2024-12-31".to_string()),
                    )],
                    postings: vec![PostingData {
                        account: "Income:Capital-Losses".to_string(),
                        units: Some(AmountData {
                            number: "-100".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    }],
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

        // Should be unchanged (same year)
        if let DirectiveData::Transaction(t) = &directives[0].data {
            assert_eq!(t.postings.len(), 1);
        }
    }
}
