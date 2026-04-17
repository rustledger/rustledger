//! Valuation plugin - track opaque fund values using synthetic commodities.
//!
//! This plugin allows specifying total investment account value over time and
//! creates an underlying fictional commodity whose price is set to match the
//! total value of the account.
//!
//! All incoming and outgoing transactions are converted into transactions
//! buying and selling this commodity at a calculated price.
//!
//! Usage:
//! ```beancount
//! plugin "beancount_lazy_plugins.valuation"
//!
//! 1970-01-01 open Assets:Fund:Total "FIFO"
//! 1970-01-01 open Income:Fund:PnL
//!
//! 1970-01-01 custom "valuation" "config"
//!     account: "Assets:Fund:Total"
//!     currency: "FUND_USD"
//!     pnlAccount: "Income:Fund:PnL"
//!
//! ; Assert total value
//! 2024-01-05 custom "valuation" Assets:Fund:Total 2345 USD
//! ```

use std::collections::{HashMap, HashSet};

use rust_decimal::Decimal;

use crate::types::{
    AmountData, CommodityData, CostData, DirectiveData, DirectiveWrapper, MetaValueData,
    PluginError, PluginErrorSeverity, PluginInput, PluginOutput, PostingData, PriceAnnotationData,
    PriceData, TransactionData,
};

use super::super::NativePlugin;

const MAPPED_CURRENCY_PRECISION: u32 = 7;
const TAG_TO_ADD: &str = "valuation-applied";
const EPSILON: Decimal = Decimal::from_parts(1, 0, 0, false, 9); // 1e-9

/// Plugin for tracking opaque fund values.
pub struct ValuationPlugin;

/// Account mapping configuration.
#[derive(Clone, Debug)]
struct AccountConfig {
    account: String,
    currency: String,
    pnl_account: String,
}

/// A cost lot for FIFO tracking.
#[derive(Clone, Debug)]
struct CostLot {
    units: Decimal,
    cost_per_unit: Decimal,
    date: String,
}

/// State for a mapped account.
#[derive(Clone, Debug)]
struct AccountState {
    config: AccountConfig,
    lots: Vec<CostLot>,
    last_price: Decimal,
    total_units: Decimal,
}

impl AccountState {
    const fn new(config: AccountConfig) -> Self {
        Self {
            config,
            lots: Vec::new(),
            last_price: Decimal::ONE,
            total_units: Decimal::ZERO,
        }
    }
}

impl NativePlugin for ValuationPlugin {
    fn name(&self) -> &'static str {
        "valuation"
    }

    fn description(&self) -> &'static str {
        "Track opaque fund values using synthetic commodities"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut errors: Vec<PluginError> = Vec::new();
        let mut output_directives: Vec<DirectiveWrapper> = Vec::new();

        // Track state per account
        let mut account_states: HashMap<String, AccountState> = HashMap::new();

        // Track which commodities already exist
        let mut commodities_present: HashSet<String> = HashSet::new();

        // Track last date for commodity directive generation
        let mut last_date: Option<String> = None;

        // First pass: collect configs and existing commodities
        for directive in &input.directives {
            match &directive.data {
                DirectiveData::Custom(custom) => {
                    if custom.custom_type == "valuation"
                        && !custom.values.is_empty()
                        && matches!(custom.values.first(), Some(MetaValueData::String(s)) if s == "config")
                        && let Some(config) = parse_config(&custom.metadata)
                    {
                        account_states.insert(config.account.clone(), AccountState::new(config));
                    }
                }
                DirectiveData::Commodity(commodity) => {
                    commodities_present.insert(commodity.currency.clone());
                }
                _ => {}
            }
        }

        // Second pass: process directives in order
        for directive in input.directives {
            last_date = Some(directive.date.clone());

            match &directive.data {
                DirectiveData::Transaction(txn) => {
                    // Check if any posting is on a mapped account
                    let has_mapped_posting = txn
                        .postings
                        .iter()
                        .any(|p| account_states.contains_key(&p.account));

                    if !has_mapped_posting {
                        output_directives.push(directive);
                        continue;
                    }

                    // Transform the transaction
                    let (transformed, new_directives, new_errors) = transform_transaction(
                        &directive,
                        txn,
                        &mut account_states,
                        &mut commodities_present,
                    );

                    // Add any price directives generated
                    output_directives.extend(new_directives);
                    errors.extend(new_errors);
                    output_directives.push(transformed);
                }
                DirectiveData::Custom(custom)
                    if custom.custom_type == "valuation" && !custom.values.is_empty() =>
                {
                    // Check if this is a config (pass through) or a valuation assertion
                    if matches!(custom.values.first(), Some(MetaValueData::String(s)) if s == "config")
                    {
                        output_directives.push(directive);
                        continue;
                    }

                    // This is a valuation assertion
                    let (new_directives, new_errors) =
                        process_valuation_assertion(&directive, custom, &mut account_states);

                    output_directives.extend(new_directives);
                    errors.extend(new_errors);
                }
                DirectiveData::Custom(_) => {
                    output_directives.push(directive);
                }
                DirectiveData::Commodity(commodity) => {
                    commodities_present.insert(commodity.currency.clone());
                    output_directives.push(directive);
                }
                _ => {
                    output_directives.push(directive);
                }
            }
        }

        // Generate commodity directives for synthetic currencies that don't exist
        // Use the last transaction date, not 1970-01-01
        if let Some(date) = last_date {
            for state in account_states.values() {
                if !commodities_present.contains(&state.config.currency) {
                    output_directives.push(DirectiveWrapper {
                        directive_type: "commodity".to_string(),
                        date: date.clone(),
                        filename: Some("<valuation>".to_string()),
                        lineno: Some(0),
                        data: DirectiveData::Commodity(CommodityData {
                            currency: state.config.currency.clone(),
                            metadata: vec![],
                        }),
                    });
                    // Only add once
                    commodities_present.insert(state.config.currency.clone());
                }
            }
        }

        PluginOutput {
            directives: output_directives,
            errors,
        }
    }
}

/// Parse config metadata into `AccountConfig`.
fn parse_config(metadata: &[(String, MetaValueData)]) -> Option<AccountConfig> {
    let account = get_meta_string(metadata, "account")?;
    let currency = get_meta_string(metadata, "currency")?;
    let pnl_account = get_meta_string(metadata, "pnlAccount")?;
    Some(AccountConfig {
        account,
        currency,
        pnl_account,
    })
}

/// Get a string value from metadata.
fn get_meta_string(metadata: &[(String, MetaValueData)], key: &str) -> Option<String> {
    for (k, v) in metadata {
        if k == key {
            match v {
                MetaValueData::String(s) => return Some(s.clone()),
                MetaValueData::Account(a) => return Some(a.clone()),
                _ => {}
            }
        }
    }
    None
}

/// Transform a transaction that has postings on mapped accounts.
fn transform_transaction(
    directive: &DirectiveWrapper,
    txn: &TransactionData,
    account_states: &mut HashMap<String, AccountState>,
    _commodities_present: &mut HashSet<String>,
) -> (DirectiveWrapper, Vec<DirectiveWrapper>, Vec<PluginError>) {
    let mut new_directives: Vec<DirectiveWrapper> = Vec::new();
    let errors: Vec<PluginError> = Vec::new();
    let mut new_postings: Vec<PostingData> = Vec::new();

    for posting in &txn.postings {
        if let Some(state) = account_states.get_mut(&posting.account) {
            // This is a mapped account posting
            let Some(ref units) = posting.units else {
                new_postings.push(posting.clone());
                continue;
            };

            let Ok(units_number) = units.number.parse::<Decimal>() else {
                new_postings.push(posting.clone());
                continue;
            };

            // Check for @@ total price annotation
            if let Some(ref price_annot) = posting.price
                && price_annot.is_total
            {
                // Handle @@ price annotation - generates 3 postings
                let (postings, price_directive) = handle_total_price_posting(
                    posting,
                    units_number,
                    &units.currency,
                    price_annot,
                    state,
                    &directive.date,
                    directive,
                );
                if let Some(pd) = price_directive {
                    new_directives.push(pd);
                }
                new_postings.extend(postings);
                continue;
            }

            // Generate initial price directive if this is the first transaction
            if state.lots.is_empty() && state.total_units == Decimal::ZERO {
                new_directives.push(DirectiveWrapper {
                    directive_type: "price".to_string(),
                    date: directive.date.clone(),
                    filename: directive.filename.clone(),
                    lineno: directive.lineno,
                    data: DirectiveData::Price(PriceData {
                        currency: state.config.currency.clone(),
                        amount: AmountData {
                            number: format_decimal(state.last_price),
                            currency: units.currency.clone(),
                        },
                        metadata: vec![],
                    }),
                });
            }

            if units_number > Decimal::ZERO {
                // INFLOW: Convert to synthetic currency
                let synthetic_units =
                    round_up(units_number / state.last_price, MAPPED_CURRENCY_PRECISION);

                // Add to lots
                state.lots.push(CostLot {
                    units: synthetic_units,
                    cost_per_unit: state.last_price,
                    date: directive.date.clone(),
                });
                state.total_units += synthetic_units;

                // Create posting with cost basis
                new_postings.push(PostingData {
                    account: posting.account.clone(),
                    units: Some(AmountData {
                        number: format_decimal_fixed(synthetic_units, MAPPED_CURRENCY_PRECISION),
                        currency: state.config.currency.clone(),
                    }),
                    cost: Some(CostData {
                        number_per: Some(format_decimal(state.last_price)),
                        number_total: None,
                        currency: Some(units.currency.clone()),
                        date: Some(directive.date.clone()),
                        label: None,
                        merge: false,
                    }),
                    price: None,
                    flag: posting.flag.clone(),
                    metadata: posting.metadata.clone(),
                });
            } else {
                // OUTFLOW: FIFO sell from lots
                let amount_to_sell = -units_number;
                let (sell_postings, total_pnl) = process_fifo_sell(
                    state,
                    amount_to_sell,
                    &posting.account,
                    &units.currency,
                    &posting.flag,
                    &posting.metadata,
                );

                // Add PnL posting first (negative PnL = gain)
                if total_pnl != Decimal::ZERO {
                    new_postings.push(PostingData {
                        account: state.config.pnl_account.clone(),
                        units: Some(AmountData {
                            number: format_decimal(-total_pnl),
                            currency: units.currency.clone(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    });
                }

                // Add the sell postings
                new_postings.extend(sell_postings);
            }
        } else {
            // Not a mapped account, pass through
            new_postings.push(posting.clone());
        }
    }

    // Create modified transaction with tag
    let mut new_tags = txn.tags.clone();
    if !new_tags.contains(&TAG_TO_ADD.to_string()) {
        new_tags.push(TAG_TO_ADD.to_string());
    }

    let transformed = DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: directive.date.clone(),
        filename: directive.filename.clone(),
        lineno: directive.lineno,
        data: DirectiveData::Transaction(TransactionData {
            flag: txn.flag.clone(),
            payee: txn.payee.clone(),
            narration: txn.narration.clone(),
            tags: new_tags,
            links: txn.links.clone(),
            metadata: txn.metadata.clone(),
            postings: new_postings,
        }),
    };

    (transformed, new_directives, errors)
}

/// Handle posting with @@ total price annotation.
/// Returns the new postings and optionally a price directive.
fn handle_total_price_posting(
    posting: &PostingData,
    units_number: Decimal,
    units_currency: &str,
    price_annot: &PriceAnnotationData,
    state: &mut AccountState,
    date: &str,
    _directive: &DirectiveWrapper,
) -> (Vec<PostingData>, Option<DirectiveWrapper>) {
    let mut postings = Vec::new();

    // Get the total price amount
    let Some(ref price_amount) = price_annot.amount else {
        return (vec![posting.clone()], None);
    };

    let Ok(total_price) = price_amount.number.parse::<Decimal>() else {
        return (vec![posting.clone()], None);
    };

    // Calculate per-unit price
    let per_unit_price = total_price / units_number;

    // 1. Original posting with @ per_unit price
    postings.push(PostingData {
        account: posting.account.clone(),
        units: Some(AmountData {
            number: format_decimal(units_number),
            currency: units_currency.to_string(),
        }),
        cost: None,
        price: Some(PriceAnnotationData {
            is_total: false,
            amount: Some(AmountData {
                number: format_decimal(per_unit_price),
                currency: price_amount.currency.clone(),
            }),
            number: None,
            currency: None,
        }),
        flag: posting.flag.clone(),
        metadata: posting.metadata.clone(),
    });

    // 2. Reversal posting
    postings.push(PostingData {
        account: posting.account.clone(),
        units: Some(AmountData {
            number: format_decimal(-units_number),
            currency: units_currency.to_string(),
        }),
        cost: None,
        price: None,
        flag: None,
        metadata: vec![],
    });

    // 3. Synthetic currency posting
    let synthetic_units = round_up(units_number / state.last_price, MAPPED_CURRENCY_PRECISION);

    // Add to lots
    state.lots.push(CostLot {
        units: synthetic_units,
        cost_per_unit: state.last_price,
        date: date.to_string(),
    });
    state.total_units += synthetic_units;

    postings.push(PostingData {
        account: posting.account.clone(),
        units: Some(AmountData {
            number: format_decimal_fixed(synthetic_units, MAPPED_CURRENCY_PRECISION),
            currency: state.config.currency.clone(),
        }),
        cost: Some(CostData {
            number_per: Some(format_decimal(state.last_price)),
            number_total: None,
            currency: Some(units_currency.to_string()),
            date: Some(date.to_string()),
            label: None,
            merge: false,
        }),
        price: None,
        flag: None,
        metadata: vec![],
    });

    (postings, None)
}

/// Process FIFO sell and return postings and total `PnL`.
fn process_fifo_sell(
    state: &mut AccountState,
    amount_to_sell: Decimal,
    account: &str,
    currency: &str,
    flag: &Option<String>,
    metadata: &[(String, MetaValueData)],
) -> (Vec<PostingData>, Decimal) {
    let mut postings = Vec::new();
    let mut remaining = amount_to_sell;
    let mut total_pnl = Decimal::ZERO;
    let current_price = state.last_price;

    while remaining > EPSILON && !state.lots.is_empty() {
        let lot = &mut state.lots[0];
        let lot_value_at_current_price = lot.units * current_price;

        if lot_value_at_current_price <= remaining + EPSILON {
            // Sell entire lot
            let units_to_sell = lot.units;
            let pnl = (current_price - lot.cost_per_unit) * units_to_sell;
            total_pnl += pnl;

            // Round down for sells
            let rounded_units = round_down(units_to_sell, MAPPED_CURRENCY_PRECISION);

            postings.push(PostingData {
                account: account.to_string(),
                units: Some(AmountData {
                    number: format_decimal_fixed(-rounded_units, MAPPED_CURRENCY_PRECISION),
                    currency: state.config.currency.clone(),
                }),
                cost: Some(CostData {
                    number_per: Some(format_decimal(lot.cost_per_unit)),
                    number_total: None,
                    currency: Some(currency.to_string()),
                    date: Some(lot.date.clone()),
                    label: None,
                    merge: false,
                }),
                price: Some(PriceAnnotationData {
                    is_total: false,
                    amount: Some(AmountData {
                        number: format_decimal(current_price),
                        currency: currency.to_string(),
                    }),
                    number: None,
                    currency: None,
                }),
                flag: flag.clone(),
                metadata: if postings.is_empty() {
                    metadata.to_vec()
                } else {
                    vec![]
                },
            });

            state.total_units -= lot.units;
            remaining -= lot_value_at_current_price;
            state.lots.remove(0);
        } else {
            // Partial sell from this lot
            let units_to_sell = remaining / current_price;
            let pnl = (current_price - lot.cost_per_unit) * units_to_sell;
            total_pnl += pnl;

            let rounded_units = round_down(units_to_sell, MAPPED_CURRENCY_PRECISION);

            postings.push(PostingData {
                account: account.to_string(),
                units: Some(AmountData {
                    number: format_decimal_fixed(-rounded_units, MAPPED_CURRENCY_PRECISION),
                    currency: state.config.currency.clone(),
                }),
                cost: Some(CostData {
                    number_per: Some(format_decimal(lot.cost_per_unit)),
                    number_total: None,
                    currency: Some(currency.to_string()),
                    date: Some(lot.date.clone()),
                    label: None,
                    merge: false,
                }),
                price: Some(PriceAnnotationData {
                    is_total: false,
                    amount: Some(AmountData {
                        number: format_decimal(current_price),
                        currency: currency.to_string(),
                    }),
                    number: None,
                    currency: None,
                }),
                flag: flag.clone(),
                metadata: if postings.is_empty() {
                    metadata.to_vec()
                } else {
                    vec![]
                },
            });

            lot.units -= units_to_sell;
            state.total_units -= units_to_sell;
            remaining = Decimal::ZERO;
        }
    }

    (postings, total_pnl)
}

/// Process a valuation assertion custom directive.
fn process_valuation_assertion(
    directive: &DirectiveWrapper,
    custom: &crate::types::CustomData,
    account_states: &mut HashMap<String, AccountState>,
) -> (Vec<DirectiveWrapper>, Vec<PluginError>) {
    let mut new_directives: Vec<DirectiveWrapper> = Vec::new();
    let mut errors: Vec<PluginError> = Vec::new();

    // Parse the valuation: custom "valuation" Account Amount
    if custom.values.len() < 2 {
        new_directives.push(directive.clone());
        return (new_directives, errors);
    }

    let account = match &custom.values[0] {
        MetaValueData::Account(a) => a.clone(),
        MetaValueData::String(s) => s.clone(),
        _ => {
            new_directives.push(directive.clone());
            return (new_directives, errors);
        }
    };

    let Some(state) = account_states.get_mut(&account) else {
        errors.push(PluginError {
            message: format!("No valuation config for account {account}"),
            source_file: directive.filename.clone(),
            line_number: directive.lineno,
            severity: PluginErrorSeverity::Error,
        });
        new_directives.push(directive.clone());
        return (new_directives, errors);
    };

    let Some((valuation_amount, valuation_currency)) = parse_valuation_amount(&custom.values[1])
    else {
        new_directives.push(directive.clone());
        return (new_directives, errors);
    };

    // Get current balance in synthetic units
    let last_balance = state.total_units;

    if last_balance.abs() < EPSILON {
        errors.push(PluginError {
            message: format!("Valuation called on empty account {account}"),
            source_file: directive.filename.clone(),
            line_number: directive.lineno,
            severity: PluginErrorSeverity::Error,
        });
        new_directives.push(directive.clone());
        return (new_directives, errors);
    }

    // Calculate new price
    let calculated_price = valuation_amount / last_balance;
    state.last_price = calculated_price;

    // Create metadata for lastBalance and calculatedPrice
    let mut new_metadata = custom.metadata.clone();
    new_metadata.push((
        "lastBalance".to_string(),
        MetaValueData::Number(format_decimal(last_balance)),
    ));
    new_metadata.push((
        "calculatedPrice".to_string(),
        MetaValueData::Number(format_decimal(calculated_price)),
    ));

    // Add modified custom directive
    new_directives.push(DirectiveWrapper {
        directive_type: "custom".to_string(),
        date: directive.date.clone(),
        filename: directive.filename.clone(),
        lineno: directive.lineno,
        data: DirectiveData::Custom(crate::types::CustomData {
            custom_type: custom.custom_type.clone(),
            values: custom.values.clone(),
            metadata: new_metadata.clone(),
        }),
    });

    // Add price directive with same metadata
    new_directives.push(DirectiveWrapper {
        directive_type: "price".to_string(),
        date: directive.date.clone(),
        filename: directive.filename.clone(),
        lineno: directive.lineno,
        data: DirectiveData::Price(PriceData {
            currency: state.config.currency.clone(),
            amount: AmountData {
                number: format_decimal(calculated_price),
                currency: valuation_currency,
            },
            metadata: vec![
                (
                    "lastBalance".to_string(),
                    MetaValueData::Number(format_decimal(last_balance)),
                ),
                (
                    "calculatedPrice".to_string(),
                    MetaValueData::Number(format_decimal(calculated_price)),
                ),
            ],
        }),
    });

    (new_directives, errors)
}

/// Parse a valuation amount from a `MetaValueData`.
fn parse_valuation_amount(value: &MetaValueData) -> Option<(Decimal, String)> {
    match value {
        MetaValueData::Amount(amount) => amount
            .number
            .parse::<Decimal>()
            .ok()
            .map(|n| (n, amount.currency.clone())),
        _ => None,
    }
}

/// Round up with given precision.
fn round_up(value: Decimal, decimals: u32) -> Decimal {
    let scale = Decimal::new(1, decimals);
    (value / scale).ceil() * scale
}

/// Round down with given precision.
fn round_down(value: Decimal, decimals: u32) -> Decimal {
    let scale = Decimal::new(1, decimals);
    (value / scale).floor() * scale
}

/// Format a decimal number, stripping trailing zeros.
fn format_decimal(d: Decimal) -> String {
    let s = d.to_string();
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    } else {
        s
    }
}

/// Format a decimal with fixed precision (for synthetic amounts).
fn format_decimal_fixed(d: Decimal, decimals: u32) -> String {
    let scaled = d.round_dp(decimals);
    let s = format!("{:.1$}", scaled, decimals as usize);
    // Trim trailing zeros but keep at least 7 decimal places for consistency
    s.trim_end_matches('0').to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_valuation_config_parsing() {
        let metadata = vec![
            (
                "account".to_string(),
                MetaValueData::String("Assets:Fund".to_string()),
            ),
            (
                "currency".to_string(),
                MetaValueData::String("FUND_USD".to_string()),
            ),
            (
                "pnlAccount".to_string(),
                MetaValueData::String("Income:Fund:PnL".to_string()),
            ),
        ];

        let config = parse_config(&metadata);
        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.account, "Assets:Fund");
        assert_eq!(config.currency, "FUND_USD");
        assert_eq!(config.pnl_account, "Income:Fund:PnL");
    }

    #[test]
    fn test_round_up() {
        let value = Decimal::new(12_345_678, 8); // 0.12345678
        let rounded = round_up(value, 7);
        assert!(rounded >= value);
        // 0.12345678 rounded up to 7 decimals = 0.1234568
        assert_eq!(rounded, Decimal::new(1_234_568, 7));
    }

    #[test]
    fn test_round_down() {
        let value = Decimal::new(12_345_678, 8); // 0.12345678
        let rounded = round_down(value, 7);
        assert!(rounded <= value);
        // 0.12345678 rounded down to 7 decimals = 0.1234567
        assert_eq!(rounded, Decimal::new(1_234_567, 7));
    }

    #[test]
    fn test_fifo_lot_tracking() {
        let config = AccountConfig {
            account: "Assets:Fund".to_string(),
            currency: "FUND_USD".to_string(),
            pnl_account: "Income:PnL".to_string(),
        };

        let mut state = AccountState::new(config);

        // Add first lot at price 1.0
        state.lots.push(CostLot {
            units: Decimal::new(1000, 0),
            cost_per_unit: Decimal::ONE,
            date: "2024-01-10".to_string(),
        });
        state.total_units = Decimal::new(1000, 0);

        // Update price to 0.8
        state.last_price = Decimal::new(8, 1);

        // Add second lot at price 0.8
        let second_units = Decimal::new(500, 0) / state.last_price; // 625
        state.lots.push(CostLot {
            units: second_units,
            cost_per_unit: state.last_price,
            date: "2024-01-13".to_string(),
        });
        state.total_units += second_units;

        assert_eq!(state.lots.len(), 2);
        assert_eq!(state.lots[0].cost_per_unit, Decimal::ONE);
        assert_eq!(state.lots[1].cost_per_unit, Decimal::new(8, 1));
    }

    #[test]
    fn test_format_decimal() {
        assert_eq!(format_decimal(Decimal::new(12345, 4)), "1.2345");
        assert_eq!(format_decimal(Decimal::new(10000, 4)), "1");
        assert_eq!(format_decimal(Decimal::new(12300, 4)), "1.23");
    }

    #[test]
    fn test_format_decimal_fixed() {
        let d = Decimal::new(1000, 0); // 1000
        let formatted = format_decimal_fixed(d, 7);
        assert!(formatted.starts_with("1000."));
    }
}
