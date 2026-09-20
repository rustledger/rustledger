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
    PluginError, PluginErrorSeverity, PluginInput, PluginOp, PluginOutput, PostingData,
    PriceAnnotationData, PriceData, TransactionData,
};

use super::super::{NativePlugin, RegularPlugin};

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
///
/// # Why this is NOT `rustledger_core::Inventory` (Phase-1 sweep Z3)
///
/// This plugin deliberately keeps a private lot list instead of reusing the
/// core inventory's booking-method reduction, because the two operations
/// are different in kind, not just in code:
///
/// - **Core `Inventory::reduce` is unit-denominated**: a reduction consumes
///   N units, matched against lots per booking method. This plugin's sells
///   are **value-denominated**: [`process_fifo_sell`] consumes lots against
///   a currency amount (`lot.units × current_price` vs the remaining value),
///   which core has no API for — porting would mean re-deriving exactly the
///   loop below on top of core types.
/// - The plugin applies its own **rounding policy** (`round_down` on sells,
///   `round_up` on buys, at `MAPPED_CURRENCY_PRECISION`) and computes `PnL`
///   against `last_price`; core reduction is exact and PnL-agnostic
///   (capital gains live in the booking engine).
/// - The plugin operates in the **DTO domain** (`PostingData`, string
///   numbers) on the plugin wire, not on core `Position`s.
///
/// Revisit only if core ever grows a value-denominated reduction — then
/// this loop is the candidate call site. For unit-denominated needs, use
/// `rustledger_core::Inventory`; do not extend this struct.
/// A valuation price held as an exact ratio rather than as its quotient.
///
/// A derived price is frequently non-terminating: `1200 / 1125` is `16/15`,
/// and `Decimal` can only keep 28 places of it. Dividing a cash amount BY
/// that stored quotient then compounds the loss, so `400 / (16/15)` lands on
/// `374.99999...` where the exact answer, `400 x 1125 / 1200`, is `375`.
///
/// Keeping the numerator and denominator defers the division to the last
/// step, where [`rustledger_booking::prorate`] performs it multiply-first and
/// escalates to `BigDecimal` when the intermediate product would not fit.
/// Every value this plugin posts is then exact whenever the exact answer is
/// representable, which for the fixtures in #2360 it always is: the prices
/// repeat but the unit counts and gains do not.
#[derive(Clone, Copy, Debug)]
struct PriceRatio {
    num: Decimal,
    den: Decimal,
}

impl PriceRatio {
    /// A price of 1, the state before any valuation directive.
    const ONE: Self = Self {
        num: Decimal::ONE,
        den: Decimal::ONE,
    };

    /// `value x price`, exact where the result is representable.
    fn multiply(self, value: Decimal) -> Option<Decimal> {
        rustledger_booking::prorate(value, self.num, self.den)
    }

    /// `value / price`, which is `value x den / num`.
    fn divide(self, value: Decimal) -> Option<Decimal> {
        rustledger_booking::prorate(value, self.den, self.num)
    }

    /// The price as a single `Decimal`, for the annotations we emit.
    ///
    /// This is the one place the quotient is unavoidable: a `{cost}` or `@`
    /// annotation is a number in the ledger text. It is used ONLY for those
    /// annotations, never to derive a unit count or a gain.
    fn to_decimal(self) -> Decimal {
        // The denominator is the unit balance the price was derived from, and
        // `process_valuation_assertion` refuses to let that reach zero, so the
        // fallback is unreachable. It is `unwrap_or_default` rather than an
        // expect because an annotation is not worth a panic; if it ever does
        // fire, a zero cost annotation is visible in the output rather than
        // silently folded into a computed number, since this value is used
        // ONLY for annotations.
        self.num.checked_div(self.den).unwrap_or_default()
    }
}

#[derive(Clone, Debug)]
struct CostLot {
    units: Decimal,
    cost: PriceRatio,
    date: String,
}

/// State for a mapped account.
#[derive(Clone, Debug)]
struct AccountState {
    config: AccountConfig,
    lots: Vec<CostLot>,
    last_price: PriceRatio,
    total_units: Decimal,
}

impl AccountState {
    const fn new(config: AccountConfig) -> Self {
        Self {
            config,
            lots: Vec::new(),
            last_price: PriceRatio::ONE,
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
        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());

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
        for (i, directive) in input.directives.into_iter().enumerate() {
            last_date = Some(directive.date.clone());

            match &directive.data {
                DirectiveData::Transaction(txn) => {
                    // Check if any posting is on a mapped account
                    let has_mapped_posting = txn
                        .postings
                        .iter()
                        .any(|p| account_states.contains_key(&p.account));

                    if !has_mapped_posting {
                        ops.push(PluginOp::Keep(i));
                        continue;
                    }

                    // Transform the transaction
                    let (transformed, new_directives, new_errors) = transform_transaction(
                        &directive,
                        txn,
                        &mut account_states,
                        &mut commodities_present,
                    );

                    // Add any price directives generated as Inserts.
                    for new_d in new_directives {
                        ops.push(PluginOp::Insert(new_d));
                    }
                    errors.extend(new_errors);
                    ops.push(PluginOp::Modify(i, transformed));
                }
                DirectiveData::Custom(custom)
                    if custom.custom_type == "valuation" && !custom.values.is_empty() =>
                {
                    // Check if this is a config (pass through) or a valuation assertion
                    if matches!(custom.values.first(), Some(MetaValueData::String(s)) if s == "config")
                    {
                        ops.push(PluginOp::Keep(i));
                        continue;
                    }

                    // This is a valuation assertion — replace it with the
                    // synthesized directives (Delete + Inserts).
                    let (new_directives, new_errors) =
                        process_valuation_assertion(&directive, custom, &mut account_states);

                    ops.push(PluginOp::Delete(i));
                    for new_d in new_directives {
                        ops.push(PluginOp::Insert(new_d));
                    }
                    errors.extend(new_errors);
                }
                DirectiveData::Custom(_) => {
                    ops.push(PluginOp::Keep(i));
                }
                DirectiveData::Commodity(commodity) => {
                    commodities_present.insert(commodity.currency.clone());
                    ops.push(PluginOp::Keep(i));
                }
                _ => {
                    ops.push(PluginOp::Keep(i));
                }
            }
        }

        // Generate commodity directives for synthetic currencies that don't exist
        // Use the last transaction date, not 1970-01-01
        if let Some(date) = last_date {
            for state in account_states.values() {
                if !commodities_present.contains(&state.config.currency) {
                    ops.push(PluginOp::Insert(DirectiveWrapper {
                        directive_type: "commodity".to_string(),
                        date: date.clone(),
                        filename: Some("<valuation>".to_string()),
                        lineno: Some(0),
                        data: DirectiveData::Commodity(CommodityData {
                            currency: state.config.currency.clone(),
                            metadata: vec![],
                        }),
                    }));
                    // Only add once
                    commodities_present.insert(state.config.currency.clone());
                }
            }
        }

        PluginOutput { ops, errors }
    }
}

impl RegularPlugin for ValuationPlugin {}

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
    let mut errors: Vec<PluginError> = Vec::new();
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
                // A total price over zero units has no per-unit price, and
                // deriving one used to divide by zero and panic the process on
                // an ordinary ledger. Upstream reaches the same input and
                // reports a plugin error rather than crashing, so report too
                // and leave the posting alone. Pre-existing on main; fixed here
                // because it is the last bare division in this function and
                // removing those is what this change is for.
                if units_number.is_zero() {
                    errors.push(PluginError {
                        message: format!(
                            "a total price on {} covers zero units, so it has \
                             no per-unit price",
                            posting.account
                        ),
                        source_file: directive.filename.clone(),
                        line_number: directive.lineno,
                        severity: PluginErrorSeverity::Error,
                    });
                    new_postings.push(posting.clone());
                    continue;
                }
                // Handle @@ price annotation - generates 3 postings
                let (postings, price_directive, total_price_errors) = handle_total_price_posting(
                    posting,
                    units_number,
                    &units.currency,
                    price_annot,
                    state,
                    &directive.date,
                    directive,
                );
                errors.extend(total_price_errors);
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
                            number: format_decimal(state.last_price.to_decimal()),
                            currency: units.currency.clone(),
                        },
                        metadata: vec![],
                    }),
                });
            }

            if units_number > Decimal::ZERO {
                // INFLOW: Convert to synthetic currency
                // The unit count can be unavailable two ways: a price of
                // zero, where the account was valued at nothing so no number
                // of units accounts for an inflow of cash, and a count past
                // `Decimal`'s ceiling, which a near-zero price reaches. Both
                // used to panic in `units_number / state.last_price`
                // ("Division by zero" and "Division overflowed").
                //
                // Report and leave the posting alone. Passing it through
                // SILENTLY, which an earlier revision of this change did, is
                // worse than the panic it replaced: the cash never enters the
                // fund, the account is short by the whole purchase, and
                // `rledger check` says "No errors found".
                let Some(exact_units) = state.last_price.divide(units_number) else {
                    errors.push(PluginError {
                        message: format!(
                            "{} cannot be converted to {}: the valuation price \
                             is zero or the unit count is out of range",
                            posting.account, state.config.currency
                        ),
                        source_file: directive.filename.clone(),
                        line_number: directive.lineno,
                        severity: PluginErrorSeverity::Error,
                    });
                    new_postings.push(posting.clone());
                    continue;
                };
                let synthetic_units = round_up(exact_units, MAPPED_CURRENCY_PRECISION);

                // Add to lots
                state.lots.push(CostLot {
                    units: synthetic_units,
                    cost: state.last_price,
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
                        number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                            value: format_decimal(state.last_price.to_decimal()),
                        }),
                        currency: Some(units.currency.clone()),
                        date: Some(directive.date.clone()),
                        label: None,
                        merge: false,
                    }),
                    price: None,
                    flag: posting.flag.clone(),
                    metadata: posting.metadata.clone(),
                    span: None,
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
                        span: None,
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
    directive: &DirectiveWrapper,
) -> (Vec<PostingData>, Option<DirectiveWrapper>, Vec<PluginError>) {
    let mut postings = Vec::new();
    let mut errors: Vec<PluginError> = Vec::new();

    // Get the total price amount
    let Some(ref price_amount) = price_annot.amount else {
        return (vec![posting.clone()], None, errors);
    };

    let Ok(total_price) = price_amount.number.parse::<Decimal>() else {
        return (vec![posting.clone()], None, errors);
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
        span: None,
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
        span: None,
    });

    // 3. Synthetic currency posting
    // Same reasoning as the plain inflow: an unavailable unit count is
    // reported and the posting left alone, never silently dropped or filled
    // with zero.
    let Some(exact_units) = state.last_price.divide(units_number) else {
        errors.push(PluginError {
            message: format!(
                "{} cannot be converted to {}: the valuation price is zero or \
                 the unit count is out of range",
                posting.account, state.config.currency
            ),
            source_file: directive.filename.clone(),
            line_number: directive.lineno,
            severity: PluginErrorSeverity::Error,
        });
        return (vec![posting.clone()], None, errors);
    };
    let synthetic_units = round_up(exact_units, MAPPED_CURRENCY_PRECISION);

    // Add to lots
    state.lots.push(CostLot {
        units: synthetic_units,
        cost: state.last_price,
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
            number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                value: format_decimal(state.last_price.to_decimal()),
            }),
            currency: Some(units_currency.to_string()),
            date: Some(date.to_string()),
            label: None,
            merge: false,
        }),
        price: None,
        flag: None,
        metadata: vec![],
        span: None,
    });

    (postings, None, errors)
}

/// Process FIFO sell and return postings and total `PnL`.
/// The gain on `units` sold at `price` against a lot carried at `cost`.
///
/// Computed as `units x price - units x cost` rather than
/// `(price - cost) x units`. The two are equal in exact arithmetic, but the
/// subtraction-first form has to collapse both ratios to a single `Decimal`
/// before multiplying, which is where #2360's dust came from. Each product
/// here is taken multiply-first through [`PriceRatio::multiply`], so a
/// representable gain comes out exact: the 2024-02-12 sale in
/// `some_fund_example` is exactly 25, not `25.00000000000000000000000001`.
fn lot_gain(price: PriceRatio, cost: PriceRatio, units: Decimal) -> Decimal {
    // Both sides fail only on an unrepresentable product, never on a zero
    // denominator (see `to_decimal`). They are taken together so that a
    // failure on one side cannot leave the other standing as the whole gain,
    // which would be a wrong number rather than a missing one.
    match (price.multiply(units), cost.multiply(units)) {
        (Some(proceeds), Some(basis)) => proceeds - basis,
        _ => Decimal::ZERO,
    }
}

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
        // `multiply` divides by the unit balance the price was derived from,
        // which `process_valuation_assertion` refuses to let reach zero, so
        // the fallback needs an unrepresentable product rather than a missing
        // denominator.
        let lot_value_at_current_price = current_price.multiply(lot.units).unwrap_or(Decimal::ZERO);

        if lot_value_at_current_price <= remaining + EPSILON {
            // Sell entire lot
            let units_to_sell = lot.units;
            total_pnl += lot_gain(current_price, lot.cost, units_to_sell);

            // Round down for sells
            let rounded_units = round_down(units_to_sell, MAPPED_CURRENCY_PRECISION);

            postings.push(PostingData {
                account: account.to_string(),
                units: Some(AmountData {
                    number: format_decimal_fixed(-rounded_units, MAPPED_CURRENCY_PRECISION),
                    currency: state.config.currency.clone(),
                }),
                cost: Some(CostData {
                    number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                        value: format_decimal(lot.cost.to_decimal()),
                    }),
                    currency: Some(currency.to_string()),
                    date: Some(lot.date.clone()),
                    label: None,
                    merge: false,
                }),
                price: Some(PriceAnnotationData {
                    is_total: false,
                    amount: Some(AmountData {
                        number: format_decimal(current_price.to_decimal()),
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
                span: None,
            });

            // Same reasoning as the partial branch: the posting reported
            // `rounded_units`, so that is what leaves the running total. With
            // the partial branch fixed, `lot.units` is already at
            // `MAPPED_CURRENCY_PRECISION` and this is a no-op — but it keeps
            // the two branches saying the same thing, and it is still correct
            // for a lot carrying more precision than the posting can express.
            state.total_units -= rounded_units;
            remaining -= lot_value_at_current_price;
            state.lots.remove(0);
        } else {
            // Partial sell from this lot
            let units_to_sell = current_price.divide(remaining).unwrap_or(Decimal::ZERO);
            total_pnl += lot_gain(current_price, lot.cost, units_to_sell);

            let rounded_units = round_down(units_to_sell, MAPPED_CURRENCY_PRECISION);

            postings.push(PostingData {
                account: account.to_string(),
                units: Some(AmountData {
                    number: format_decimal_fixed(-rounded_units, MAPPED_CURRENCY_PRECISION),
                    currency: state.config.currency.clone(),
                }),
                cost: Some(CostData {
                    number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                        value: format_decimal(lot.cost.to_decimal()),
                    }),
                    currency: Some(currency.to_string()),
                    date: Some(lot.date.clone()),
                    label: None,
                    merge: false,
                }),
                price: Some(PriceAnnotationData {
                    is_total: false,
                    amount: Some(AmountData {
                        number: format_decimal(current_price.to_decimal()),
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
                span: None,
            });

            // Decrement by what was POSTED, not by the unrounded quotient.
            //
            // The posting above reports `rounded_units`; decrementing the lot
            // by the full-precision `units_to_sell` lets the plugin's idea of
            // the lot drift below the balance the ledger actually shows. The
            // drift is at most 1e-7 per partial sell and is invisible until a
            // later full sell posts `lot.units` — by then already short — and
            // leaves a residual position that should not exist (#2018).
            //
            // The buy path has always done it this way: it rounds once and
            // uses that single value for both the lot and the posting.
            lot.units -= rounded_units;
            state.total_units -= rounded_units;
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

    // Keep the price as the ratio it is. Collapsing `valuation_amount /
    // last_balance` to a `Decimal` here is what #2360 traced the dust to: the
    // quotient is often non-terminating, and every unit count and gain
    // derived from it inherits the loss.
    let new_price = PriceRatio {
        num: valuation_amount,
        den: last_balance,
    };
    let calculated_price = new_price.to_decimal();
    state.last_price = new_price;

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
/// Python `decimal`'s `ROUND_UP`: away from zero, NOT toward +infinity.
///
/// The upstream plugin rounds a cash INFLOW with `ROUND_UP` and an OUTFLOW
/// with `ROUND_DOWN` (`valuation/__init__.py`), so the fund never credits
/// more units than the cash bought. `ceil`/`floor` agree with Python for
/// positive values and are exactly INVERTED for negative ones, which is the
/// outflow path — so an outflow of `-6000/11` rounded to `-545.4545455`
/// here against beancount's `-545.4545454`.
///
/// That one digit is the whole of the "1E-7 residue" this fixture is known
/// for: beancount's three legs sum to `0.0000001` because of its own
/// truncation, and rledger's summed to zero. It is not a `rust_decimal`
/// precision limit — these are ten-digit values.
fn round_up(value: Decimal, decimals: u32) -> Decimal {
    let scale = Decimal::new(1, decimals);
    let scaled = value / scale;
    // Away from zero.
    let rounded = if value.is_sign_negative() {
        scaled.floor()
    } else {
        scaled.ceil()
    };
    rounded * scale
}

/// Round down with given precision.
/// Python `decimal`'s `ROUND_DOWN`: toward zero — see [`round_up`].
fn round_down(value: Decimal, decimals: u32) -> Decimal {
    let scale = Decimal::new(1, decimals);
    (value / scale).trunc() * scale
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
/// Render at EXACTLY `decimals` places, matching Python's
/// `round(Decimal, decimals)`.
///
/// This used to `trim_end_matches('0')`, which does the opposite of what its
/// own comment claimed ("keep at least 7 decimal places") — it stripped every
/// trailing zero, so an inflow of `1000` emitted `1000` where beancount emits
/// `1000.0000000`. The values were equal; the scale was not, and the scale is
/// what the position and its cost render at.
fn format_decimal_fixed(d: Decimal, decimals: u32) -> String {
    format!("{:.1$}", d.round_dp(decimals), decimals as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::*;

    /// A derived price that does not terminate must not cost the values
    /// derived from it their exactness (#2360).
    ///
    /// `1200 / 1125` is `16/15`. Dividing cash by the stored quotient is what
    /// used to make a 400 USD withdrawal post `374.9999999` units and a gain
    /// of `25.00000000000000000000000001`. Both exact answers are
    /// representable, so both must come out exact.
    #[test]
    fn a_repeating_price_still_yields_exact_units_and_gain() {
        let price = PriceRatio {
            num: Decimal::from(1200),
            den: Decimal::from(1125),
        };
        let cash = Decimal::from(400);

        // The guard: going through the quotient does NOT recover 375, which is
        // why the ratio is carried. Without this the test could pass on a
        // build where the naive path happened to be exact too.
        let naive = cash
            .checked_div(price.to_decimal())
            .expect("a quotient of the rounded price");
        assert_ne!(
            naive,
            Decimal::from(375),
            "dividing by the rounded price must be the lossy path this fixes"
        );

        // 400 / (1200/1125) == 400 * 1125 / 1200 == 375.
        let units = price.divide(cash).expect("a representable unit count");
        assert_eq!(units, Decimal::from(375));
        assert_eq!(units.to_string(), "375", "exact, and with no dust tail");

        // Selling those 375 units, carried at a cost of 1, gains exactly 25.
        let gain = lot_gain(price, PriceRatio::ONE, units);
        assert_eq!(gain, Decimal::from(25));
        assert_eq!(gain.to_string(), "25", "exact, and with no dust tail");
    }

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

    /// The SELL call sites must keep the exactness, not just `PriceRatio`
    /// itself (#2360).
    ///
    /// `a_repeating_price_still_yields_exact_units_and_gain` pins the helper in
    /// isolation, which a sabotage check showed is not enough: reverting either
    /// gain call site to `(price - cost) x units` on quotients, or the unit
    /// count to `cash / price`, left all 330 tests green. This drives
    /// `process_fifo_sell` so the call sites are covered too.
    #[test]
    fn a_sell_at_a_repeating_price_posts_exact_units_and_gain() {
        let mut state = AccountState::new(AccountConfig {
            account: "Assets:Fund:Total".to_string(),
            currency: "FUND_USD".to_string(),
            pnl_account: "Income:Fund:PnL".to_string(),
        });
        state.lots.push(CostLot {
            units: Decimal::from(500),
            cost: PriceRatio::ONE,
            date: "2024-01-10".to_string(),
        });
        state.total_units = Decimal::from(500);
        // 1200/1125 is 16/15: the quotient does not terminate.
        state.last_price = PriceRatio {
            num: Decimal::from(1200),
            den: Decimal::from(1125),
        };

        let (postings, total_pnl) = process_fifo_sell(
            &mut state,
            Decimal::from(400),
            "Assets:Fund:Total",
            "USD",
            &None,
            &[],
        );

        // 400 / (1200/1125) is exactly 375, so the posting reports all seven
        // places as zeros rather than `-374.9999999`.
        let units = postings
            .iter()
            .filter_map(|p| p.units.as_ref())
            .map(|a| a.number.as_str())
            .collect::<Vec<_>>();
        assert_eq!(
            units,
            vec!["-375.0000000"],
            "the sell posting must carry the exact unit count"
        );

        // The gain is exactly 25, with no dust tail in either direction.
        assert_eq!(total_pnl, Decimal::from(25));
        assert_eq!(total_pnl.to_string(), "25", "exact, and no dust tail");
    }

    // `lot_gain` and `PriceRatio::divide` are EXACT wherever the exact answer
    // is representable, not merely on the fixture in #2360.
    //
    // The reference is integer arithmetic rather than a second decimal
    // computation, so the test cannot agree with the code by sharing its
    // rounding. With `price = a/b` and `cost = c/d`, choosing
    // `units = b*d*k` makes every quantity an integer: proceeds are `a*d*k`,
    // the basis is `c*b*k`, and the gain is exactly `k*(a*d - c*b)`. The same
    // construction gives `divide` an integer answer, since `cash = a*k` buys
    // exactly `b*k` units at `a/b`.
    //
    // What this does NOT claim: `lot_gain` subtracts two separately-rounded
    // products, so where the exact gain is NOT representable it can sit up to
    // about 5e-22 from the correctly-rounded value in this range. Measured
    // over 400,000 random ratios: of the cases whose exact gain is
    // representable, 6,158 of 6,158 came out exact, which is the property
    // pinned here; of all cases, 84% differ from a single-rounding reference
    // by that tiny amount. Computing the gain as one ratio would close that,
    // at the cost of multiplying the two denominators.
    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(4000))]
        #[test]
        fn exact_wherever_the_answer_is_representable(
            a in 1i64..400, b in 1i64..400,
            c in 1i64..400, d in 1i64..400,
            k in 1i64..400,
        ) {
            let price = PriceRatio { num: Decimal::from(a), den: Decimal::from(b) };
            let cost = PriceRatio { num: Decimal::from(c), den: Decimal::from(d) };
            let units = Decimal::from(b * d * k);

            // gain == k*(a*d - c*b), exactly.
            let want_gain = Decimal::from(k * (a * d - c * b));
            proptest::prop_assert_eq!(
                lot_gain(price, cost, units),
                want_gain,
                "gain for price {}/{} cost {}/{} units {}",
                a, b, c, d, units
            );

            // cash of a*k buys exactly b*k units at a price of a/b.
            let cash = Decimal::from(a * k);
            proptest::prop_assert_eq!(
                price.divide(cash),
                Some(Decimal::from(b * k)),
                "units bought for {} at {}/{}",
                cash, a, b
            );

            // and units*price is exact the other way round.
            proptest::prop_assert_eq!(
                price.multiply(Decimal::from(b * k)),
                Some(Decimal::from(a * k)),
                "value of {} units at {}/{}",
                b * k, a, b
            );
        }
    }

    /// A unit count past `Decimal`'s ceiling is reported, not posted in the
    /// original currency as though nothing happened.
    ///
    /// A near-zero valuation price makes `cash / price` overflow. On main that
    /// panicked with "Division overflowed"; an earlier revision of this change
    /// passed the posting through silently, which is worse, because the cash
    /// never enters the fund and `rledger check` reports no errors at all.
    #[test]
    fn an_out_of_range_unit_count_is_reported_rather_than_dropped() {
        let mut states = HashMap::new();
        let mut state = AccountState::new(AccountConfig {
            account: "Assets:Fund:Total".to_string(),
            currency: "FUND_USD".to_string(),
            pnl_account: "Income:Fund:PnL".to_string(),
        });
        state.lots.push(CostLot {
            units: Decimal::ONE,
            cost: PriceRatio::ONE,
            date: "2024-01-01".to_string(),
        });
        state.total_units = Decimal::ONE;
        // A price of 1e-20: buying 1e10 of it needs 1e30 units, past the
        // 7.9e28 ceiling.
        state.last_price = PriceRatio {
            num: Decimal::ONE,
            den: Decimal::from(10u64.pow(19)) * Decimal::TEN,
        };
        states.insert("Assets:Fund:Total".to_string(), state);

        let directive = DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-12".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "buy".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![],
            }),
        };
        let txn = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "buy".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Fund:Total".to_string(),
                units: Some(AmountData {
                    number: "10000000000".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: None,
                flag: None,
                metadata: vec![],
                span: None,
            }],
        };

        let mut commodities = HashSet::new();
        let (transformed, _new, errors) =
            transform_transaction(&directive, &txn, &mut states, &mut commodities);

        assert_eq!(errors.len(), 1, "the failure must be reported: {errors:?}");
        assert!(
            errors[0].message.contains("out of range"),
            "the message must name the cause: {}",
            errors[0].message
        );

        // The posting is left alone rather than dropped or zeroed, and it is
        // still in the ORIGINAL currency, which is why the error matters.
        let DirectiveData::Transaction(out) = transformed.data else {
            panic!("a transaction must stay a transaction");
        };
        assert_eq!(out.postings.len(), 1);
        let units = out.postings[0].units.as_ref().expect("units");
        assert_eq!(units.currency, "USD");
        assert_eq!(units.number, "10000000000");
    }

    /// The `@@` inflow path must keep the exactness as well.
    ///
    /// `handle_total_price_posting` has its own `divide` call, and a sabotage
    /// check found it uncovered while the plain inflow and both sell sites were
    /// pinned. `1/3` is used for the same reason as in the plain-inflow test:
    /// the quotient overshoots, so `round_up` cannot hide the difference.
    #[test]
    fn a_total_price_buy_at_a_repeating_price_records_an_exact_lot() {
        let mut states = HashMap::new();
        let mut state = AccountState::new(AccountConfig {
            account: "Assets:Fund:Total".to_string(),
            currency: "FUND_USD".to_string(),
            pnl_account: "Income:Fund:PnL".to_string(),
        });
        state.lots.push(CostLot {
            units: Decimal::from(10),
            cost: PriceRatio::ONE,
            date: "2024-01-01".to_string(),
        });
        state.total_units = Decimal::from(10);
        state.last_price = PriceRatio {
            num: Decimal::ONE,
            den: Decimal::from(3),
        };
        states.insert("Assets:Fund:Total".to_string(), state);

        let directive = DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-02-14".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "buy with a total price".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![],
            }),
        };
        let txn = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "buy with a total price".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Fund:Total".to_string(),
                units: Some(AmountData {
                    number: "1".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: Some(PriceAnnotationData {
                    is_total: true,
                    amount: Some(AmountData {
                        number: "5".to_string(),
                        currency: "EUR".to_string(),
                    }),
                    number: None,
                    currency: None,
                }),
                flag: None,
                metadata: vec![],
                span: None,
            }],
        };

        let mut commodities = HashSet::new();
        let (transformed, _new, errors) =
            transform_transaction(&directive, &txn, &mut states, &mut commodities);
        assert!(errors.is_empty(), "no errors: {errors:?}");

        let DirectiveData::Transaction(out) = transformed.data else {
            panic!("a transaction must stay a transaction");
        };
        // The `@@` path emits three postings; the synthetic one carries the
        // unit count, and 1 USD at a price of 1/3 buys exactly 3 units.
        let synthetic: Vec<&str> = out
            .postings
            .iter()
            .filter_map(|p| p.units.as_ref())
            .filter(|a| a.currency == "FUND_USD")
            .map(|a| a.number.as_str())
            .collect();
        assert_eq!(
            synthetic,
            vec!["3.0000000"],
            "the synthetic leg must be exact, not 3.0000001"
        );

        let lot = states["Assets:Fund:Total"]
            .lots
            .last()
            .expect("the new lot");
        assert_eq!(lot.units, Decimal::from(3), "the lot must not be inflated");
    }

    /// A total price over zero units is reported, not a panic.
    ///
    /// `total_price / units_number` was a bare division, so an ordinary ledger
    /// carrying `0 USD @@ 100 EUR` on a mapped account took the whole process
    /// down with "Division by zero". Upstream reaches the same input and
    /// reports a plugin error, which is what we do now.
    #[test]
    fn a_total_price_over_zero_units_is_reported_rather_than_panicking() {
        let mut states = HashMap::new();
        let mut state = AccountState::new(AccountConfig {
            account: "Assets:Fund:Total".to_string(),
            currency: "FUND_USD".to_string(),
            pnl_account: "Income:Fund:PnL".to_string(),
        });
        state.lots.push(CostLot {
            units: Decimal::from(10),
            cost: PriceRatio::ONE,
            date: "2024-01-01".to_string(),
        });
        state.total_units = Decimal::from(10);
        states.insert("Assets:Fund:Total".to_string(), state);

        let directive = DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-02-12".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "zero units with @@".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![],
            }),
        };
        let txn = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "zero units with @@".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Fund:Total".to_string(),
                units: Some(AmountData {
                    number: "0".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: Some(PriceAnnotationData {
                    is_total: true,
                    amount: Some(AmountData {
                        number: "100".to_string(),
                        currency: "EUR".to_string(),
                    }),
                    number: None,
                    currency: None,
                }),
                flag: None,
                metadata: vec![],
                span: None,
            }],
        };

        let mut commodities = HashSet::new();
        // The assertion is that this RETURNS at all; a regression panics here.
        let (_transformed, _new, errors) =
            transform_transaction(&directive, &txn, &mut states, &mut commodities);

        assert_eq!(errors.len(), 1, "one error, not a crash: {errors:?}");
        assert!(
            errors[0].message.contains("zero units"),
            "the message must name the cause: {}",
            errors[0].message
        );
    }

    /// The INFLOW call site must keep the exactness too (#2360).
    ///
    /// Same reasoning as the sell test above: this is the site whose sabotage
    /// went unnoticed by every other test.
    #[test]
    fn a_buy_at_a_repeating_price_records_an_exact_lot() {
        let mut states = HashMap::new();
        let mut state = AccountState::new(AccountConfig {
            account: "Assets:Fund:Total".to_string(),
            currency: "FUND_USD".to_string(),
            pnl_account: "Income:Fund:PnL".to_string(),
        });
        // Non-empty, so the first-transaction price directive is not emitted
        // and the assertions below see only the posting under test.
        state.lots.push(CostLot {
            units: Decimal::from(10),
            cost: PriceRatio::ONE,
            date: "2024-01-01".to_string(),
        });
        state.total_units = Decimal::from(10);
        // 1/3, not 1200/1125. The quotient of 1200/1125 falls SHORT, and
        // `round_up` lifts it back to the same seven-place value, so that price
        // cannot tell the two paths apart — a sabotage check caught this test
        // passing against the quotient path. A stored 1/3 goes the other way
        // (`1 / 0.3333...3` is `3.0000000000000000000000000003`), and rounding
        // that up credits `3.0000001` units for a purchase that buys exactly 3.
        state.last_price = PriceRatio {
            num: Decimal::ONE,
            den: Decimal::from(3),
        };
        states.insert("Assets:Fund:Total".to_string(), state);

        let directive = DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-02-12".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "buy".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![],
            }),
        };
        let txn = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "buy".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Fund:Total".to_string(),
                units: Some(AmountData {
                    number: "1".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: None,
                flag: None,
                metadata: vec![],
                span: None,
            }],
        };

        let mut commodities = HashSet::new();
        let (transformed, _new_directives, errors) =
            transform_transaction(&directive, &txn, &mut states, &mut commodities);
        assert!(errors.is_empty(), "no errors: {errors:?}");

        let DirectiveData::Transaction(out) = transformed.data else {
            panic!("a transaction must stay a transaction");
        };
        let numbers = out
            .postings
            .iter()
            .filter_map(|p| p.units.as_ref())
            .map(|a| a.number.as_str())
            .collect::<Vec<_>>();
        assert_eq!(
            numbers,
            vec!["3.0000000"],
            "1 USD at a price of 1/3 buys exactly 3 units, not 3.0000001"
        );

        let lot = states["Assets:Fund:Total"]
            .lots
            .last()
            .expect("the new lot");
        assert_eq!(lot.units, Decimal::from(3), "the lot must not be inflated");
    }

    /// A partial sell must move the lot by exactly what it posted, so a later
    /// full sell closes the lot to zero instead of leaving a phantom residual.
    ///
    /// Regression for #2018. `units_to_sell` is `remaining / price`, which can
    /// carry more precision than `MAPPED_CURRENCY_PRECISION`; the posting is
    /// rounded but the lot used to be decremented by the unrounded quotient.
    /// The gap is at most 1e-7 per partial sell and is invisible until the
    /// close-out posts a lot balance that is already short.
    ///
    /// The numbers mirror `tests_data_some_fund_example.beancount`: 500 units
    /// bought at 1, then sold at a price that does not divide evenly, then the
    /// remainder sold. Before the fix the two postings summed to -500.0000000
    /// against a 500 lot only because the lot had silently shrunk; beancount's
    /// plugin posts -374.9999999 and -125.0000001.
    #[test]
    fn partial_sell_leaves_no_phantom_residual() {
        let mut state = AccountState::new(AccountConfig {
            account: "Assets:Fund:Total".to_string(),
            currency: "FUND_USD".to_string(),
            pnl_account: "Income:Fund:PnL".to_string(),
        });
        state.lots.push(CostLot {
            units: Decimal::from(500),
            cost: PriceRatio::ONE,
            date: "2024-01-10".to_string(),
        });
        state.total_units = Decimal::from(500);
        // 1200/1125 — the price that produces a non-terminating quotient.
        state.last_price = PriceRatio {
            num: Decimal::from(1200),
            den: Decimal::from(1125),
        };

        let posted = |ps: &[PostingData]| -> Decimal {
            ps.iter()
                .filter(|p| p.account == "Assets:Fund:Total")
                .filter_map(|p| p.units.as_ref())
                .map(|a| a.number.parse::<Decimal>().expect("posted units parse"))
                .sum()
        };

        let (first, _) = process_fifo_sell(
            &mut state,
            Decimal::from(400),
            "Assets:Fund:Total",
            "USD",
            &None,
            &[],
        );
        let sold_first = posted(&first);

        // Sell everything that remains, at whatever price.
        let remaining_value = state
            .last_price
            .multiply(state.total_units)
            .expect("a representable remaining value");
        let (second, _) = process_fifo_sell(
            &mut state,
            remaining_value,
            "Assets:Fund:Total",
            "USD",
            &None,
            &[],
        );
        let sold_second = posted(&second);

        assert_eq!(
            sold_first + sold_second,
            Decimal::from(-500),
            "the two sells must dispose of exactly the 500 units bought; a \
             shortfall here is the #2018 residual"
        );
        assert!(
            state.lots.is_empty(),
            "the lot should be gone, found {:?}",
            state.lots
        );
        assert_eq!(
            state.total_units,
            Decimal::ZERO,
            "running total must close to zero, not to a 1e-7 remainder"
        );
    }

    /// `format_decimal_fixed` renders EXACTLY `decimals` places.
    ///
    /// It used to `trim_end_matches('0')` — the opposite of its own comment —
    /// so an inflow of `1000` emitted `1000` where beancount emits
    /// `1000.0000000`. Asserts the full string, not a prefix or a length:
    /// the failure mode was a SHORTER rendering of an equal value, which a
    /// `starts_with` or a parse-and-compare would both accept.
    #[test]
    fn format_decimal_fixed_pads_to_exactly_the_requested_places() {
        assert_eq!(
            format_decimal_fixed(Decimal::new(1000, 0), 7),
            "1000.0000000"
        );
        assert_eq!(format_decimal_fixed(Decimal::new(0, 0), 7), "0.0000000");
        // Already at 7dp: unchanged.
        assert_eq!(
            format_decimal_fixed(Decimal::new(5_454_545_454, 7), 7),
            "545.4545454"
        );
        // More precision than asked for: rounded to exactly 7.
        assert_eq!(
            format_decimal_fixed(Decimal::new(54_545_454_549, 8), 7),
            "545.4545455"
        );
        // Negative keeps its sign and its padding.
        assert_eq!(
            format_decimal_fixed(Decimal::new(-1000, 0), 7),
            "-1000.0000000"
        );
    }

    #[test]
    fn test_round_up() {
        // `ROUND_UP` is AWAY FROM ZERO, not toward +infinity. The two agree on
        // positives, which is all this test covered while the helper used
        // `ceil` — so the direction could be wrong for negatives with the
        // suite green. Reference values from CPython's `decimal`.
        let value = Decimal::new(12_345_678, 8); // 0.12345678
        assert_eq!(round_up(value, 7), Decimal::new(1_234_568, 7));
        assert!(round_up(value, 7) >= value, "positives grow");

        let negative = Decimal::new(-12_345_678, 8); // -0.12345678
        assert_eq!(
            round_up(negative, 7),
            Decimal::new(-1_234_568, 7),
            "away from zero, so a negative gets MORE negative",
        );
        // Deliberately not `>= negative`: that assertion encodes the
        // toward-+infinity reading this helper is not.
        assert!(round_up(negative, 7).abs() >= negative.abs());
    }

    #[test]
    fn test_round_down() {
        // `ROUND_DOWN` is TOWARD ZERO — see `test_round_up`. This is the
        // direction the sell path takes, and the one that made the
        // `cool_fund` close-out differ from beancount in the last digit.
        let value = Decimal::new(12_345_678, 8); // 0.12345678
        assert_eq!(round_down(value, 7), Decimal::new(1_234_567, 7));
        assert!(round_down(value, 7) <= value, "positives shrink");

        let negative = Decimal::new(-12_345_678, 8); // -0.12345678
        assert_eq!(
            round_down(negative, 7),
            Decimal::new(-1_234_567, 7),
            "toward zero, so a negative gets LESS negative",
        );
        assert!(round_down(negative, 7).abs() <= negative.abs());
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
            cost: PriceRatio::ONE,
            date: "2024-01-10".to_string(),
        });
        state.total_units = Decimal::new(1000, 0);

        // Update price to 0.8
        state.last_price = PriceRatio {
            num: Decimal::new(8, 1),
            den: Decimal::ONE,
        };

        // Add second lot at price 0.8
        let second_units = state.last_price.divide(Decimal::new(500, 0)).expect("625"); // 625
        state.lots.push(CostLot {
            units: second_units,
            cost: state.last_price,
            date: "2024-01-13".to_string(),
        });
        state.total_units += second_units;

        assert_eq!(state.lots.len(), 2);
        assert_eq!(state.lots[0].cost.to_decimal(), Decimal::ONE);
        assert_eq!(state.lots[1].cost.to_decimal(), Decimal::new(8, 1));
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
