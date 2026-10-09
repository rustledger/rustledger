//! Check that assigned short options fold the premium into the stock leg.
//!
//! When a short option is assigned, the premium is not a separate gain. For
//! a short put, the stock's basis is strike × shares − premium. For a short
//! call, the sale proceeds are strike × shares + premium. This plugin checks
//! that the stock leg of an assignment says so.
//!
//! An **assignment** is a transaction that reduces a short position in an
//! OCC option (see [`super::option_symbol`]) and also moves the option's
//! root commodity — stock units rise for a put, fall for a call. Ordinary
//! closes, long options, cash-settled index options, and assignments split
//! across two transactions are not checked.
//!
//! The plugin runs after booking, so a closing `{}` posting carries the cost
//! of the lot it closed — the premium. Each assignment gets at most one
//! error, from the first rule that fails:
//!
//! 1. Stock units = 100 × contracts.
//! 2. The option leg realizes no gain (no price, or a price equal to cost).
//! 3. The stock basis (put) or proceeds (call) match within half a cent per
//!    share, compared as totals across every booked lot.
//!
//! The plugin only reports: every directive is kept and nothing is inserted.

use std::collections::BTreeMap;
use std::str::FromStr;

use rust_decimal::Decimal;

use crate::types::{
    CostNumberData, DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput, PostingData,
    PriceAnnotationView,
};

use super::super::{NativePlugin, RegularPlugin};
use super::option_symbol::{OptionRight, parse_occ};

/// Shares delivered per standard equity option contract.
const SHARES_PER_CONTRACT: u32 = 100;

/// Plugin that checks the stock leg of short-option assignments.
pub struct CheckOptionAssignmentPlugin;

/// Parse a posting's units as a number.
fn units_of(posting: &PostingData) -> Option<Decimal> {
    Decimal::from_str(&posting.units.as_ref()?.number).ok()
}

/// Total cost of a posting's units, as a positive number.
fn cost_total(posting: &PostingData, units: Decimal) -> Option<Decimal> {
    let parse = |s: &str| Decimal::from_str(s).ok();
    let total = match posting.cost.as_ref()?.number.as_ref()? {
        CostNumberData::PerUnit { value } => parse(value)? * units,
        CostNumberData::Total { value } | CostNumberData::PerUnitFromTotal { total: value, .. } => {
            parse(value)?
        }
        CostNumberData::Compound { per_unit, total } => parse(per_unit)? * units + parse(total)?,
    };
    Some(total.abs())
}

/// Total price of a posting's units, as a positive number. `None` when the
/// posting has no price or an incomplete one.
fn price_total(posting: &PostingData, units: Decimal) -> Option<Decimal> {
    let total = match posting.price.as_ref()?.view() {
        PriceAnnotationView::Unit(a) => Decimal::from_str(&a.number).ok()? * units,
        PriceAnnotationView::Total(a) => Decimal::from_str(&a.number).ok()?,
        PriceAnnotationView::UnitIncomplete { .. }
        | PriceAnnotationView::TotalIncomplete { .. } => {
            return None;
        }
    };
    Some(total.abs())
}

/// Option legs of one transaction that close short contracts on one underlying.
#[derive(Default)]
struct Closing {
    symbols: Vec<String>,
    rights: Vec<OptionRight>,
    contracts: Decimal,
    /// Σ strike × shares.
    strike_value: Decimal,
    premium: Decimal,
    premium_realized: bool,
    /// Distinct strikes among the closed contracts.
    strikes: Vec<Decimal>,
    currency: Option<String>,
}

impl NativePlugin for CheckOptionAssignmentPlugin {
    fn name(&self) -> &'static str {
        "check_option_assignment"
    }

    fn description(&self) -> &'static str {
        "Check that assigned short options fold the premium into the stock leg"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut order: Vec<usize> = (0..input.directives.len()).collect();
        order.sort_by(|&a, &b| input.directives[a].date.cmp(&input.directives[b].date));

        let shares_per_contract = Decimal::from(SHARES_PER_CONTRACT);
        let mut net: BTreeMap<(String, String), Decimal> = BTreeMap::new();
        let mut errors = Vec::new();

        for &i in &order {
            let wrapper = &input.directives[i];
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                continue;
            };

            // Option legs that close short contracts, grouped by underlying.
            let mut closings: BTreeMap<String, Closing> = BTreeMap::new();
            for posting in &txn.postings {
                let Some(units) = units_of(posting) else {
                    continue;
                };
                let symbol = &posting.units.as_ref().expect("units parsed").currency;
                let Some(occ) = parse_occ(symbol) else {
                    continue;
                };
                let held = net
                    .get(&(posting.account.clone(), symbol.clone()))
                    .copied()
                    .unwrap_or_default();
                if held >= Decimal::ZERO || units <= Decimal::ZERO {
                    continue;
                }
                let Some(premium) = cost_total(posting, units) else {
                    continue;
                };
                let c = closings.entry(occ.root.clone()).or_default();
                if !c.symbols.contains(symbol) {
                    c.symbols.push(symbol.clone());
                }
                if !c.strikes.contains(&occ.strike) {
                    c.strikes.push(occ.strike);
                }
                c.rights.push(occ.right);
                c.contracts += units;
                c.strike_value += occ.strike * units * shares_per_contract;
                c.premium += premium;
                c.currency = c
                    .currency
                    .take()
                    .or_else(|| posting.cost.as_ref().and_then(|k| k.currency.clone()));
                if let Some(price) = price_total(posting, units) {
                    c.premium_realized |= price != premium;
                }
            }

            for (root, c) in &closings {
                let right = c.rights[0];
                if c.rights.iter().any(|r| *r != right) {
                    continue;
                }
                let stock: Vec<(&PostingData, Decimal)> = txn
                    .postings
                    .iter()
                    .filter(|p| p.units.as_ref().is_some_and(|u| &u.currency == root))
                    .filter_map(|p| units_of(p).map(|u| (p, u)))
                    .collect();
                let stock_units: Decimal = stock.iter().map(|(_, u)| *u).sum();
                let assigned = match right {
                    OptionRight::Put => stock_units > Decimal::ZERO,
                    OptionRight::Call => stock_units < Decimal::ZERO,
                };
                if !assigned {
                    continue;
                }

                let label = c.symbols.join(", ");
                let currency = c.currency.clone().unwrap_or_default();
                let shares = stock_units.abs();
                let expected_shares = c.contracts * shares_per_contract;
                let breakdown_strike = if c.strikes.len() == 1 {
                    format!("strike {} × {}", c.strikes[0], expected_shares.normalize())
                } else {
                    format!("strike value {:.2}", c.strike_value)
                };

                let message = if shares != expected_shares {
                    Some(format!(
                        "{label} assignment: {} contract(s) but {} {root}; expected {}",
                        c.contracts.normalize(),
                        shares.normalize(),
                        expected_shares.normalize()
                    ))
                } else if c.premium_realized {
                    Some(format!(
                        "{label} assignment: premium realized on the option leg; close it at cost and fold the premium into the {root} leg"
                    ))
                } else {
                    let tolerance = Decimal::new(5, 3) * shares;
                    match right {
                        OptionRight::Put => {
                            let expected = c.strike_value - c.premium;
                            let basis: Option<Decimal> =
                                stock.iter().map(|(p, u)| cost_total(p, *u)).sum();
                            basis.and_then(|basis| {
                                ((basis - expected).abs() > tolerance).then(|| {
                                    format!(
                                        "{label} assignment: {root} basis {basis:.2} {currency}, expected {expected:.2} {currency} ({breakdown_strike} − premium {:.2})",
                                        c.premium
                                    )
                                })
                            })
                        }
                        OptionRight::Call => {
                            let expected = c.strike_value + c.premium;
                            let proceeds: Option<Decimal> =
                                stock.iter().map(|(p, u)| price_total(p, *u)).sum();
                            Some(match proceeds {
                                None => format!(
                                    "{label} assignment: {root} sale has no price; expected proceeds {expected:.2} {currency}"
                                ),
                                Some(proceeds) if (proceeds - expected).abs() > tolerance => {
                                    format!(
                                        "{label} assignment: {root} proceeds {proceeds:.2} {currency}, expected {expected:.2} {currency} ({breakdown_strike} + premium {:.2})",
                                        c.premium
                                    )
                                }
                                Some(_) => continue,
                            })
                        }
                    }
                };

                if let Some(message) = message {
                    let mut error = PluginError::error(message);
                    if let (Some(file), Some(line)) = (&wrapper.filename, wrapper.lineno) {
                        error = error.at(file.clone(), line);
                    }
                    errors.push(error);
                }
            }

            // Apply this transaction's option legs to the running positions.
            for posting in &txn.postings {
                let Some(units) = units_of(posting) else {
                    continue;
                };
                let symbol = &posting.units.as_ref().expect("units parsed").currency;
                if parse_occ(symbol).is_some() {
                    *net.entry((posting.account.clone(), symbol.clone()))
                        .or_default() += units;
                }
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for CheckOptionAssignmentPlugin {}
