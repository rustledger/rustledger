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
//!    share, compared as totals across every booked lot. A put's stock leg
//!    needs a cost, and a call's a price; a call that opens a short stock
//!    position (no stock held in that account before) may give its
//!    proceeds as the short lot's cost instead.
//!
//! Puts and calls on one root are separate assignments, so a put assigned
//! beside a call bought back in the same entry is still checked. Same-day
//! entries are taken in beancount's `entry_sortkey` order (date, type,
//! line number). An assignment whose arithmetic leaves `Decimal`'s range
//! is skipped, not reported. The plugin reads no config: a non-blank config
//! string gives one warning.
//!
//! The plugin only reports: every directive is kept and nothing is inserted.

use std::collections::{BTreeMap, BTreeSet};
use std::str::FromStr;

use rust_decimal::Decimal;

use crate::types::{
    CostNumberData, DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput, PostingData,
    PriceAnnotationView,
};

use super::super::{NativePlugin, RegularPlugin};
use super::option_symbol::{OptionRight, config_is_set, parse_occ};

/// Shares delivered per standard equity option contract.
const SHARES_PER_CONTRACT: u32 = 100;

/// Plugin that checks the stock leg of short-option assignments.
pub struct CheckOptionAssignmentPlugin;

/// Why a total could not be computed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gap {
    /// The posting has no cost (or price), or an incomplete one.
    Missing,
    /// The arithmetic leaves `Decimal`'s range.
    Overflow,
}

/// Parse a posting's units as a number.
fn units_of(posting: &PostingData) -> Option<Decimal> {
    Decimal::from_str(&posting.units.as_ref()?.number).ok()
}

/// Total cost of a posting's units, as a positive number.
fn cost_total(posting: &PostingData, units: Decimal) -> Result<Decimal, Gap> {
    let parse = |s: &str| Decimal::from_str(s).map_err(|_| Gap::Missing);
    let number = posting
        .cost
        .as_ref()
        .and_then(|c| c.number.as_ref())
        .ok_or(Gap::Missing)?;
    let total = match number {
        CostNumberData::PerUnit { value } => {
            parse(value)?.checked_mul(units).ok_or(Gap::Overflow)?
        }
        CostNumberData::Total { value } | CostNumberData::PerUnitFromTotal { total: value, .. } => {
            parse(value)?
        }
        CostNumberData::Compound { per_unit, total } => parse(per_unit)?
            .checked_mul(units)
            .and_then(|t| t.checked_add(parse(total).ok()?))
            .ok_or(Gap::Overflow)?,
    };
    Ok(total.abs())
}

/// Total price of a posting's units, as a positive number.
fn price_total(posting: &PostingData, units: Decimal) -> Result<Decimal, Gap> {
    let parse = |s: &str| Decimal::from_str(s).map_err(|_| Gap::Missing);
    let total = match posting.price.as_ref().ok_or(Gap::Missing)?.view() {
        PriceAnnotationView::Unit(a) => {
            parse(&a.number)?.checked_mul(units).ok_or(Gap::Overflow)?
        }
        PriceAnnotationView::Total(a) => parse(&a.number)?,
        PriceAnnotationView::UnitIncomplete { .. }
        | PriceAnnotationView::TotalIncomplete { .. } => return Err(Gap::Missing),
    };
    Ok(total.abs())
}

/// Sum of totals: the first `Overflow` wins over any `Missing`, so an
/// overflow is never reported as a missing cost or price.
fn sum_totals(totals: impl Iterator<Item = Result<Decimal, Gap>>) -> Result<Decimal, Gap> {
    let mut sum = Some(Decimal::ZERO);
    let mut missing = false;
    for total in totals {
        match total {
            Ok(t) => sum = sum.and_then(|s| s.checked_add(t)),
            Err(Gap::Missing) => missing = true,
            Err(Gap::Overflow) => return Err(Gap::Overflow),
        }
    }
    match sum {
        None => Err(Gap::Overflow),
        Some(_) if missing => Err(Gap::Missing),
        Some(s) => Ok(s),
    }
}

/// Option legs of one transaction that close short contracts of one right
/// on one underlying.
#[derive(Default)]
struct Closing {
    symbols: Vec<String>,
    contracts: Decimal,
    /// Σ strike × shares.
    strike_value: Decimal,
    premium: Decimal,
    /// Σ price and Σ cost of the option legs that carry a price.
    priced: Decimal,
    priced_cost: Decimal,
    premium_realized: bool,
    /// Distinct strikes among the closed contracts.
    strikes: Vec<Decimal>,
    currency: Option<String>,
    /// Some sum left `Decimal`'s range; the closing is not checked.
    overflowed: bool,
}

impl Closing {
    /// Add one option leg closing `units` contracts at `strike`.
    fn add(
        &mut self,
        units: Decimal,
        strike: Decimal,
        premium: Decimal,
        price: Option<Decimal>,
    ) -> Option<()> {
        let shares = Decimal::from(SHARES_PER_CONTRACT);
        self.contracts = self.contracts.checked_add(units)?;
        self.strike_value = self
            .strike_value
            .checked_add(strike.checked_mul(units)?.checked_mul(shares)?)?;
        self.premium = self.premium.checked_add(premium)?;
        if let Some(price) = price {
            self.priced = self.priced.checked_add(price)?;
            self.priced_cost = self.priced_cost.checked_add(premium)?;
            self.premium_realized |= price != premium;
        }
        Some(())
    }
}

/// Running net units per (account, commodity); `None` once a sum overflowed.
type Positions = BTreeMap<(String, String), Option<Decimal>>;

impl NativePlugin for CheckOptionAssignmentPlugin {
    fn name(&self) -> &'static str {
        "check_option_assignment"
    }

    fn description(&self) -> &'static str {
        "Check that assigned short options fold the premium into the stock leg"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut errors = Vec::new();
        if config_is_set(input.config.as_deref()) {
            errors.push(PluginError::warning(
                "check_option_assignment: the config is ignored; this plugin has no options",
            ));
        }
        let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();

        // The option symbols and their roots: the only commodities tracked.
        let mut tracked: BTreeSet<&str> = BTreeSet::new();
        for d in &input.directives {
            let DirectiveData::Transaction(txn) = &d.data else {
                continue;
            };
            for units in txn.postings.iter().filter_map(|p| p.units.as_ref()) {
                if let Some(occ) = parse_occ(&units.currency) {
                    tracked.insert(units.currency.as_str());
                    if let Some(root) = txn
                        .postings
                        .iter()
                        .filter_map(|p| p.units.as_ref())
                        .find(|u| u.currency == occ.root)
                    {
                        tracked.insert(root.currency.as_str());
                    }
                }
            }
        }
        if tracked.is_empty() {
            return PluginOutput { ops, errors };
        }

        // Walk directives in beancount's `entry_sortkey` order (date, type,
        // line). The loader keeps file order for same-day entries; beancount
        // does not.
        let mut order: Vec<usize> = (0..input.directives.len()).collect();
        order.sort_by(|&a, &b| {
            input.directives[a]
                .sort_key()
                .cmp(&input.directives[b].sort_key())
        });

        let shares_per_contract = Decimal::from(SHARES_PER_CONTRACT);
        let mut net: Positions = BTreeMap::new();

        for &i in &order {
            let wrapper = &input.directives[i];
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                continue;
            };
            let held = |account: &str, commodity: &str| {
                net.get(&(account.to_string(), commodity.to_string()))
                    .copied()
                    .unwrap_or(Some(Decimal::ZERO))
            };

            // Option legs that close short contracts, by underlying and right.
            let mut closings: BTreeMap<(String, OptionRight), Closing> = BTreeMap::new();
            for posting in &txn.postings {
                let Some(units) = units_of(posting) else {
                    continue;
                };
                let symbol = &posting.units.as_ref().expect("units parsed").currency;
                let Some(occ) = parse_occ(symbol) else {
                    continue;
                };
                let Some(position) = held(&posting.account, symbol) else {
                    continue;
                };
                if position >= Decimal::ZERO || units <= Decimal::ZERO {
                    continue;
                }
                let premium = match cost_total(posting, units) {
                    Ok(premium) => premium,
                    Err(Gap::Missing) => continue,
                    Err(Gap::Overflow) => {
                        closings
                            .entry((occ.root.clone(), occ.right))
                            .or_default()
                            .overflowed = true;
                        continue;
                    }
                };
                let price = match price_total(posting, units) {
                    Ok(price) => Some(price),
                    Err(Gap::Missing) => None,
                    Err(Gap::Overflow) => {
                        closings
                            .entry((occ.root.clone(), occ.right))
                            .or_default()
                            .overflowed = true;
                        continue;
                    }
                };
                let c = closings.entry((occ.root.clone(), occ.right)).or_default();
                if !c.symbols.contains(symbol) {
                    c.symbols.push(symbol.clone());
                }
                if !c.strikes.contains(&occ.strike) {
                    c.strikes.push(occ.strike);
                }
                c.currency = c
                    .currency
                    .take()
                    .or_else(|| posting.cost.as_ref().and_then(|k| k.currency.clone()));
                if c.add(units, occ.strike, premium, price).is_none() {
                    c.overflowed = true;
                }
            }

            for ((root, right), c) in &closings {
                if c.overflowed {
                    continue;
                }
                if let Some(message) =
                    check(root, *right, c, &txn.postings, &held, shares_per_contract)
                {
                    let mut error = PluginError::error(message);
                    if let (Some(file), Some(line)) = (&wrapper.filename, wrapper.lineno) {
                        error = error.at(file.clone(), line);
                    }
                    errors.push(error);
                }
            }

            // Apply this transaction's tracked legs to the running positions.
            for posting in &txn.postings {
                let Some(units) = units_of(posting) else {
                    continue;
                };
                let commodity = &posting.units.as_ref().expect("units parsed").currency;
                if tracked.contains(commodity.as_str()) {
                    let entry = net
                        .entry((posting.account.clone(), commodity.clone()))
                        .or_insert(Some(Decimal::ZERO));
                    *entry = entry.and_then(|n| n.checked_add(units));
                }
            }
        }

        PluginOutput { ops, errors }
    }
}

/// The error for one closing group, if it is an assignment that fails a
/// rule. `None` when it is not an assignment, passes, or overflows.
fn check(
    root: &str,
    right: OptionRight,
    c: &Closing,
    postings: &[PostingData],
    held: &impl Fn(&str, &str) -> Option<Decimal>,
    shares_per_contract: Decimal,
) -> Option<String> {
    let stock: Vec<(&PostingData, Decimal)> = postings
        .iter()
        .filter(|p| p.units.as_ref().is_some_and(|u| u.currency == root))
        .filter_map(|p| units_of(p).map(|u| (p, u)))
        .collect();
    let stock_units = stock
        .iter()
        .try_fold(Decimal::ZERO, |sum, (_, u)| sum.checked_add(*u))?;
    let assigned = match right {
        OptionRight::Put => stock_units > Decimal::ZERO,
        OptionRight::Call => stock_units < Decimal::ZERO,
    };
    if !assigned {
        return None;
    }

    let label = c.symbols.join(", ");
    let currency = c.currency.clone().unwrap_or_default();
    let shares = stock_units.abs();
    let expected_shares = c.contracts.checked_mul(shares_per_contract)?;
    if shares != expected_shares {
        return Some(format!(
            "{label} assignment: {} contract(s) but {} {root}; expected {}",
            c.contracts.normalize(),
            shares.normalize(),
            expected_shares.normalize()
        ));
    }
    if c.premium_realized {
        return Some(format!(
            "{label} assignment: option leg priced at {:.2} {currency}, not its cost {:.2} {currency}; close it at cost and fold the premium into the {root} leg",
            c.priced, c.priced_cost
        ));
    }

    let breakdown_strike = if c.strikes.len() == 1 {
        format!("strike {} × {}", c.strikes[0], expected_shares.normalize())
    } else {
        format!("strike value {:.2}", c.strike_value)
    };
    let tolerance = Decimal::new(5, 3).checked_mul(shares)?;
    let off = |actual: Decimal, expected: Decimal| -> Option<bool> {
        Some(actual.checked_sub(expected)?.abs() > tolerance)
    };
    match right {
        OptionRight::Put => {
            let expected = c.strike_value.checked_sub(c.premium)?;
            match sum_totals(stock.iter().map(|(p, u)| cost_total(p, *u))) {
                Err(Gap::Overflow) => None,
                Err(Gap::Missing) => Some(format!(
                    "{label} assignment: {root} purchase has no cost; expected basis {expected:.2} {currency}"
                )),
                Ok(basis) => off(basis, expected)?.then(|| {
                    format!(
                        "{label} assignment: {root} basis {basis:.2} {currency}, expected {expected:.2} {currency} ({breakdown_strike} − premium {:.2})",
                        c.premium
                    )
                }),
            }
        }
        OptionRight::Call => {
            let expected = c.strike_value.checked_add(c.premium)?;
            // A sale with no price that opens (or extends) a short position
            // gives its proceeds as the short lot's cost.
            let proceeds = stock.iter().map(|(p, u)| match price_total(p, *u) {
                Err(Gap::Missing)
                    if p.cost.is_some()
                        && held(&p.account, root).is_some_and(|h| h <= Decimal::ZERO) =>
                {
                    cost_total(p, *u)
                }
                total => total,
            });
            match sum_totals(proceeds) {
                Err(Gap::Overflow) => None,
                Err(Gap::Missing) => Some(format!(
                    "{label} assignment: {root} sale has no price; expected proceeds {expected:.2} {currency}"
                )),
                Ok(proceeds) => off(proceeds, expected)?.then(|| {
                    format!(
                        "{label} assignment: {root} proceeds {proceeds:.2} {currency}, expected {expected:.2} {currency} ({breakdown_strike} + premium {:.2})",
                        c.premium
                    )
                }),
            }
        }
    }
}

impl RegularPlugin for CheckOptionAssignmentPlugin {}
