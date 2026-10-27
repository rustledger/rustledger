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
//! With a commission the entry settles beyond the strike value, and rule 3
//! then accepts the range "fee expensed to fee folded" — but only when the
//! entry is plainly one assignment and its cash is an independent witness
//! (#2732): exactly one closing group, every cash posting written rather
//! than booking-interpolated, and no posting carrying a cost or price
//! outside the group's option and stock legs. The fee the window allows is
//! the one the entry's cash proves it moved. Fees paid to acquire
//! capitalize into basis (26 CFR §1.263(a)-4(c)(1)(i), (b)(1)(v),
//! (e)(4)(iii)(B)); selling costs reduce the amount realized
//! (§1.263(a)-1(e)(1)). When a guard fails, or there is no cash to measure
//! a fee from, the exact figure is required: the safe direction, since at
//! worst a fee-folded ledger gets flagged.
//!
//! Two things this window knowingly misses. An explicitly typed cash
//! amount that is wrong by exactly the basis error still passes (only
//! booking-interpolated cash forces the fallback); a `balance` assertion
//! is what catches that. And a ledger whose basis matches its 1099-B —
//! which carries the commission on the option's *opening* trade too — is
//! flagged when it expensed that opening fee: a false alarm against the
//! books, not a missed error.
//!
//! Puts and calls on one root are separate assignments, so a put assigned
//! beside a call bought back in the same entry is still checked. Same-day
//! entries are taken in beancount's `entry_sortkey` order (date, type,
//! line number). The plugin reads no config: a non-blank config string
//! gives one warning.
//!
//! Each rule runs whenever its own arithmetic fits in `Decimal`: the share
//! count needs only contracts × 100, so it is still checked when strike ×
//! shares is out of range. When a rule cannot run for that reason, the
//! assignment gets an error, `… assignment not checked: amounts exceed the
//! supported decimal range`, at the entry. It is an error, not a warning,
//! for the same reason E4004 is: a check that did not run must not pass.
//! Running positions cannot leave the range after booking, which rejects
//! such an inventory first; unbooked input that does is not tracked.
//!
//! beancount-options has the Python counterpart (rustledger/beancount-options#4)
//! and both report the same thing. Two details are documented in its README
//! (`### Configuration`) instead of matched: its config notice is an error
//! (beancount has no warnings), and amounts past `Decimal`'s range are
//! checked rather than reported unchecked.
//!
//! The plugin only reports: every directive is kept and nothing is inserted.

use std::collections::{BTreeMap, BTreeSet};
use std::str::FromStr;

use rust_decimal::Decimal;

use crate::types::{
    CostNumberData, DirectiveData, PluginAccountTypes, PluginError, PluginInput, PluginOp,
    PluginOutput, PostingData, PriceAnnotationView,
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

/// Whether `account` is under one of the two cash roots the ledger
/// configured. Equity is excluded: a settlement's cash belongs on the
/// balance sheet's cash side (#2732).
fn is_cash_account(account: &str, account_types: &PluginAccountTypes) -> bool {
    let root = account.split(':').next().unwrap_or(account);
    root == account_types.assets || root == account_types.liabilities
}

/// Whether `posting` is one of the entry's cash postings for the fee
/// window: no cost, no price, in `currency`, on an Assets or Liabilities
/// account (#2732).
fn is_cash_posting(
    posting: &PostingData,
    currency: &str,
    account_types: &PluginAccountTypes,
) -> bool {
    posting.cost.is_none()
        && posting.price.is_none()
        && posting
            .units
            .as_ref()
            .is_some_and(|u| u.currency == currency)
        && is_cash_account(&posting.account, account_types)
}

/// The commission the entry's cash proves it moved, floored at 0 (#2732).
///
/// Widens rule 3 from the exact figure to the range "fee expensed to fee
/// folded", but only when the cash is an independent witness and the entry
/// is one assignment, the two guards accepted in #2555: exactly one
/// closing group; every cash posting written (a booking-interpolated
/// figure is filled from the very residual this would measure); and no
/// posting carrying a cost or price outside the group's option and stock
/// legs (a sweep purchase, a foreign-currency settlement priced with `@`,
/// or a second trade would all move the cash). Any guard failing, a
/// missing cost currency, or arithmetic out of range gives 0 — today's
/// exact rule, the safe direction: at worst a fee-folded ledger gets
/// flagged.
fn commission(
    postings: &[PostingData],
    root: &str,
    right: OptionRight,
    currency: Option<&str>,
    strike_value: Decimal,
    one_assignment: bool,
    account_types: &PluginAccountTypes,
) -> Decimal {
    let Some(currency) = currency else {
        return Decimal::ZERO;
    };
    if !one_assignment {
        return Decimal::ZERO;
    }
    for posting in postings {
        if posting.cost.is_none() && posting.price.is_none() {
            continue;
        }
        let group_leg = posting.units.as_ref().is_some_and(|u| {
            u.currency == root
                || parse_occ(&u.currency).is_some_and(|o| o.root == root && o.right == right)
        });
        if !group_leg {
            return Decimal::ZERO;
        }
    }
    let mut cash = Some(Decimal::ZERO);
    for posting in postings {
        if !is_cash_posting(posting, currency, account_types) {
            continue;
        }
        if posting.is_interpolated() {
            return Decimal::ZERO;
        }
        let number = posting
            .units
            .as_ref()
            .and_then(|u| Decimal::from_str(&u.number).ok());
        cash = cash.zip(number).and_then(|(c, n)| c.checked_add(n));
    }
    let Some(cash) = cash else {
        return Decimal::ZERO;
    };
    let fee = match right {
        OptionRight::Put => Decimal::ZERO
            .checked_sub(cash)
            .and_then(|c| c.checked_sub(strike_value)),
        OptionRight::Call => strike_value.checked_sub(cash),
    };
    fee.map_or(Decimal::ZERO, |f| f.max(Decimal::ZERO))
}

/// Option legs of one transaction that close short contracts of one right
/// on one underlying. Each sum is `None` once it leaves `Decimal`'s range,
/// so the rules that need it are not run, and the others still are.
struct Closing {
    symbols: Vec<String>,
    contracts: Option<Decimal>,
    /// Σ strike × shares.
    strike_value: Option<Decimal>,
    premium: Option<Decimal>,
    /// Σ price and Σ cost of the option legs that carry a price.
    priced: Option<Decimal>,
    priced_cost: Option<Decimal>,
    premium_realized: bool,
    /// Distinct strikes among the closed contracts.
    strikes: Vec<Decimal>,
    currency: Option<String>,
}

impl Default for Closing {
    fn default() -> Self {
        Self {
            symbols: Vec::new(),
            contracts: Some(Decimal::ZERO),
            strike_value: Some(Decimal::ZERO),
            premium: Some(Decimal::ZERO),
            priced: Some(Decimal::ZERO),
            priced_cost: Some(Decimal::ZERO),
            premium_realized: false,
            strikes: Vec::new(),
            currency: None,
        }
    }
}

/// Add `term` to `sum`; `None` (out of range) on either side stays `None`.
fn accumulate(sum: &mut Option<Decimal>, term: Option<Decimal>) {
    *sum = sum.zip(term).and_then(|(s, t)| s.checked_add(t));
}

impl Closing {
    /// Add one option leg closing `units` contracts at `strike`. `premium`
    /// is `None` when out of range; `price` is the leg's total price.
    fn add(
        &mut self,
        units: Decimal,
        strike: Decimal,
        premium: Option<Decimal>,
        price: Result<Decimal, Gap>,
    ) {
        let shares = Decimal::from(SHARES_PER_CONTRACT);
        accumulate(&mut self.contracts, Some(units));
        accumulate(
            &mut self.strike_value,
            strike
                .checked_mul(units)
                .and_then(|v| v.checked_mul(shares)),
        );
        accumulate(&mut self.premium, premium);
        match price {
            Err(Gap::Missing) => {}
            Ok(price) => {
                accumulate(&mut self.priced, Some(price));
                accumulate(&mut self.priced_cost, premium);
                self.premium_realized |= premium.is_some_and(|p| p != price);
            }
            Err(Gap::Overflow) => {
                self.priced = None;
                self.priced_cost = None;
            }
        }
    }
}

/// What [`check`] found for one closing group.
#[derive(Debug, PartialEq, Eq)]
enum Finding {
    /// The assignment fails a rule.
    Error(String),
    /// The assignment's arithmetic leaves `Decimal`'s range before every
    /// rule could run.
    Unchecked,
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
                    Ok(premium) => Some(premium),
                    Err(Gap::Missing) => continue,
                    Err(Gap::Overflow) => None,
                };
                let price = price_total(posting, units);
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
                c.add(units, occ.strike, premium, price);
            }

            for ((root, right), c) in &closings {
                if let Some(finding) = check(
                    root,
                    *right,
                    c,
                    &txn.postings,
                    &held,
                    shares_per_contract,
                    closings.len() == 1,
                    &input.options.account_types,
                ) {
                    let message = match finding {
                        Finding::Error(message) => message,
                        Finding::Unchecked => format!(
                            "{} assignment not checked: amounts exceed the supported decimal range",
                            c.symbols.join(", ")
                        ),
                    };
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

/// What one closing group gives, if it is an assignment: the error of the
/// first rule that fails, or [`Finding::Unchecked`] when a rule's
/// arithmetic leaves `Decimal`'s range before any rule failed. `None` when
/// it is not an assignment or passes every rule.
fn check(
    root: &str,
    right: OptionRight,
    c: &Closing,
    postings: &[PostingData],
    held: &impl Fn(&str, &str) -> Option<Decimal>,
    shares_per_contract: Decimal,
    one_assignment: bool,
    account_types: &PluginAccountTypes,
) -> Option<Finding> {
    use Finding::{Error, Unchecked};
    let stock: Vec<(&PostingData, Decimal)> = postings
        .iter()
        .filter(|p| p.units.as_ref().is_some_and(|u| u.currency == root))
        .filter_map(|p| units_of(p).map(|u| (p, u)))
        .collect();
    // Out of range here means the direction is unknown, so whether this is
    // an assignment is too: say so rather than pass it.
    let Some(stock_units) = stock
        .iter()
        .try_fold(Decimal::ZERO, |sum, (_, u)| sum.checked_add(*u))
    else {
        return Some(Unchecked);
    };
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
    // Rule 1 needs only contracts × 100, so it runs even when the strike
    // value below is out of range.
    let Some((contracts, expected_shares)) = c
        .contracts
        .and_then(|n| Some((n, n.checked_mul(shares_per_contract)?)))
    else {
        return Some(Unchecked);
    };
    if shares != expected_shares {
        return Some(Error(format!(
            "{label} assignment: {} contract(s) but {} {root}; expected {}",
            contracts.normalize(),
            shares.normalize(),
            expected_shares.normalize()
        )));
    }
    let (Some(priced), Some(priced_cost)) = (c.priced, c.priced_cost) else {
        return Some(Unchecked);
    };
    if c.premium_realized {
        return Some(Error(format!(
            "{label} assignment: option leg priced at {priced:.2} {currency}, not its cost {priced_cost:.2} {currency}; close it at cost and fold the premium into the {root} leg"
        )));
    }

    let (Some(strike_value), Some(premium)) = (c.strike_value, c.premium) else {
        return Some(Unchecked);
    };
    let breakdown_strike = if c.strikes.len() == 1 {
        format!("strike {} × {}", c.strikes[0], expected_shares.normalize())
    } else {
        format!("strike value {strike_value:.2}")
    };
    let Some(tolerance) = Decimal::new(5, 3).checked_mul(shares) else {
        return Some(Unchecked);
    };
    // Rule 3's acceptance band. `fee` widens it to "fee expensed to fee
    // folded" when the entry's cash proves a commission (#2732); 0 keeps
    // the exact rule.
    let fee = commission(
        postings,
        root,
        right,
        c.currency.as_deref(),
        strike_value,
        one_assignment,
        account_types,
    );
    // The fee widens only the side it can move: a put's basis may carry
    // it, a call's proceeds may lose it.
    let outside = |actual: Decimal, expected: Decimal| -> Option<bool> {
        let (lo, hi) = match right {
            OptionRight::Put => (
                expected.checked_sub(tolerance)?,
                expected.checked_add(fee)?.checked_add(tolerance)?,
            ),
            OptionRight::Call => (
                expected.checked_sub(fee)?.checked_sub(tolerance)?,
                expected.checked_add(tolerance)?,
            ),
        };
        Some(actual < lo || actual > hi)
    };
    match right {
        OptionRight::Put => {
            let Some(expected) = strike_value.checked_sub(premium) else {
                return Some(Unchecked);
            };
            match sum_totals(stock.iter().map(|(p, u)| cost_total(p, *u))) {
                Err(Gap::Overflow) => Some(Unchecked),
                Err(Gap::Missing) => Some(Error(format!(
                    "{label} assignment: {root} purchase has no cost; expected basis {expected:.2} {currency}"
                ))),
                Ok(basis) => match outside(basis, expected) {
                    None => Some(Unchecked),
                    Some(false) => None,
                    Some(true) => Some(Error(if fee > Decimal::ZERO {
                        match expected.checked_add(fee) {
                            None => return Some(Unchecked),
                            Some(window_hi) => format!(
                                "{label} assignment: {root} basis {basis:.2} {currency}, expected {expected:.2} to {window_hi:.2} {currency} ({breakdown_strike} − premium {premium:.2}, + up to {fee:.2} in fees)"
                            ),
                        }
                    } else {
                        format!(
                            "{label} assignment: {root} basis {basis:.2} {currency}, expected {expected:.2} {currency} ({breakdown_strike} − premium {premium:.2})"
                        )
                    })),
                },
            }
        }
        OptionRight::Call => {
            let Some(expected) = strike_value.checked_add(premium) else {
                return Some(Unchecked);
            };
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
                Err(Gap::Overflow) => Some(Unchecked),
                Err(Gap::Missing) => Some(Error(format!(
                    "{label} assignment: {root} sale has no price; expected proceeds {expected:.2} {currency}"
                ))),
                Ok(proceeds) => match outside(proceeds, expected) {
                    None => Some(Unchecked),
                    Some(false) => None,
                    Some(true) => Some(Error(if fee > Decimal::ZERO {
                        match expected.checked_sub(fee) {
                            None => return Some(Unchecked),
                            Some(window_lo) => format!(
                                "{label} assignment: {root} proceeds {proceeds:.2} {currency}, expected {window_lo:.2} to {expected:.2} {currency} ({breakdown_strike} + premium {premium:.2}, − up to {fee:.2} in fees)"
                            ),
                        }
                    } else {
                        format!(
                            "{label} assignment: {root} proceeds {proceeds:.2} {currency}, expected {expected:.2} {currency} ({breakdown_strike} + premium {premium:.2})"
                        )
                    })),
                },
            }
        }
    }
}

impl RegularPlugin for CheckOptionAssignmentPlugin {}
