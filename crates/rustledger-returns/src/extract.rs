//! Cash-flow extraction: turn a ledger into the [`CashFlow`] series that
//! [`xirr`](crate::xirr) consumes.
//!
//! This is the correctness core of returns reporting. Given an interpolated,
//! pad-expanded directive stream (see the input contract below — it does *not*
//! require booking) and a [`Scope`] that classifies accounts, it produces the
//! dated, single-currency cash-flow series an investor's money-weighted return is
//! computed from.
//!
//! # The boundary-crossing model
//!
//! Every account plays one of three [roles](AccountRole):
//!
//! - **Investment** — the holdings and their associated settlement cash. Their
//!   value is tracked *inside* the portfolio, so a change to them is not itself
//!   a cash flow.
//! - **Income** — dividends, realized gains, fees: profit-and-loss *generated
//!   by* the investment. Internal to the return, not money the investor moved.
//! - **External** — everything else (a bank, an outside cash account). This is
//!   the money that actually crosses the portfolio boundary.
//!
//! For any transaction that touches an investment or income account, the cash
//! flow is the sum of its **external** postings, each converted to the single
//! reporting currency at the transaction's date:
//!
//! ```text
//! cashflow_t = Σ { p.units : p.account is External }
//! ```
//!
//! For a plain transaction (no per-posting cost or price annotation) the
//! postings' units sum to zero, so this equals `−Σ { units : Investment or
//! Income }` — the boundary is crossed by exactly the external side. External
//! postings are summed by their **units**, i.e. the money that actually moved
//! through the outside account, which is what a cash flow is. (A transaction
//! whose *external* leg carries its own `@`price or `{cost}` — an in-kind
//! transfer across the boundary, or a cash leg with an explicit rate — is a
//! documented edge: its units are valued through the oracle, not the stated
//! weight. See [`extract_flows`].)
//!
//! With the investor-centric sign convention (see the [crate] docs) this gives
//! the right answer for free:
//!
//! - **Purchase** (`Assets:Bank -1000 USD`) → cash flow **-1000**: an investor
//!   outlay.
//! - **Sale / dividend to bank** (`Assets:Bank +500 USD`) → **+500**: money the
//!   investor received.
//! - **Internal transfer** — shares or cash moved between two accounts that are
//!   *both* inside the scope — has no external posting, so its flow is **0** and
//!   it correctly does not register. Double-counting an internal transfer is the
//!   single most error-prone mistake in returns math; here the boundary model
//!   excludes it structurally rather than by a special case.
//!
//! A final synthetic **terminal** flow values the position still held on the
//! report end date at market (see [`terminal_value`]), because an investor who
//! has not sold has still earned (or lost) that unrealized value.
//!
//! # What the caller supplies
//!
//! Prices come through the [`PriceOracle`] trait rather than a concrete price
//! database, so this crate stays a leaf (no dependency on the query engine that
//! owns the price index) and the extraction logic is testable against a
//! hand-specified rate table. The production consumer implements [`PriceOracle`]
//! over its price database.
//!
//! # Input contract
//!
//! Both entry points take the **interpolated, pad-expanded** directive stream —
//! amounts interpolated and `pad`/`balance` directives already expanded into their
//! synthesized transactions (the loader's `Ledger::balance_view` output, the same
//! stream the canonical `report_cmd::account_balances` consumes). This crate is a
//! leaf and cannot interpolate or pad-expand a raw stream itself.
//!
//! It does **not** require a *booked* stream. Money-weighted (XIRR) and
//! time-weighted returns depend on cash flows and terminal **market** value
//! (`net units × price`), never on cost-basis lots, so this crate values **net
//! units** — the running sum of each account's complete posting units — without
//! lot-matching. A cost-basis/lot error therefore does not affect the report: an
//! over-sell or an empty-cost `{}` sale with no matching lot (the common state of
//! imported brokerage data) simply nets the units, possibly negative, and is
//! valued at market — like beancount + beangrow. `rledger check` remains the
//! validator (see #1850). The one shape it genuinely cannot value is an in-scope
//! account with an elided/uninterpolated posting — its net units are unknown —
//! which surfaces as [`ExtractError::UnbookedInput`] rather than a silently
//! understated figure. It cannot defend the pad half either: handing it an
//! un-expanded stream silently drops any position seeded by a pad, so callers must
//! pad-expand first.
//!
//! Returns are computed **from ledger inception** — there is no analysis start
//! date. An opening balance (a `pad`, or an explicit `Equity:Opening-Balances`
//! posting) is therefore a genuine cash flow: the capital the investor already
//! had in the position at the start. Its `Equity` leg classifies as External, so
//! seeding `Assets:Broker:Cash 500 / Equity:Opening-Balances -500` yields a −500
//! opening outflow that correctly pairs with the +500 that account contributes
//! to the terminal value — net a 0% return on an untouched opening balance, as
//! it should be. (A period-scoped model with a start date, valuing the position
//! at that date as the opening basis, is future work; see the tracking issue.)

use rust_decimal::Decimal;
use rust_decimal::prelude::ToPrimitive;
use rustledger_core::{Amount, Directive, IncompleteAmount, NaiveDate, is_subaccount_or_equal};

use crate::CashFlow;

/// Resolves the exchange rate needed to state every flow in one reporting
/// currency.
///
/// The extraction layer is single-currency by construction — a money-weighted
/// return over flows in mixed currencies is meaningless — so every flow and the
/// terminal valuation are converted through this trait before the math runs.
///
/// The method mirrors the signature of the consumer's price-database
/// `convert`, so wiring a real price index to this trait is a pass-through.
pub trait PriceOracle {
    /// Convert `amount` into `to_currency` using the rate in effect on `date`
    /// (conventionally the most recent rate on or before it).
    ///
    /// Returns `None` when no conversion path exists — a same-currency
    /// conversion must return the amount unchanged (rate 1), never `None`.
    ///
    /// The conversion must be **linear in the amount** — a fixed rate applied to
    /// `amount.number`, so `convert(-x) == -convert(x)`. Extraction relies on
    /// this to value a net-short holding (negative units) as a negative terminal
    /// flow; an implementation that clamped or took the absolute value would
    /// invert a short position's contribution.
    fn convert(&self, amount: &Amount, to_currency: &str, date: NaiveDate) -> Option<Amount>;
}

/// The role an account plays in a returns computation.
///
/// See the module-level documentation for how each role contributes (or
/// doesn't) to the cash-flow series.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccountRole {
    /// A holding or its settlement cash: inside the portfolio boundary.
    Investment,
    /// Profit-and-loss generated by the investment — dividends and realized
    /// gains, but also investment *expenses* (broker fees, commissions): inside
    /// the boundary, so it drags the return rather than counting as money the
    /// investor moved. Named for the `--income` scoping flag, but semantically
    /// P&L (income *and* related expenses).
    Income,
    /// Outside the portfolio: money moving across the boundary is a cash flow.
    External,
}

/// Classifies each account into an [`AccountRole`] by matching it against
/// caller-supplied account prefixes.
///
/// Matching is segment-aware (via [`is_subaccount_or_equal`]): the prefix
/// `Assets:Broker` matches `Assets:Broker` and `Assets:Broker:Cash` but not
/// `Assets:Brokerage`. An account takes the role of the **longest** (most
/// specific) prefix it matches across both lists, so nesting resolves the
/// intuitive way: with investment `Assets:Broker` and income
/// `Assets:Broker:Dividends`, the dividend subaccount is Income (the longer
/// match) while the rest of the broker tree is Investment. An account matching
/// neither list is **External**. On an exact-length tie (the same string in both
/// lists — a misconfiguration) Investment wins.
///
/// The `income` prefixes are the investment's **P&L** (income *and* related
/// expenses): dividend and gain accounts, and also the broker fees / commissions
/// the investment incurs. Scope fees here, not as External — a fee left External
/// is treated as money the investor received on a sale (gross instead of net
/// proceeds), overstating the return. Conversely, the prefixes must name *only*
/// investment-related P&L, never a whole tree like `Income`: capturing unrelated
/// earnings (salary, refunds) would fold those into the portfolio's flows and
/// corrupt the return the other way.
#[derive(Debug, Clone, Default)]
pub struct Scope {
    investment: Vec<String>,
    income: Vec<String>,
}

impl Scope {
    /// Build a scope from investment and income account prefixes.
    #[must_use]
    pub const fn new(investment: Vec<String>, income: Vec<String>) -> Self {
        Self { investment, income }
    }

    /// Classify a single account.
    ///
    /// The account takes the role of the longest matching prefix across both
    /// lists (most-specific wins), so an income account nested under an
    /// investment prefix still classifies as Income. Investment breaks an
    /// exact-length tie.
    #[must_use]
    pub fn classify(&self, account: &str) -> AccountRole {
        // Longest matching prefix wins. Track the best match length for each
        // role; on a tie (`>=` for investment, `>` for income) Investment wins.
        let longest = |prefixes: &[String]| -> Option<usize> {
            prefixes
                .iter()
                .filter(|p| is_subaccount_or_equal(account, p))
                .map(String::len)
                .max()
        };
        let investment = longest(&self.investment);
        let income = longest(&self.income);
        match (investment, income) {
            (Some(inv), Some(inc)) if inc > inv => AccountRole::Income,
            (Some(_), _) => AccountRole::Investment,
            (None, Some(_)) => AccountRole::Income,
            (None, None) => AccountRole::External,
        }
    }
}

/// Why cash-flow extraction could not produce a well-defined series.
///
/// Extraction fails loudly rather than dropping a flow it cannot state in the
/// reporting currency: a silently omitted flow does not error, it just returns
/// the wrong rate.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ExtractError {
    /// No exchange rate was available to convert an amount into the reporting
    /// currency on the date it was needed. Carries the source currency and the
    /// date whose rate was missing.
    #[error("no price to convert {currency} to the reporting currency on {date}")]
    MissingPrice {
        /// The currency that could not be converted.
        currency: String,
        /// The date whose rate was missing.
        date: NaiveDate,
    },
    /// A posting with elided/uninterpolated units left a scope-relevant quantity
    /// unknown, so the figure cannot be computed. Two shapes: an **in-scope
    /// holding** whose net units are unknown (valuation side), and an
    /// **external/boundary leg of a portfolio-touching transaction** whose cash
    /// flow is unknown (flows side — [`extract_flows`]). This is the ONE class of
    /// input that net-units genuinely cannot handle — unlike a cost-basis/lot error
    /// (an over-sell, an empty-cost `{}` sale with no matching lot), which nets the
    /// units and values at market.
    /// Extraction refuses rather than silently understate the position or drop the
    /// flow. Carries a human-readable description.
    #[error("cannot compute returns: {0}")]
    UnbookedInput(String),
}

/// Extract the full cash-flow series (external boundary-crossing flows plus the
/// terminal market value of the position still held) for `scope`, in
/// `reporting_currency`, valued as of `end_date`.
///
/// Flows dated after `end_date` are excluded; `end_date` is both the horizon and
/// the valuation date for the terminal flow. The returned series is sorted by
/// date and ready to hand to [`xirr`](crate::xirr).
///
/// # Input contract
///
/// `directives` must be the **interpolated, pad-expanded** stream — amounts
/// interpolated and `pad`/`balance` directives already expanded into their
/// synthesized transactions (the loader's `Ledger::balance_view` output, the same
/// stream `report_cmd::account_balances` consumes). This crate is a leaf and
/// cannot interpolate or pad-expand a raw stream. It does **not** require a booked
/// stream: it values net units at market, so a cost-basis/lot error nets the units
/// rather than realizing a wrong inventory (see the module docs). An un-expanded
/// stream still drops pad-seeded positions, though.
///
/// Returns are computed **from ledger inception** — an opening balance (a `pad`,
/// or an `Equity:Opening-Balances` posting) is a genuine flow, the capital
/// already in the position at the start, and it correctly pairs with that
/// account's contribution to the terminal value. See the module-level docs for
/// the full rationale and the boundary-crossing model.
///
/// # Errors
///
/// Returns [`ExtractError::MissingPrice`] if any external flow or held position
/// cannot be converted to `reporting_currency` on the date it is needed, or
/// [`ExtractError::UnbookedInput`] if an elided/uninterpolated posting leaves a
/// scope-relevant quantity unknown — an in-scope holding (see [`terminal_value`])
/// or an external boundary leg (see [`extract_flows`]).
pub fn extract_cash_flows(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
) -> Result<Vec<CashFlow>, ExtractError> {
    let mut flows = extract_flows(directives, scope, reporting_currency, prices, end_date)?;
    if let Some(terminal) = terminal_value(directives, scope, reporting_currency, prices, end_date)?
    {
        flows.push(terminal);
    }
    // Sort by date so the series is deterministic and the earliest flow (which
    // xirr uses as t=0) is unambiguous.
    flows.sort_by_key(|flow| flow.date);
    Ok(flows)
}

/// Extract only the boundary-crossing flows (no terminal valuation).
///
/// Each relevant transaction contributes one flow equal to the sum of its
/// external postings, converted to `reporting_currency` at the transaction's
/// date. Transactions that touch no investment or income account, and those
/// whose external postings net to zero (internal transfers), contribute
/// nothing. Flows dated after `end_date` are excluded. Expects the interpolated,
/// pad-expanded stream described in the module-level docs (booking is not
/// required — a cost-basis/lot error does not affect the flows).
///
/// External postings are valued by their **units** (the money that moved
/// through the outside account). A boundary-crossing external posting that
/// carries its own `@`price or `{cost}` — an in-kind commodity transfer in or
/// out, or a cash leg with an explicit rate — is valued through the oracle at
/// its units, *not* its stated balance weight; if the two disagree the flow
/// follows the oracle. This is a deliberate limitation for the common case
/// (external legs are plain cash): honoring per-posting weights is future work.
///
/// # Errors
///
/// Returns [`ExtractError::MissingPrice`] if an external posting of a relevant
/// transaction cannot be converted to `reporting_currency` on its date, or
/// [`ExtractError::UnbookedInput`] if such a posting has elided/uninterpolated
/// units (its cash flow is unknown — the flows counterpart of an elided holding).
pub fn extract_flows(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
) -> Result<Vec<CashFlow>, ExtractError> {
    let mut flows = Vec::new();

    for directive in directives {
        let Directive::Transaction(txn) = directive else {
            continue;
        };
        if txn.date > end_date {
            continue;
        }

        // Relevance gate first: only a transaction that touches the portfolio
        // (an investment or income account) can produce a flow. Classifying for
        // relevance up front — and short-circuiting on the first in-scope
        // posting — means an irrelevant transaction (the common case) costs only
        // this scan: no conversion, no allocation, and never a spurious
        // MissingPrice on an unrelated currency. Relevant transactions are a
        // small minority, so re-classifying their postings in the sum below is
        // cheaper than allocating a per-transaction buffer for every directive.
        let touches_portfolio = txn.postings.iter().any(|posting| {
            !matches!(
                scope.classify(posting.account.as_str()),
                AccountRole::External
            )
        });
        if !touches_portfolio {
            continue;
        }

        // The flow is the sum of the external postings' units, each converted at
        // the transaction's date. For a plain transaction the external side is
        // exactly the negation of the investment+income side, so summing it
        // directly makes the sign land investor-centric (a purchase debits an
        // external cash account negative → an outflow) without a manual negation.
        let mut net = Decimal::ZERO;
        for posting in &txn.postings {
            if scope.classify(posting.account.as_str()) != AccountRole::External {
                continue;
            }
            // An elided/uninterpolated external leg of a portfolio-touching
            // transaction is a boundary cash flow of UNKNOWN magnitude — the flows
            // counterpart of an elided in-scope holding (see `value_investment_scope`).
            // Net-units tolerates a cost-basis/lot error, but it cannot invent a
            // flow it can't see, so surface it as `UnbookedInput` rather than
            // silently drop the contribution (which would understate `invested` and
            // report a wrong money-weighted return). A fully interpolated stream
            // never hits this; a re-merged booking-failed transaction can.
            let Some(amount) = posting.amount() else {
                return Err(ExtractError::UnbookedInput(format!(
                    "posting to {} on {} has elided/uninterpolated units; cannot compute its cash flow",
                    posting.account, txn.date
                )));
            };
            let converted = prices
                .convert(amount, reporting_currency, txn.date)
                .ok_or_else(|| ExtractError::MissingPrice {
                    currency: amount.currency.to_string(),
                    date: txn.date,
                })?;
            net += converted.number;
        }

        if !net.is_zero() {
            flows.push(CashFlow::new(txn.date, net));
        }
    }

    Ok(flows)
}

/// Value the position still held in investment accounts as of `end_date`.
///
/// Returns it as a single terminal cash flow (the money the investor would
/// realize by liquidating) dated `end_date`, or `None` when nothing is held **or
/// the held position's market value is exactly zero**. A zero-valued terminal is
/// deliberately *not* emitted: it is not neutral to [`xirr`](crate::xirr) — a
/// zero flow on a date later than the real flows defeats xirr's all-same-date
/// degenerate guard, which would turn a genuinely-undefined series (e.g. a
/// same-date deposit/withdrawal wash with a worthless residual holding) into a
/// fabricated return. A consumer that needs to distinguish "still holding,
/// net-flat" from "fully liquidated" must not learn it from a zero cash flow.
///
/// Holdings are the **net units** per `(account, commodity)` — the running sum of
/// each account's complete posting units over every transaction dated on or before
/// `end_date`, **without lot-matching** — valued at **market** via `prices`. Market
/// value is `units × price` and every lot of a commodity shares one market price,
/// so the terminal value depends only on total held units, never on which lots a
/// reduction matched or on cost basis; a cost-basis/lot error (an over-sell, an
/// empty-cost `{}` sale with no matching lot) simply nets the units. Only accounts
/// the `scope` classifies as [`Investment`](AccountRole::Investment) are counted.
/// Positions seeded by a `pad` are counted only if the input stream is pad-expanded,
/// as [`extract_cash_flows`]' input contract requires.
///
/// A net-short position (negative units) values negatively, correctly reducing
/// the terminal flow (see the [`PriceOracle`] linearity requirement). A position
/// whose currency is already the reporting currency (uninvested broker cash)
/// needs no price.
///
/// # Errors
///
/// Returns [`ExtractError::MissingPrice`] if a held commodity has no price in
/// `reporting_currency` on `end_date`, or [`ExtractError::UnbookedInput`] if an
/// in-scope account carries an elided/uninterpolated posting (its net units are
/// unknown — the one shape net-units cannot value).
pub fn terminal_value(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
) -> Result<Option<CashFlow>, ExtractError> {
    let total = investment_value_at(directives, scope, reporting_currency, prices, end_date)?;
    // Only a nonzero market value becomes a terminal flow. A zero total — whether
    // from an empty portfolio or a net-flat/worthless holding — yields no flow:
    // emitting a zero flow on `end_date` is not neutral, it defeats xirr's
    // all-same-date degenerate guard and would fabricate a return (see the fn
    // docs). `total` can only be nonzero if some position was valued, so this
    // also covers the "nothing held" case.
    if total.is_zero() {
        Ok(None)
    } else {
        Ok(Some(CashFlow::new(end_date, total)))
    }
}

/// Market value (in `reporting_currency`) of the investment-scope holdings as of
/// `date`: the **net units** accumulated from every transaction dated on or before
/// `date`, each commodity valued at **market** at `date`.
///
/// This is the shared valuation primitive behind [`terminal_value`] (the value at
/// the report end date) and [`twr`] (the value at each cash-flow date). On a
/// booked stream the net units per commodity equal the total units
/// `report_cmd::account_balances` (`crates/rustledger/src/cmd/report_cmd/mod.rs`)
/// realizes, so the market value agrees; the returns CLI's
/// `terminal_value_matches_account_balances_realization` test guards that
/// agreement (it values `account_balances`' inventories and compares to
/// [`terminal_value`], which delegates here). Net units are held in a `BTreeMap`
/// so iteration order — hence which currency a `MissingPrice` names — is stable
/// across runs and between 32- and 64-bit targets (an `FxHashMap` would not be).
fn investment_value_at(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    date: NaiveDate,
) -> Result<Decimal, ExtractError> {
    let mut holdings = NetUnits::default();
    for directive in directives {
        if let Directive::Transaction(txn) = directive
            && txn.date <= date
        {
            holdings.apply(txn);
        }
    }
    value_investment_scope(&holdings, scope, reporting_currency, prices, date)
}

/// Net units held per `(account, commodity)`, accumulated by summing complete
/// posting units — **without lot-matching**.
///
/// Market valuation for returns (XIRR/TWR) is `net units × price`; it never needs
/// cost-basis lots. So a lot-matching/cost-basis error — an over-sell with no
/// matching lot, an empty-cost `{}` sale (the common state of imported brokerage
/// data) — simply nets the units (possibly negative) and is valued at market,
/// rather than trapping or refusing the report. `rledger check` remains the
/// validator; the returns report computes over what loaded, like beancount +
/// beangrow (see #1850). `BTreeMap`s keep `MissingPrice` selection deterministic
/// across runs and target word sizes.
#[derive(Default)]
struct NetUnits {
    per_account: std::collections::BTreeMap<
        rustledger_core::Account,
        std::collections::BTreeMap<rustledger_core::Currency, Decimal>,
    >,
    /// Accounts with an elided/uninterpolated posting: a leg's units are unknown,
    /// so the account's net units are incomplete. This is the ONE input the
    /// net-units method genuinely cannot value — valuing such an in-scope account
    /// errors rather than silently understating it.
    unvaluable: std::collections::BTreeSet<rustledger_core::Account>,
}

impl NetUnits {
    fn apply(&mut self, txn: &rustledger_core::Transaction) {
        for posting in &txn.postings {
            if let Some(IncompleteAmount::Complete(amount)) = &posting.units {
                *self
                    .per_account
                    .entry(posting.account.clone())
                    .or_default()
                    .entry(amount.currency.clone())
                    .or_default() += amount.number;
            } else {
                self.unvaluable.insert(posting.account.clone());
            }
        }
    }
}

/// Total market value (in `reporting_currency`, at `date`) of the
/// `Investment`-scope net holdings.
///
/// The single valuation shared by [`investment_value_at`] and the batch
/// [`investment_values_at`] / [`investment_values_multi`], so they cannot drift.
/// Iterates the deterministic `BTreeMap` so which currency a
/// [`ExtractError::MissingPrice`] names is stable.
///
/// # Errors
/// [`ExtractError::MissingPrice`] when an in-scope commodity has no price in
/// `reporting_currency` on `date`, or [`ExtractError::UnbookedInput`] when an
/// in-scope account carried an elided/uninterpolated posting (its net units are
/// incomplete — the one shape net-units cannot value).
fn value_investment_scope(
    holdings: &NetUnits,
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    date: NaiveDate,
) -> Result<Decimal, ExtractError> {
    // An in-scope account carrying an elided/uninterpolated posting has incomplete
    // net units — the one shape net-units cannot value — so error rather than
    // understate it. Scanned over the whole `unvaluable` set (a `BTreeSet`, so the
    // choice of named account is deterministic), including accounts that appear
    // ONLY with an elided leg and so never entered `per_account`.
    for account in &holdings.unvaluable {
        if scope.classify(account.as_str()) == AccountRole::Investment {
            return Err(ExtractError::UnbookedInput(format!(
                "account {account} has an elided/uninterpolated posting; cannot value returns"
            )));
        }
    }
    let mut total = Decimal::ZERO;
    for (account, commodities) in &holdings.per_account {
        if scope.classify(account.as_str()) != AccountRole::Investment {
            continue;
        }
        for (commodity, units) in commodities {
            if units.is_zero() {
                continue;
            }
            let converted = prices
                .convert(
                    &Amount::new(*units, commodity.clone()),
                    reporting_currency,
                    date,
                )
                .ok_or_else(|| ExtractError::MissingPrice {
                    currency: commodity.to_string(),
                    date,
                })?;
            total += converted.number;
        }
    }
    Ok(total)
}

/// Market value of the `Investment`-scope holdings at each date in `dates`
/// (**sorted ascending**) — one entry per date, in order.
///
/// Result is per date rather than one fallible batch: valuing a date is
/// independent, so a `MissingPrice` at one date does not abort the others, and the
/// caller can propagate an error only for a date it actually consumes (matching
/// the old per-date lazy short-circuit in [`twr`]).
///
/// # Fast path vs. fallback
///
/// When `directives` is **date-sorted** (the report's stream is), a single
/// forward pass suffices — `O(directives + dates × accounts)`, each date pricing
/// the in-scope net units, versus the `O(dates × directives)` of a per-date
/// rescan — because the per-date accumulation applies transactions in directive
/// order, which *is* date order, so a cursor that snapshots as it crosses each
/// target date agrees exactly (all same-date transactions applied before that
/// date's snapshot).
///
/// When it is **not** date-sorted, the single pass would skip a later-appearing
/// in-range transaction, so this falls back to the order-independent per-date
/// [`investment_value_at`] — the result then matches `investment_value_at` for
/// *any* input, never silently wrong. The
/// `investment_values_at_matches_per_date` and
/// `investment_values_at_matches_per_date_when_unsorted` tests pin both paths.
fn investment_values_at(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    dates: &[NaiveDate],
) -> Vec<Result<Decimal, ExtractError>> {
    debug_assert!(
        dates.windows(2).all(|w| w[0] <= w[1]),
        "investment_values_at requires ascending dates"
    );

    // The single-pass cursor is only equivalent to the per-date accumulation when
    // transactions are in date order; otherwise fall back to the (order-independent)
    // per-date path so the result is correct for any stream. The check is a cheap
    // O(transactions) date-comparison scan, dominated by the accumulation pass it
    // guards; the report's input is always sorted, so the fast path is the norm.
    let transactions = || {
        directives.iter().filter_map(|directive| match directive {
            Directive::Transaction(txn) => Some(txn),
            _ => None,
        })
    };
    if !transactions().is_sorted_by_key(|txn| txn.date) {
        return dates
            .iter()
            .map(|&date| investment_value_at(directives, scope, reporting_currency, prices, date))
            .collect();
    }

    let mut holdings = NetUnits::default();
    let mut txns = transactions().peekable();
    let mut values = Vec::with_capacity(dates.len());
    for &date in dates {
        // Accumulate every transaction on or before this date (dates and txns both
        // ascend, so the cursor only moves forward across the whole batch).
        while let Some(txn) = txns.peek() {
            if txn.date <= date {
                holdings.apply(txn);
                txns.next();
            } else {
                break;
            }
        }
        values.push(value_investment_scope(
            &holdings,
            scope,
            reporting_currency,
            prices,
            date,
        ));
    }
    values
}

/// Value SEVERAL scopes at their (each ascending) dates in ONE accumulation pass
/// over the whole ledger.
///
/// The net-units forward pass is **scope-independent** — it sums every
/// transaction's units once for every account — so N scopes share a single
/// accumulation; only the per-date valuation ([`value_investment_scope`]) filters
/// by scope. The net-units state at any date is exactly `transactions ≤ date`,
/// identical to what per-scope [`investment_values_at`] would build, so each
/// scope's values match `investment_values_at` for that scope — but the O(N) pass
/// is paid once instead of once per scope. Returns, per scope (in input order),
/// its value at each of its dates. Falls back to per-scope `investment_values_at`
/// on an unsorted stream, matching that function's own fallback. Pinned by
/// `investment_values_multi_matches_per_scope`.
fn investment_values_multi(
    directives: &[Directive],
    scoped_dates: &[(&Scope, &[NaiveDate])],
    reporting_currency: &str,
    prices: &impl PriceOracle,
) -> Vec<Vec<Result<Decimal, ExtractError>>> {
    let transactions = || {
        directives.iter().filter_map(|directive| match directive {
            Directive::Transaction(txn) => Some(txn),
            _ => None,
        })
    };
    if !transactions().is_sorted_by_key(|txn| txn.date) {
        return scoped_dates
            .iter()
            .map(|(scope, dates)| {
                investment_values_at(directives, scope, reporting_currency, prices, dates)
            })
            .collect();
    }

    // Snapshot points are the union of every scope's dates; each scope's dates are
    // a sorted subset, so a per-scope cursor advances monotonically across it.
    let union: std::collections::BTreeSet<NaiveDate> = scoped_dates
        .iter()
        .flat_map(|(_, dates)| dates.iter().copied())
        .collect();

    let mut holdings = NetUnits::default();
    let mut txns = transactions().peekable();
    let mut values: Vec<Vec<Result<Decimal, ExtractError>>> = scoped_dates
        .iter()
        .map(|(_, dates)| Vec::with_capacity(dates.len()))
        .collect();
    let mut cursors = vec![0usize; scoped_dates.len()];

    for &date in &union {
        while let Some(txn) = txns.peek() {
            if txn.date <= date {
                holdings.apply(txn);
                txns.next();
            } else {
                break;
            }
        }
        for (i, (scope, dates)) in scoped_dates.iter().enumerate() {
            // Emit a value for every occurrence of this date in the scope's list
            // (a scope may list `end_date` twice when it coincides with the last
            // flow date), then leave the cursor at the next, later date.
            while cursors[i] < dates.len() && dates[cursors[i]] == date {
                values[i].push(value_investment_scope(
                    &holdings,
                    scope,
                    reporting_currency,
                    prices,
                    date,
                ));
                cursors[i] += 1;
            }
        }
    }
    values
}

/// Annualized **time-weighted return** (TWR) for `scope`, in `reporting_currency`,
/// from ledger inception to `end_date` — or `None` when it is undefined.
///
/// TWR measures how the *investments themselves* performed, independent of the
/// investor's contribution timing (the GIPS / manager-comparison metric). It
/// complements the money-weighted [`xirr`](crate::xirr), which answers "what did *I* earn
/// given when I moved money". Report both, MWR as the headline.
///
/// # Method
///
/// The unit-value (mutual-fund NAV) method. The portfolio is valued at every
/// external cash-flow date; the sub-period return between two consecutive
/// valuations is the market change of the holdings that were present, and the
/// whole-period return is those sub-periods chained geometrically, then
/// annualized. Because each contribution/withdrawal is netted out at its date,
/// only market movement — and income the holdings generate (reinvested
/// dividends, internal reshuffling, which are not external flows) — drives the
/// result; the *timing* of the investor's money does not, which is exactly what
/// distinguishes TWR from MWR.
///
/// Concretely, with the portfolio value `Vᵢ` at flow date `dᵢ`
/// (holdings ≤ `dᵢ` valued at `dᵢ` prices) and the net
/// contribution `Fᵢ` into the portfolio at `dᵢ`, the sub-period return since the
/// previous valuation `Vₚ` is `(Vᵢ − Fᵢ) / Vₚ` — the holdings priced just before
/// the flow, over their value just after the previous one. (`Vᵢ − Fᵢ` assumes a
/// contribution buys assets worth its cash value; an off-market purchase price
/// introduces a small approximation, as in most TWR tools.)
///
/// The whole-period return is **annualized** (`total^(365/days) − 1`), matching
/// hledger. Over a span **shorter than a year this extrapolates**: a +10% return
/// realized in one month reports as ≈ +214%/year. That is the standard
/// convention, but a returns report run a few weeks after the first purchase can
/// show an implausibly large figure for that reason.
///
/// # Returns `None`
///
/// When the return is undefined: no cash flows; the whole span is a single day
/// (nothing to annualize); a **net-short** portfolio (negative value, at any
/// valuation point) where unit accounting is undefined; or a mid-stream full
/// **liquidation-then-refund** (a zero value between two flows, breaking the
/// chain) — both documented limitations of this MVP. A position simply **closed
/// out on the report date** (value zero only at the very end) is *not* `None`:
/// its holding-period return is reported.
///
/// # Performance
///
/// When the stream is date-sorted (the report's input is), the portfolio is
/// valued at every flow date and at `end_date` in a **single forward accumulation
/// pass** (`investment_values_at`): one net-units walk of the stream, snapshotting
/// value as it crosses each date, so cost is `O(directives + flow_dates ×
/// accounts)` — linear in the ledger. An unsorted stream falls back to a per-date
/// accumulation (`O(flow_dates × directives)`), still correct; see
/// `investment_values_at`.
///
/// # Errors
///
/// [`ExtractError::MissingPrice`] if a held commodity cannot be valued at a flow
/// date or at `end_date`. TWR needs a price at *every* flow date, not just the
/// end — a purchase supplies an implicit price at its own date, and
/// [`PriceOracle`] resolves the most recent price on or before a date, so a
/// dividend date with no same-day price still resolves from an earlier one.
///
/// The interpolated, pad-expanded input contract of [`extract_cash_flows`] applies:
/// an in-scope account with an elided/uninterpolated posting surfaces as
/// [`ExtractError::UnbookedInput`] (not a panic), while an un-pad-expanded stream
/// silently omits pad-seeded positions. A cost-basis/lot error is tolerated (net
/// units valued at market).
pub fn twr(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
) -> Result<Option<f64>, ExtractError> {
    // External boundary flows drive the sub-period boundaries. Net them per date
    // and flip to portfolio-centric sign (a contribution INTO the portfolio is
    // positive; CashFlow is investor-centric, so negate). BTreeMap keeps dates
    // ordered.
    let flows = extract_flows(directives, scope, reporting_currency, prices, end_date)?;
    if flows.is_empty() {
        return Ok(None);
    }
    let mut net_by_date: std::collections::BTreeMap<NaiveDate, Decimal> =
        std::collections::BTreeMap::new();
    for flow in &flows {
        *net_by_date.entry(flow.date).or_default() += -flow.amount;
    }

    // Value the portfolio at every flow date and at `end_date` in ONE forward
    // accumulation pass (rather than a fresh pass per date). Flows are all
    // `<= end_date`, so appending `end_date` keeps the date list ascending; the
    // trailing entry is the end valuation.
    let mut dates: Vec<NaiveDate> = net_by_date.keys().copied().collect();
    dates.push(end_date);
    let mut values = investment_values_at(directives, scope, reporting_currency, prices, &dates);
    // Split off the `end_date` valuation; `values` then has exactly one entry per
    // flow date, in `net_by_date` order.
    let end_value = values.pop().expect("dates always includes end_date");
    // An unvaluable (elided-in-scope) stream is more severe than an undefined
    // sub-period: surface `UnbookedInput` EAGERLY, before `twr_from_values`' lazy
    // short-circuits (`v_prev <= 0`, `r <= 0`) could return `Ok(None)` at an
    // earlier flow and mask a later unvaluable value. `MissingPrice` stays lazy (a
    // later price gap is irrelevant once the chain is undefined), but an unvaluable
    // ledger is never silently "n/a". `compute_returns` needs no such scan — it
    // surfaces `UnbookedInput` via its eager `end_value?` — so this lives here, on
    // the standalone public path, not in the shared `twr_from_values` hot path.
    for value in values.iter().chain(std::iter::once(&end_value)) {
        if let Err(e @ ExtractError::UnbookedInput(_)) = value {
            return Err(e.clone());
        }
    }
    twr_from_values(&net_by_date, values, end_value, end_date)
}

/// Chain the sub-period returns from portfolio valuations already computed.
///
/// The unit-value core of [`twr`], factored out so it can run over values
/// snapshotted in a SINGLE forward pass — shared with [`compute_returns`], which
/// derives MWR and the terminal value from the same valuations. `flow_values[i]`
/// is the portfolio value at the i-th flow date (in `net_by_date` order);
/// `end_value` is the value at `end_date`. Each value is a `Result` so a
/// `MissingPrice` at a later date is propagated only if the chain actually reaches
/// it (`?` at the flow it belongs to), preserving the lazy short-circuit — an
/// early undefined sub-period (`Ok(None)`) never surfaces a later price gap.
fn twr_from_values(
    net_by_date: &std::collections::BTreeMap<NaiveDate, Decimal>,
    flow_values: Vec<Result<Decimal, ExtractError>>,
    end_value: Result<Decimal, ExtractError>,
    end_date: NaiveDate,
) -> Result<Option<f64>, ExtractError> {
    // `v_prev` is the portfolio value just after the previous valuation; on the
    // first flow date it is only established (that flow is the opening capital,
    // not a return).
    let mut cumulative = 1.0_f64;
    let mut v_prev: Option<f64> = None;
    let mut first_date: Option<NaiveDate> = None;
    for ((&date, &contribution), value) in net_by_date.iter().zip(flow_values) {
        first_date.get_or_insert(date);
        // A Decimal that can't be represented as f64 makes the return undefined
        // (report n/a), never a silent 0 — which would fabricate a wrong rate.
        let Some(v_i) = value?.to_f64() else {
            return Ok(None);
        };
        if let Some(vp) = v_prev {
            if vp <= 0.0 {
                // Portfolio was non-positive at the *previous* flow (fully
                // liquidated then re-funded mid-stream, or a net short): unit
                // chaining across a zero is undefined — a documented limitation.
                return Ok(None);
            }
            let Some(f) = contribution.to_f64() else {
                return Ok(None);
            };
            let r = (v_i - f) / vp;
            if r <= 0.0 {
                return Ok(None); // sub-period wiped the portfolio out
            }
            cumulative *= r;
        }
        v_prev = Some(v_i);
    }

    // Final sub-period: last flow date → end_date, with no flow. If the position
    // was fully closed at the last flow (`v_prev == 0`), this span holds nothing
    // and contributes no return — the whole-period figure is already in
    // `cumulative`, so a position closed out on the report date still yields its
    // holding-period TWR rather than `None`.
    let Some(v_end) = end_value?.to_f64() else {
        return Ok(None);
    };
    match v_prev {
        Some(vp) if vp > 0.0 => {
            let r = v_end / vp;
            if r <= 0.0 {
                return Ok(None);
            }
            cumulative *= r;
        }
        // Net short (negative value): unit accounting across a non-positive value
        // is undefined — return None, consistent with the in-loop guard that
        // returns None for a mid-stream vp <= 0. (Not the same as a clean close.)
        Some(vp) if vp < 0.0 => return Ok(None),
        // Exactly zero: fully liquidated at the last flow, so the final span holds
        // nothing and contributes no return — the whole-period figure is already
        // in `cumulative` (a position closed out on the report date keeps its TWR).
        Some(_) => {}
        None => return Ok(None), // no flows ⇒ nothing to chain
    }

    // Annualize the total return over [first_date, end_date] (actual/365, the
    // same day count as `xirr`). A zero-length span cannot be annualized.
    let Some(first_date) = first_date else {
        return Ok(None); // no flows
    };
    let days = end_date.since(first_date).map_or(0, |s| s.get_days());
    if days <= 0 {
        return Ok(None);
    }
    let years = f64::from(days) / crate::DAYS_PER_YEAR;
    let annualized = cumulative.powf(1.0 / years) - 1.0;
    Ok(annualized.is_finite().then_some(annualized))
}

/// A scope's full return summary, computed in one pass by [`compute_returns`].
#[derive(Debug, Clone, PartialEq)]
pub struct Returns {
    /// Number of dated cash flows in the money-weighted series — the boundary
    /// flows plus the terminal market value, if nonzero.
    pub cash_flows: usize,
    /// Capital contributed: the sum of outlays (investor-negative flows, sign-flipped).
    pub invested: Decimal,
    /// Distributions received: dividends and sale proceeds (investor-positive flows).
    pub distributions: Decimal,
    /// Market value of the held position at `end_date`.
    pub current_value: Decimal,
    /// Money-weighted return (annualized XIRR); `None` when undefined.
    pub money_weighted: Option<f64>,
    /// Time-weighted return (annualized); `None` when undefined.
    pub time_weighted: Option<f64>,
}

/// Compute a scope's full return summary from a single flow extraction and a
/// single portfolio valuation.
///
/// Folds [`extract_flows`], [`terminal_value`], [`xirr`](crate::xirr), and
/// [`twr`] into one computation: the boundary flows are extracted once, and the
/// portfolio is valued at every flow date and at `end_date` in one forward
/// accumulation pass (on the date-sorted fast path — the report's stream is; an
/// unsorted stream falls back to per-date valuation, see `investment_values_at`),
/// then reused for the terminal value, the money-weighted series, and the
/// time-weighted chaining. A caller needing every figure (the `report returns`
/// breakdown, one call per group) thus avoids the ~2× extraction and ~2× valuation
/// of invoking those functions separately. The result is identical to composing
/// them by hand — pinned by `compute_returns_matches_manual_composition`.
///
/// TWR is `None` for a scope that never held investment capital (an income-only
/// group, or a holding opened but never bought): with no capital there is no
/// holding period to weight, so a flat 0% would be fabricated.
///
/// # Errors
///
/// [`ExtractError::MissingPrice`] if a boundary flow or the `end_date` valuation
/// cannot be priced in `reporting_currency`. A missing price at an *intermediate*
/// flow date degrades TWR to `None` rather than erroring — the summary itself is
/// still well-defined.
///
/// The interpolated, pad-expanded input contract of [`twr`] applies: an in-scope
/// account with an elided/uninterpolated posting surfaces as
/// [`ExtractError::UnbookedInput`] rather than panicking; a cost-basis/lot error is
/// tolerated (net units valued at market). (Date-sorted input is a fast path, not a
/// correctness requirement — an unsorted stream falls back to the order-independent
/// per-date valuation.)
pub fn compute_returns(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
) -> Result<Returns, ExtractError> {
    let flows = extract_flows(directives, scope, reporting_currency, prices, end_date)?;
    // One pass over the flows for all three derived quantities: capital in
    // (outlays), distributions out, and the per-date net (portfolio-centric sign,
    // so a contribution INTO the portfolio is positive) that drives TWR's
    // sub-period boundaries.
    let mut invested = Decimal::ZERO;
    let mut distributions = Decimal::ZERO;
    let mut net_by_date: std::collections::BTreeMap<NaiveDate, Decimal> =
        std::collections::BTreeMap::new();
    for flow in &flows {
        if flow.amount.is_sign_negative() {
            invested += -flow.amount;
        } else {
            distributions += flow.amount;
        }
        *net_by_date.entry(flow.date).or_default() += -flow.amount;
    }

    // One forward accumulation pass: value at every flow date and at `end_date`.
    let mut dates: Vec<NaiveDate> = net_by_date.keys().copied().collect();
    dates.push(end_date);
    let mut values = investment_values_at(directives, scope, reporting_currency, prices, &dates);
    let end_value = values.pop().expect("dates always includes end_date");
    // The terminal is eager: a missing end-date price is a real gap in the summary
    // (matches the old `terminal_value(..)?`).
    let current_value = end_value?;

    // Money-weighted: xirr over the boundary flows plus the terminal value. Only a
    // nonzero terminal becomes a flow — a zero would defeat xirr's degenerate-date
    // guard and fabricate a rate (see `terminal_value`).
    let mut series = flows;
    if !current_value.is_zero() {
        series.push(CashFlow::new(end_date, current_value));
    }
    series.sort_by_key(|f| f.date);
    let cash_flows = series.len();
    let money_weighted = crate::xirr(&series);

    // Time-weighted: chain from the values already realized above. `None` for a
    // scope that never held capital (see the fn docs); a mid-stream price gap
    // degrades to `None` rather than erroring.
    let time_weighted = if invested.is_zero() && current_value.is_zero() {
        None
    } else {
        twr_from_values(&net_by_date, values, Ok(current_value), end_date).unwrap_or(None)
    };

    Ok(Returns {
        cash_flows,
        invested,
        distributions,
        current_value,
        money_weighted,
        time_weighted,
    })
}

/// Compute [`compute_returns`] for SEVERAL scopes while accumulating the portfolio
/// only ONCE.
///
/// `report returns --by-group` computes one summary for the whole scope plus one
/// per group; calling [`compute_returns`] for each re-runs the accumulation pass
/// every time even though it is scope-independent. This shares a single net-units
/// accumulation across all scopes (see `investment_values_multi`), turning the
/// per-group cost from `O(scopes × directives)` into `O(directives)`. Flow
/// extraction and valuation are still per scope (they must be), so the result for
/// each scope is **identical** to `compute_returns(that scope)` — pinned by
/// `compute_returns_multi_matches_per_scope`. Returns one result per input scope,
/// in order.
///
/// # Errors
///
/// Both error kinds are **per-scope independent** — reported in the offending
/// scope's slot without affecting the others — because valuation runs per scope
/// over the shared accumulation. A [`ExtractError::MissingPrice`] names an
/// unpriceable boundary flow or `end_date` valuation. An
/// [`ExtractError::UnbookedInput`] names a scope whose Investment accounts include
/// one with an elided/uninterpolated posting; a scope that does not classify that
/// account as Investment is unaffected. A cost-basis/lot error affects no scope
/// (net units valued at market). (Date-sorted is a fast path, not a requirement —
/// an unsorted stream falls back to per-scope valuation.)
#[must_use]
pub fn compute_returns_multi(
    directives: &[Directive],
    scopes: &[Scope],
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
) -> Vec<Result<Returns, ExtractError>> {
    /// Per-scope work computed before the shared accumulation.
    struct Prep {
        flows: Vec<CashFlow>,
        invested: Decimal,
        distributions: Decimal,
        net_by_date: std::collections::BTreeMap<NaiveDate, Decimal>,
        dates: Vec<NaiveDate>,
    }

    // Extract flows and derive the per-date net for each scope. Extraction can
    // fail per scope (an unpriceable boundary flow); such a scope is reported as
    // that error and sits out the shared valuation.
    let preps: Vec<Result<Prep, ExtractError>> = scopes
        .iter()
        .map(|scope| {
            let flows = extract_flows(directives, scope, reporting_currency, prices, end_date)?;
            let mut invested = Decimal::ZERO;
            let mut distributions = Decimal::ZERO;
            let mut net_by_date: std::collections::BTreeMap<NaiveDate, Decimal> =
                std::collections::BTreeMap::new();
            for flow in &flows {
                if flow.amount.is_sign_negative() {
                    invested += -flow.amount;
                } else {
                    distributions += flow.amount;
                }
                *net_by_date.entry(flow.date).or_default() += -flow.amount;
            }
            let mut dates: Vec<NaiveDate> = net_by_date.keys().copied().collect();
            dates.push(end_date);
            Ok(Prep {
                flows,
                invested,
                distributions,
                net_by_date,
                dates,
            })
        })
        .collect();

    // ONE accumulation pass over the union of the ready scopes' dates.
    let scoped_dates: Vec<(&Scope, &[NaiveDate])> = preps
        .iter()
        .zip(scopes)
        .filter_map(|(prep, scope)| prep.as_ref().ok().map(|p| (scope, p.dates.as_slice())))
        .collect();
    let mut shared_values =
        investment_values_multi(directives, &scoped_dates, reporting_currency, prices).into_iter();

    // Assemble each scope's `Returns` from its shared values. The failed preps are
    // skipped here exactly as they were skipped when building `scoped_dates`, so
    // `shared_values` stays aligned with the ready scopes in order.
    preps
        .into_iter()
        .map(|prep| {
            let prep = prep?;
            let mut values = shared_values
                .next()
                .expect("one value vector per ready scope");
            let end_value = values.pop().expect("dates always includes end_date");
            let current_value = end_value?;

            let mut series = prep.flows;
            if !current_value.is_zero() {
                series.push(CashFlow::new(end_date, current_value));
            }
            series.sort_by_key(|f| f.date);
            let cash_flows = series.len();
            let money_weighted = crate::xirr(&series);

            let time_weighted = if prep.invested.is_zero() && current_value.is_zero() {
                None
            } else {
                twr_from_values(&prep.net_by_date, values, Ok(current_value), end_date)
                    .unwrap_or(None)
            };

            Ok(Returns {
                cash_flows,
                invested: prep.invested,
                distributions: prep.distributions,
                current_value,
                money_weighted,
                time_weighted,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal::Decimal;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Posting, Transaction, naive_date};
    use std::collections::HashMap;

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn amt(n: Decimal, ccy: &str) -> Amount {
        Amount::new(n, ccy)
    }

    /// A trivial [`PriceOracle`] backed by an explicit `(base, quote, date) ->
    /// rate` table, with same-currency handled as rate 1. Missing entries mean
    /// "no price" so tests can exercise the failure path.
    #[derive(Default)]
    struct MockPrices {
        rates: HashMap<(String, String, NaiveDate), Decimal>,
    }

    impl MockPrices {
        fn with(mut self, base: &str, quote: &str, date: NaiveDate, rate: Decimal) -> Self {
            self.rates
                .insert((base.to_string(), quote.to_string(), date), rate);
            self
        }
    }

    impl PriceOracle for MockPrices {
        fn convert(&self, amount: &Amount, to_currency: &str, date: NaiveDate) -> Option<Amount> {
            if amount.currency == to_currency {
                return Some(amount.clone());
            }
            let rate =
                self.rates
                    .get(&(amount.currency.to_string(), to_currency.to_string(), date))?;
            Some(Amount::new(amount.number * rate, to_currency))
        }
    }

    fn txn(date: NaiveDate, postings: Vec<Posting>) -> Directive {
        let mut t = Transaction::new(date, "test");
        for p in postings {
            t = t.with_synthesized_posting(p);
        }
        Directive::Transaction(t)
    }

    fn invest_scope() -> Scope {
        Scope::new(
            vec!["Assets:Broker".to_string()],
            vec!["Income:Dividends".to_string()],
        )
    }

    /// Net-units valuation tolerates a cost-basis/lot error. The loader re-merges
    /// booking-FAILED transactions in their un-booked shape, so a returns consumer
    /// can hand `compute_returns` a reduction of more units than were ever held —
    /// the common state of imported brokerage data (empty-cost `{}` sales, no
    /// matching lot). Because returns value **net units at market** (never
    /// cost-basis lots), this must NOT trap, refuse the report, nor understate:
    /// buying 5 then reducing 10 nets to −5 units, valued at the terminal price.
    /// `rledger check` remains the validator; the returns report computes over
    /// what loaded (like beancount + beangrow). See #1850.
    #[test]
    fn oversell_nets_negative_valued_at_market() {
        use rustledger_core::{CostNumber, CostSpec};
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(5), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number(CostNumber::PerUnit { value: dec!(100) })
                            .with_currency("USD"),
                    ),
                    Posting::new("Assets:Bank", amt(dec!(-500), "USD")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL"))
                        .with_cost(CostSpec::empty()),
                    Posting::new("Assets:Bank", amt(dec!(1000), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(120));
        let r = compute_returns(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31))
            .expect("net-units valuation tolerates an over-sell");
        // Net −5 AAPL × 120 = −600; not a trap, not an UnbookedInput refusal.
        assert_eq!(r.current_value, dec!(-600));
    }

    /// The one shape net-units genuinely cannot value: an in-scope account with an
    /// elided/uninterpolated posting (booking would have filled it). Its net units
    /// are incomplete, so valuing it must surface as [`ExtractError::UnbookedInput`]
    /// rather than silently understate the position. This is distinct from a
    /// cost-basis error (tolerated, see `oversell_nets_negative_valued_at_market`) —
    /// here the units themselves are unknown.
    #[test]
    fn elided_in_scope_posting_errors_not_understates() {
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                // Elided in-scope investment leg (no units) — its net units are unknown.
                Posting::auto("Assets:Broker:Stock"),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(120));
        let r = compute_returns(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31));
        assert!(
            matches!(r, Err(ExtractError::UnbookedInput(_))),
            "an elided in-scope posting must yield UnbookedInput, got {r:?}"
        );
    }

    /// The FLOWS counterpart: an elided **external** (boundary cash) leg of a
    /// portfolio-touching transaction is a contribution of unknown magnitude. It
    /// must surface as [`ExtractError::UnbookedInput`], NOT be silently dropped —
    /// dropping it would value the (complete) investment leg at market with no
    /// matching outflow, understating `invested` and reporting a wrong
    /// money-weighted return while exiting `Ok`. The investment leg here is
    /// complete, so only the elided external leg triggers the error.
    #[test]
    fn elided_external_leg_errors_not_dropped() {
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                // Complete in-scope buy...
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                // ...but the boundary cash leg is elided (interpolation failed).
                Posting::auto("Assets:Bank"),
            ],
        )];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(120));
        let flows = extract_flows(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31));
        assert!(
            matches!(flows, Err(ExtractError::UnbookedInput(_))),
            "an elided external leg must yield UnbookedInput, got {flows:?}"
        );
        // And the whole summary errors rather than reporting a wrong figure.
        let r = compute_returns(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31));
        assert!(
            matches!(r, Err(ExtractError::UnbookedInput(_))),
            "compute_returns must not report a figure over a dropped flow, got {r:?}"
        );
    }

    /// Per-scope isolation — what `--by-group` partial rendering relies on. Over
    /// ONE shared accumulation, [`compute_returns_multi`] returns
    /// [`ExtractError::UnbookedInput`] for a scope whose Investment accounts include
    /// an elided posting, while a DISJOINT scope that excludes that account still
    /// computes `Ok`. (The elided account is marked unvaluable globally, but a scope
    /// errors only if it classifies that account as `Investment`.)
    #[test]
    fn compute_returns_multi_isolates_an_unvaluable_scope() {
        let dirs = vec![
            // Clean group: a complete, priceable buy.
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Clean", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            // Broken group: an elided in-scope leg → net units unknown.
            txn(
                d(2020, 3, 1),
                vec![
                    Posting::auto("Assets:Broker:Broken"),
                    Posting::new("Assets:Bank", amt(dec!(-500), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(130));
        let clean = Scope::new(vec!["Assets:Broker:Clean".to_string()], vec![]);
        let broken = Scope::new(vec!["Assets:Broker:Broken".to_string()], vec![]);
        let out = compute_returns_multi(&dirs, &[clean, broken], "USD", &prices, d(2020, 12, 31));
        assert_eq!(
            out[0].as_ref().expect("clean scope computes").current_value,
            dec!(1300),
            "net 10 AAPL × 130",
        );
        assert!(
            matches!(out[1], Err(ExtractError::UnbookedInput(_))),
            "the elided scope fails alone: {:?}",
            out[1]
        );
    }

    /// The public `twr` surfaces an elided-in-scope posting as `UnbookedInput` via
    /// its eager scan, rather than masking it as `Ok(None)` through
    /// `twr_from_values`' lazy short-circuits. The first flow date values cleanly
    /// (net 5 AAPL priced), so only the eager scan reaches the later elided date.
    /// (`compute_returns` is protected separately by its eager terminal valuation.)
    #[test]
    fn twr_surfaces_unbooked_input() {
        use rustledger_core::{CostNumber, CostSpec};
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(5), "AAPL")).with_cost(
                        CostSpec::empty()
                            .with_number(CostNumber::PerUnit { value: dec!(100) })
                            .with_currency("USD"),
                    ),
                    Posting::new("Assets:Bank", amt(dec!(-500), "USD")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    // Elided in-scope leg — net units become unknown from here.
                    Posting::auto("Assets:Broker:Stock"),
                    Posting::new("Assets:Bank", amt(dec!(-100), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 12, 31), dec!(120));
        let r = twr(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31));
        assert!(
            matches!(r, Err(ExtractError::UnbookedInput(_))),
            "twr must surface UnbookedInput, not swallow it to {r:?}"
        );
    }

    #[test]
    fn purchase_is_a_negative_flow() {
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        let flows = extract_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 1, 1),
        )
        .unwrap();
        assert_eq!(flows, vec![CashFlow::new(d(2020, 1, 1), dec!(-1000))]);
    }

    #[test]
    fn sale_is_a_positive_flow() {
        let dirs = vec![txn(
            d(2021, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(1100), "USD")),
            ],
        )];
        let flows = extract_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2021, 1, 1),
        )
        .unwrap();
        assert_eq!(flows, vec![CashFlow::new(d(2021, 1, 1), dec!(1100))]);
    }

    #[test]
    fn dividend_paid_to_bank_is_a_positive_flow() {
        // Touches an income account (not an investment one) — still relevant.
        let dirs = vec![txn(
            d(2020, 6, 1),
            vec![
                Posting::new("Assets:Bank", amt(dec!(5), "USD")),
                Posting::new("Income:Dividends", amt(dec!(-5), "USD")),
            ],
        )];
        let flows = extract_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 6, 1),
        )
        .unwrap();
        assert_eq!(flows, vec![CashFlow::new(d(2020, 6, 1), dec!(5))]);
    }

    #[test]
    fn investment_fee_scoped_as_pnl_reduces_proceeds_to_net() {
        // Sell for 1100 gross, pay a 10 fee, net 1090 to the bank. With the fee
        // account scoped as income/P&L, only the 1090 that reached the investor
        // is a flow — the fee is a drag, not proceeds. (Left External, the fee
        // would leak in and the flow would wrongly be +1100.)
        let scope = Scope::new(
            vec!["Assets:Broker".to_string()],
            vec!["Income:Gains".to_string(), "Expenses:Fees".to_string()],
        );
        let dirs = vec![txn(
            d(2021, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(1090), "USD")),
                Posting::new("Expenses:Fees", amt(dec!(10), "USD")),
                Posting::new("Income:Gains", amt(dec!(-100), "USD")),
            ],
        )];
        let flows =
            extract_flows(&dirs, &scope, "USD", &MockPrices::default(), d(2021, 1, 1)).unwrap();
        assert_eq!(flows, vec![CashFlow::new(d(2021, 1, 1), dec!(1090))]);
    }

    #[test]
    fn internal_transfer_between_investment_accounts_is_not_a_flow() {
        // The correctness trap: moving shares between two in-scope accounts must
        // NOT register as a cash flow.
        let dirs = vec![txn(
            d(2020, 3, 1),
            vec![
                Posting::new("Assets:Broker:Old", amt(dec!(-10), "AAPL")),
                Posting::new("Assets:Broker:New", amt(dec!(10), "AAPL")),
            ],
        )];
        let flows = extract_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 3, 1),
        )
        .unwrap();
        assert!(
            flows.is_empty(),
            "internal transfer must not produce a flow"
        );
    }

    #[test]
    fn reinvested_dividend_stays_inside_and_is_not_a_flow() {
        // Dividend lands in in-scope broker cash from an in-scope income account
        // — both inside the boundary, so no external money moved.
        let scope = Scope::new(
            vec!["Assets:Broker".to_string()],
            vec!["Income:Dividends".to_string()],
        );
        let dirs = vec![txn(
            d(2020, 6, 1),
            vec![
                Posting::new("Assets:Broker:Cash", amt(dec!(5), "USD")),
                Posting::new("Income:Dividends", amt(dec!(-5), "USD")),
            ],
        )];
        let flows =
            extract_flows(&dirs, &scope, "USD", &MockPrices::default(), d(2020, 6, 1)).unwrap();
        assert!(flows.is_empty());
    }

    #[test]
    fn transaction_not_touching_the_portfolio_is_ignored() {
        // A grocery purchase in a currency with no price must not error — it is
        // irrelevant, so its unconvertible amount is never inspected.
        let dirs = vec![txn(
            d(2020, 2, 1),
            vec![
                Posting::new("Expenses:Food", amt(dec!(5), "GBP")),
                Posting::new("Assets:Bank", amt(dec!(-5), "GBP")),
            ],
        )];
        let flows = extract_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 2, 1),
        )
        .unwrap();
        assert!(flows.is_empty());
    }

    #[test]
    fn multi_currency_flow_is_converted_to_the_reporting_currency() {
        // Buy a foreign holding paid from a EUR account; reporting in USD.
        let dirs = vec![txn(
            d(2020, 1, 2),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "FOO")),
                Posting::new("Assets:BankEUR", amt(dec!(-80), "EUR")),
            ],
        )];
        let prices = MockPrices::default().with("EUR", "USD", d(2020, 1, 2), dec!(1.1));
        let flows = extract_flows(&dirs, &invest_scope(), "USD", &prices, d(2020, 1, 2)).unwrap();
        // -80 EUR * 1.1 = -88 USD.
        assert_eq!(flows, vec![CashFlow::new(d(2020, 1, 2), dec!(-88.0))]);
    }

    #[test]
    fn missing_price_on_a_relevant_flow_is_an_error() {
        let dirs = vec![txn(
            d(2020, 1, 2),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "FOO")),
                Posting::new("Assets:BankEUR", amt(dec!(-80), "EUR")),
            ],
        )];
        // No EUR->USD rate supplied.
        let err = extract_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 1, 2),
        )
        .unwrap_err();
        assert_eq!(
            err,
            ExtractError::MissingPrice {
                currency: "EUR".to_string(),
                date: d(2020, 1, 2)
            }
        );
    }

    #[test]
    fn flows_after_the_end_date_are_excluded() {
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            txn(
                d(2021, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(1100), "USD")),
                ],
            ),
        ];
        let flows = extract_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 6, 1),
        )
        .unwrap();
        // Only the purchase is on or before the horizon.
        assert_eq!(flows, vec![CashFlow::new(d(2020, 1, 1), dec!(-1000))]);
    }

    #[test]
    fn terminal_value_prices_the_held_position() {
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(150));
        let terminal =
            terminal_value(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        // 10 AAPL * 150 = 1500 USD, a positive terminal flow on the end date.
        assert_eq!(terminal, Some(CashFlow::new(d(2020, 12, 31), dec!(1500))));
    }

    #[test]
    fn terminal_value_is_none_when_nothing_is_held() {
        // Bought then fully sold before the horizon → no remaining position.
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(1100), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(150));
        let terminal =
            terminal_value(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        assert_eq!(terminal, None);
    }

    #[test]
    fn terminal_value_missing_price_is_an_error() {
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        // No AAPL->USD rate on the end date.
        let err = terminal_value(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 12, 31),
        )
        .unwrap_err();
        assert_eq!(
            err,
            ExtractError::MissingPrice {
                currency: "AAPL".to_string(),
                date: d(2020, 12, 31)
            }
        );
    }

    #[test]
    fn full_series_feeds_xirr_to_a_sensible_rate() {
        // Buy 1000 USD of stock, hold a year, position now worth 1100 → ~10%.
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(110));
        let flows =
            extract_cash_flows(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        // -1000 on 2020-01-01, +1100 terminal on 2020-12-31.
        assert_eq!(
            flows,
            vec![
                CashFlow::new(d(2020, 1, 1), dec!(-1000)),
                CashFlow::new(d(2020, 12, 31), dec!(1100)),
            ]
        );
        let rate = crate::xirr(&flows).unwrap();
        // 365-day year, 364 days elapsed → a touch above 10%.
        assert!((rate - 0.10).abs() < 0.01, "unexpected rate {rate}");
    }

    #[test]
    fn broker_cash_counts_toward_terminal_value() {
        // Uninvested cash sitting in an in-scope broker account is part of the
        // portfolio's remaining value.
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Cash", amt(dec!(250), "USD")),
                Posting::new("Assets:Bank", amt(dec!(-250), "USD")),
            ],
        )];
        let terminal = terminal_value(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 12, 31),
        )
        .unwrap();
        // Same-currency, no rate needed: 250 USD held.
        assert_eq!(terminal, Some(CashFlow::new(d(2020, 12, 31), dec!(250))));
    }

    #[test]
    fn opening_balance_pairs_with_terminal_to_a_zero_return() {
        // A pad-expanded opening balance: `Assets:Broker:Cash 500 /
        // Equity:Opening-Balances -500`, the synthesized transaction the loader's
        // balance_view produces. The Equity leg is External, so the opening
        // capital registers as a -500 flow — and that flow must PAIR with the
        // +500 the account contributes to the terminal value. An untouched
        // opening balance is a 0% return, not an undefined one; dropping the
        // opening flow (e.g. by extracting flows from a non-pad-expanded stream)
        // would leave a +500 terminal with no offsetting outlay.
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Cash", amt(dec!(500), "USD")),
                Posting::new("Equity:Opening-Balances", amt(dec!(-500), "USD")),
            ],
        )];
        let flows = extract_cash_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 12, 31),
        )
        .unwrap();
        assert_eq!(
            flows,
            vec![
                CashFlow::new(d(2020, 1, 1), dec!(-500)),
                CashFlow::new(d(2020, 12, 31), dec!(500)),
            ]
        );
        let rate = crate::xirr(&flows).unwrap();
        assert!(
            rate.abs() < 1e-6,
            "untouched opening balance must be ~0%, got {rate}"
        );
    }

    #[test]
    fn opening_balance_then_internal_growth_is_a_positive_return() {
        // Open with 500, receive a 50 dividend into broker cash from an in-scope
        // income account (stays inside — no external flow), end worth 550.
        // Return is computed on the 500 opening capital: +10%.
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Cash", amt(dec!(500), "USD")),
                    Posting::new("Equity:Opening-Balances", amt(dec!(-500), "USD")),
                ],
            ),
            txn(
                d(2020, 12, 31),
                vec![
                    Posting::new("Assets:Broker:Cash", amt(dec!(50), "USD")),
                    Posting::new("Income:Dividends", amt(dec!(-50), "USD")),
                ],
            ),
        ];
        let flows = extract_cash_flows(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2020, 12, 31),
        )
        .unwrap();
        // Only the opening -500 and the +550 terminal are flows; the dividend
        // stays inside the boundary.
        assert_eq!(
            flows,
            vec![
                CashFlow::new(d(2020, 1, 1), dec!(-500)),
                CashFlow::new(d(2020, 12, 31), dec!(550)),
            ]
        );
        let rate = crate::xirr(&flows).unwrap();
        assert!((rate - 0.10).abs() < 0.001, "expected ~10%, got {rate}");
    }

    #[test]
    fn classify_is_segment_aware_and_investment_wins() {
        let scope = Scope::new(
            vec!["Assets:Broker".to_string()],
            vec!["Income:Dividends".to_string()],
        );
        assert_eq!(scope.classify("Assets:Broker"), AccountRole::Investment);
        assert_eq!(
            scope.classify("Assets:Broker:Cash"),
            AccountRole::Investment
        );
        // Segment boundary: not a subaccount of "Assets:Broker".
        assert_eq!(scope.classify("Assets:Brokerage"), AccountRole::External);
        assert_eq!(scope.classify("Income:Dividends"), AccountRole::Income);
        assert_eq!(scope.classify("Income:Salary"), AccountRole::External);
        assert_eq!(scope.classify("Assets:Bank"), AccountRole::External);
    }

    #[test]
    fn classify_prefers_the_longer_prefix_when_income_nests_under_investment() {
        // Income scoped to a subaccount of the investment prefix: the more
        // specific (longer) match wins, so the dividend account is Income even
        // though "Assets:Broker" also matches it.
        let scope = Scope::new(
            vec!["Assets:Broker".to_string()],
            vec!["Assets:Broker:Dividends".to_string()],
        );
        assert_eq!(
            scope.classify("Assets:Broker:Dividends"),
            AccountRole::Income
        );
        assert_eq!(
            scope.classify("Assets:Broker:Dividends:Foreign"),
            AccountRole::Income
        );
        assert_eq!(
            scope.classify("Assets:Broker:Cash"),
            AccountRole::Investment
        );
        assert_eq!(scope.classify("Assets:Broker"), AccountRole::Investment);
    }

    #[test]
    fn nested_income_account_does_not_cancel_terminal_value() {
        // Regression for the overlapping-prefix bug: a reinvested dividend booked
        // into an in-scope broker cash account against an income account nested
        // under the investment prefix. Longest-prefix classification keeps the
        // income leg out of the terminal so the +5 asset it created survives.
        let scope = Scope::new(
            vec!["Assets:Broker".to_string()],
            vec!["Assets:Broker:Dividends".to_string()],
        );
        let dirs = vec![txn(
            d(2020, 6, 1),
            vec![
                Posting::new("Assets:Broker:Cash", amt(dec!(5), "USD")),
                Posting::new("Assets:Broker:Dividends", amt(dec!(-5), "USD")),
            ],
        )];
        let terminal = terminal_value(
            &dirs,
            &scope,
            "USD",
            &MockPrices::default(),
            d(2020, 12, 31),
        )
        .unwrap();
        // Broker:Cash (+5, Investment) counted; Broker:Dividends (-5, Income)
        // excluded. Were both Investment, this would wrongly net to 0.
        assert_eq!(terminal, Some(CashFlow::new(d(2020, 12, 31), dec!(5))));
    }

    #[test]
    fn terminal_value_of_a_short_position_is_negative() {
        // A short sale leaves -10 AAPL held; its terminal value is negative.
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(1500), "USD")),
            ],
        )];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(150));
        let terminal =
            terminal_value(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        // -10 AAPL * 150 = -1500 USD.
        assert_eq!(terminal, Some(CashFlow::new(d(2020, 12, 31), dec!(-1500))));
    }

    #[test]
    fn terminal_value_sums_multiple_held_positions() {
        // Two distinct commodities held in the same investment account are two
        // positions; the terminal must sum both, not value only the first.
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Broker:Stock", amt(dec!(5), "GOOG")),
                Posting::new("Assets:Bank", amt(dec!(-2500), "USD")),
            ],
        )];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 12, 31), dec!(150))
            .with("GOOG", "USD", d(2020, 12, 31), dec!(200));
        let terminal =
            terminal_value(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        // 10*150 + 5*200 = 1500 + 1000 = 2500.
        assert_eq!(terminal, Some(CashFlow::new(d(2020, 12, 31), dec!(2500))));
    }

    #[test]
    fn net_flat_held_portfolio_yields_no_terminal_flow() {
        // Two positions whose market values cancel to exactly zero. Even though a
        // position is still held, no terminal flow is emitted: a zero flow on a
        // later date is NOT neutral to xirr (it defeats the all-same-date
        // degenerate guard). None is correct here.
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Broker:Stock", amt(dec!(-10), "GOOG")),
                Posting::new("Assets:Bank", amt(dec!(0), "USD")),
            ],
        )];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 12, 31), dec!(150))
            .with("GOOG", "USD", d(2020, 12, 31), dec!(150));
        let terminal =
            terminal_value(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        assert_eq!(terminal, None);
    }

    #[test]
    fn worthless_holding_with_a_same_date_wash_does_not_fabricate_a_return() {
        // Regression: a zero-valued terminal flow used to be emitted for a held
        // but worthless position. Combined with a same-date deposit/withdrawal
        // wash it defeated xirr's degenerate guard and fabricated a +10% return
        // (xirr's Newton seed) for a genuinely-undefined series. With no zero
        // terminal, the two same-date flows are all that remain and xirr
        // correctly reports None.
        let dirs = vec![
            // Buy a stock that ends up worthless (priced 0 at end_date): -1000 out.
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "FOO")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            // Same-day dividend to the bank: +1000 in. Together with the buy this
            // is a sign-changing wash on 2020-01-01.
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Bank", amt(dec!(1000), "USD")),
                    Posting::new("Income:Dividends", amt(dec!(-1000), "USD")),
                ],
            ),
        ];
        // FOO is worthless at the horizon.
        let prices = MockPrices::default().with("FOO", "USD", d(2020, 12, 31), dec!(0));
        let flows =
            extract_cash_flows(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        // Only the two same-date flows; no zero terminal.
        assert_eq!(
            flows,
            vec![
                CashFlow::new(d(2020, 1, 1), dec!(-1000)),
                CashFlow::new(d(2020, 1, 1), dec!(1000)),
            ]
        );
        // All flows share a date → the return is undefined, not +10%.
        assert_eq!(crate::xirr(&flows), None);
    }

    #[test]
    fn a_flow_and_the_terminal_can_share_the_end_date() {
        // Partial sale ON the end date plus the residual terminal ON the end date
        // — two flows share a date. xirr must still resolve a sensible rate.
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            txn(
                d(2020, 12, 31),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-4), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(600), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 12, 31), dec!(150));
        let flows =
            extract_cash_flows(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31)).unwrap();
        // -1000 @ open; +600 sale and +900 residual (6 AAPL * 150) both @ end.
        assert_eq!(
            flows,
            vec![
                CashFlow::new(d(2020, 1, 1), dec!(-1000)),
                CashFlow::new(d(2020, 12, 31), dec!(600)),
                CashFlow::new(d(2020, 12, 31), dec!(900)),
            ]
        );
        let rate = crate::xirr(&flows).unwrap();
        // 1500 back on 1000 over ~1yr → ~50%.
        assert!((rate - 0.50).abs() < 0.01, "expected ~50%, got {rate}");
    }

    #[test]
    fn twr_single_flow_is_the_holding_period_return() {
        // One purchase held for a year, +10% → TWR 10% (matches MWR when there
        // is a single flow).
        let dirs = vec![txn(
            d(2021, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2021, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2022, 1, 1), dec!(110));
        let rate = twr(&dirs, &invest_scope(), "USD", &prices, d(2022, 1, 1))
            .unwrap()
            .expect("defined");
        assert!((rate - 0.10).abs() < 1e-9, "expected 10%, got {rate}");
    }

    #[test]
    fn twr_neutralizes_contribution_timing_unlike_mwr() {
        // A small position sits flat for the first half-year (0%), then a large
        // contribution goes in right before a +20% second half. TWR reflects the
        // investments' performance (0% then 20%, chained = 20%); MWR is pulled
        // much higher because most of the money was present only for the gain.
        let dirs = vec![
            txn(
                d(2021, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(1), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-100), "USD")),
                ],
            ),
            txn(
                d(2021, 7, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2021, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2021, 7, 1), dec!(100)) // flat first half
            .with("AAPL", "USD", d(2022, 1, 1), dec!(120)); // +20% second half
        let end = d(2022, 1, 1);

        let tw = twr(&dirs, &invest_scope(), "USD", &prices, end)
            .unwrap()
            .expect("defined");
        // 1.0 (flat) * 1.2 (+20%) over 365 days → 20%.
        assert!((tw - 0.20).abs() < 1e-9, "expected TWR 20%, got {tw}");

        // MWR on the same ledger is materially higher (good contribution timing).
        let series = extract_cash_flows(&dirs, &invest_scope(), "USD", &prices, end).unwrap();
        let mw = crate::xirr(&series).unwrap();
        assert!(
            mw > tw + 0.10,
            "MWR ({mw}) should far exceed TWR ({tw}) given the timing",
        );
    }

    #[test]
    fn twr_is_none_without_flows() {
        // No transaction touches the investment scope → no flows → undefined.
        let dirs = vec![txn(
            d(2021, 1, 1),
            vec![
                Posting::new("Expenses:Food", amt(dec!(5), "USD")),
                Posting::new("Assets:Bank", amt(dec!(-5), "USD")),
            ],
        )];
        let rate = twr(
            &dirs,
            &invest_scope(),
            "USD",
            &MockPrices::default(),
            d(2021, 12, 31),
        )
        .unwrap();
        assert_eq!(rate, None);
    }

    #[test]
    fn twr_over_a_single_day_is_none() {
        // Buy and report on the same day: no elapsed time to annualize.
        let dirs = vec![txn(
            d(2021, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        let prices = MockPrices::default().with("AAPL", "USD", d(2021, 1, 1), dec!(100));
        let rate = twr(&dirs, &invest_scope(), "USD", &prices, d(2021, 1, 1)).unwrap();
        assert_eq!(rate, None);
    }

    #[test]
    fn twr_missing_price_after_an_undefined_subperiod_is_none_not_err() {
        // The single-pass rework values every date up front but must preserve the
        // old LAZY short-circuit: an early sub-period already made the return
        // undefined (here the portfolio is net short, so the second flow trips the
        // `vp <= 0` guard → Ok(None)), so a MissingPrice at the report end date
        // must NOT surface — twr returns Ok(None), never Err(MissingPrice).
        // Regression guard: if `investment_values_at`'s per-date results were ever
        // `?`-propagated eagerly, this would flip to Err and the test would fail.
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(1000), "USD")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-1), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(100), "USD")),
                ],
            ),
        ];
        // Priced at the two flow dates, but NOT at the 2020-12-31 report date.
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 6, 1), dec!(100));
        let result = twr(&dirs, &invest_scope(), "USD", &prices, d(2020, 12, 31))
            .expect("must be Ok(None), not Err(MissingPrice) — the end price is never reached");
        assert_eq!(result, None);
    }

    #[test]
    fn twr_of_a_position_closed_out_on_the_report_date() {
        // Buy 10 AAPL @100, sell all @110 on the end date. The position is fully
        // liquidated at the last flow, so v_prev hits 0 — but the ~10% return was
        // already captured before the sale, and must not be discarded as None.
        // This also exercises the withdrawal (outflow) sign path.
        let dirs = vec![
            txn(
                d(2021, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            txn(
                d(2021, 12, 31),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(1100), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default().with("AAPL", "USD", d(2021, 1, 1), dec!(100));
        let rate = twr(&dirs, &invest_scope(), "USD", &prices, d(2021, 12, 31))
            .unwrap()
            .expect("a closed-out position still has a defined TWR");
        // Bought at 1000-worth, sold for 1100 → ~10% over ~1yr.
        assert!((rate - 0.10).abs() < 0.001, "expected ~10%, got {rate}");
    }

    #[test]
    fn twr_of_a_net_short_position_is_none() {
        // A held short position leaves the portfolio value negative at the report
        // date. Unit accounting across a non-positive value is undefined, so TWR
        // is None — NOT a fabricated 0% (regression: the closed-out fix must not
        // treat a negative value the same as a fully-liquidated zero).
        let dirs = vec![txn(
            d(2021, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(1000), "USD")),
            ],
        )];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2021, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2021, 12, 31), dec!(100));
        let rate = twr(&dirs, &invest_scope(), "USD", &prices, d(2021, 12, 31)).unwrap();
        assert_eq!(rate, None);
    }

    #[test]
    fn twr_credits_a_dividend_to_bank_as_return() {
        // Marquee TWR path: a cash dividend paid OUT to the bank leaves the
        // holdings' units unchanged but IS return the investment generated. It
        // must be credited exactly once, in its sub-period.
        //   Jan–Jul: 10 AAPL flat at 100 (1000→1000) but a 50 dividend paid out
        //            → sub-period return (1000 + 50)/1000 = 1.05
        //   Jul–Jan: 100 → 110 → 1.10
        //   chained: 1.05 * 1.10 = 1.155 → 15.5% over the year.
        let dirs = vec![
            txn(
                d(2021, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            txn(
                d(2021, 7, 1),
                vec![
                    Posting::new("Assets:Bank", amt(dec!(50), "USD")),
                    Posting::new("Income:Dividends", amt(dec!(-50), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2021, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2021, 7, 1), dec!(100)) // flat: sub-period 1 is the dividend
            .with("AAPL", "USD", d(2022, 1, 1), dec!(110)); // +10% second half
        let rate = twr(&dirs, &invest_scope(), "USD", &prices, d(2022, 1, 1))
            .unwrap()
            .expect("defined");
        assert!((rate - 0.155).abs() < 0.001, "expected ~15.5%, got {rate}");
    }

    /// Drift guard (CLAUDE.md Canonical-Function Discipline): the single-pass
    /// `investment_values_at` must return exactly what calling the per-date
    /// `investment_value_at` yields for each date — the two share
    /// `value_investment_scope`, and `twr` now relies on the batch version. Uses
    /// a multi-buy/partial-sale/same-date portfolio valued at dates before,
    /// between, on, and after the flows, so a same-date or cursor off-by-one would
    /// trip it.
    #[test]
    fn investment_values_at_matches_per_date() {
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            // Two transactions on the SAME date: both must be applied before the
            // 2020-06-01 snapshot.
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1200), "USD")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(2), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-240), "USD")),
                ],
            ),
            // Partial sale.
            txn(
                d(2020, 9, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(-5), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(650), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 3, 1), dec!(110))
            .with("AAPL", "USD", d(2020, 6, 1), dec!(120))
            .with("AAPL", "USD", d(2020, 9, 1), dec!(130))
            .with("AAPL", "USD", d(2020, 12, 31), dec!(140));
        let scope = invest_scope();
        // Dates before / between / on / after the transactions (ascending).
        let dates = [
            d(2020, 1, 1),
            d(2020, 3, 1),
            d(2020, 6, 1),
            d(2020, 9, 1),
            d(2020, 12, 31),
        ];

        let batch: Vec<Decimal> = investment_values_at(&dirs, &scope, "USD", &prices, &dates)
            .into_iter()
            .map(Result::unwrap)
            .collect();
        let per_date: Vec<Decimal> = dates
            .iter()
            .map(|&date| investment_value_at(&dirs, &scope, "USD", &prices, date).unwrap())
            .collect();
        assert_eq!(
            batch, per_date,
            "single-pass diverged from per-date realization"
        );
        // Not vacuous: the values actually move across the dates.
        assert_eq!(batch[0], dec!(1000)); // 10 @ 100
        assert_eq!(batch[2], dec!(2640)); // (10+10+2) @ 120
        assert_eq!(batch[4], dec!(2380)); // 17 @ 140 after the -5 sale
    }

    /// The single-pass cursor is only valid for date-sorted directives; on an
    /// unsorted (but still booked) stream `investment_values_at` must fall back to
    /// the order-independent per-date realization, so it still matches
    /// `investment_value_at`. Without the fallback the cursor would break at the
    /// first out-of-order transaction and under-value early dates — this fixture
    /// puts a June buy *before* a January buy, so a naive cursor would report 0 at
    /// January instead of 1000.
    #[test]
    fn investment_values_at_matches_per_date_when_unsorted() {
        let dirs = vec![
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(5), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-600), "USD")),
                ],
            ),
            // Dated BEFORE the transaction above, but appears after it in the stream.
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 6, 1), dec!(120))
            .with("AAPL", "USD", d(2020, 12, 31), dec!(130));
        let scope = invest_scope();
        let dates = [d(2020, 1, 1), d(2020, 6, 1), d(2020, 12, 31)];

        let batch: Vec<Decimal> = investment_values_at(&dirs, &scope, "USD", &prices, &dates)
            .into_iter()
            .map(Result::unwrap)
            .collect();
        let per_date: Vec<Decimal> = dates
            .iter()
            .map(|&date| investment_value_at(&dirs, &scope, "USD", &prices, date).unwrap())
            .collect();
        assert_eq!(
            batch, per_date,
            "unsorted stream must fall back to the per-date realization"
        );
        // The value at January is the January buy only — a broken cursor would
        // have reported 0 here.
        assert_eq!(batch[0], dec!(1000)); // 10 @ 100
    }

    /// Assert `compute_returns` equals the by-hand composition it replaced
    /// (`extract_flows` + `terminal_value` + `xirr` + `twr`, with the zero-capital
    /// TWR guard) AND that its money-weighted series matches the canonical
    /// `extract_cash_flows`. Returns the computed `Returns` so callers can pin the
    /// concrete figures for their shape.
    fn assert_compute_returns_matches_composition(
        dirs: &[Directive],
        prices: &MockPrices,
        scope: &Scope,
        end: NaiveDate,
    ) -> Returns {
        let flows = extract_flows(dirs, scope, "USD", prices, end).unwrap();
        let terminal = terminal_value(dirs, scope, "USD", prices, end).unwrap();
        let invested: Decimal = flows
            .iter()
            .filter(|f| f.amount.is_sign_negative())
            .map(|f| -f.amount)
            .sum();
        let distributions: Decimal = flows
            .iter()
            .filter(|f| f.amount.is_sign_positive())
            .map(|f| f.amount)
            .sum();
        let current_value = terminal.map_or(Decimal::ZERO, |t| t.amount);
        let mut series = flows;
        if let Some(t) = terminal {
            series.push(t);
        }
        series.sort_by_key(|f| f.date);
        let mwr = crate::xirr(&series);
        let twr_rate = if invested.is_zero() && current_value.is_zero() {
            None
        } else {
            twr(dirs, scope, "USD", prices, end).unwrap_or(None)
        };

        let r = compute_returns(dirs, scope, "USD", prices, end).unwrap();
        assert_eq!(r.cash_flows, series.len(), "cash_flows");
        assert_eq!(r.invested, invested, "invested");
        assert_eq!(r.distributions, distributions, "distributions");
        assert_eq!(r.current_value, current_value, "current_value");
        assert_eq!(r.money_weighted, mwr, "money_weighted");
        assert_eq!(r.time_weighted, twr_rate, "time_weighted");
        // Canonical-series guard: the MWR series `compute_returns` open-codes must
        // match `extract_cash_flows` (the canonical flows+terminal+sort assembler).
        let canonical = extract_cash_flows(dirs, scope, "USD", prices, end).unwrap();
        assert_eq!(
            r.money_weighted,
            crate::xirr(&canonical),
            "MWR diverged from the canonical extract_cash_flows series"
        );
        r
    }

    /// Drift guard (CLAUDE.md Canonical-Function Discipline): `compute_returns`
    /// must equal the by-hand composition it replaced, across the shapes that hit
    /// its distinct branches — the happy path is not enough (a broken zero-terminal
    /// suppression or a narrowed zero-capital guard hides in the all-nonzero case).
    #[test]
    fn compute_returns_matches_manual_composition() {
        let scope = invest_scope();
        let end = d(2020, 12, 31);

        // (a) Happy path: buy + dividend-inclusive holding — every field non-trivial.
        let happy = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Bank", amt(dec!(20), "USD")),
                    Posting::new("Income:Dividends", amt(dec!(-20), "USD")),
                ],
            ),
        ];
        let happy_prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 6, 1), dec!(110))
            .with("AAPL", "USD", d(2020, 12, 31), dec!(130));
        let r = assert_compute_returns_matches_composition(&happy, &happy_prices, &scope, end);
        assert_eq!(r.invested, dec!(1000));
        assert_eq!(r.distributions, dec!(20));
        assert_eq!(r.current_value, dec!(1300));
        assert!(r.money_weighted.is_some() && r.time_weighted.is_some());

        // (b) Income-only: a dividend, no holding — exercises the zero-capital TWR
        // guard (twr() alone would fabricate 0%) and the zero-terminal suppression.
        let income_only = vec![txn(
            d(2020, 6, 1),
            vec![
                Posting::new("Assets:Bank", amt(dec!(20), "USD")),
                Posting::new("Income:Dividends", amt(dec!(-20), "USD")),
            ],
        )];
        let r = assert_compute_returns_matches_composition(
            &income_only,
            &MockPrices::default(),
            &scope,
            end,
        );
        assert_eq!(r.invested, dec!(0));
        assert_eq!(r.distributions, dec!(20));
        assert_eq!(r.current_value, dec!(0));
        assert_eq!(
            r.time_weighted, None,
            "zero-capital TWR must be None, not 0%"
        );

        // (c) Worthless terminal: a holding priced to zero at the end — exercises
        // the zero-terminal suppression (no terminal flow, current_value 0).
        let worthless = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        let worthless_prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 12, 31), dec!(0));
        let r =
            assert_compute_returns_matches_composition(&worthless, &worthless_prices, &scope, end);
        assert_eq!(r.invested, dec!(1000));
        assert_eq!(
            r.current_value,
            dec!(0),
            "a worthless holding suppresses the terminal"
        );
    }

    /// `compute_returns` errors eagerly on a missing `end_date` price, exactly as
    /// the old `terminal_value(..)?` did — a report can't state a summary it can't
    /// value at the horizon.
    #[test]
    fn compute_returns_errors_on_missing_end_price_like_terminal_value() {
        let dirs = vec![txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        )];
        // Priced at the buy (so extract_flows/the flow-date valuation succeed) but
        // NOT at the report end date.
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 1, 1), dec!(100));
        let scope = invest_scope();
        let end = d(2020, 12, 31);
        assert!(terminal_value(&dirs, &scope, "USD", &prices, end).is_err());
        assert!(
            compute_returns(&dirs, &scope, "USD", &prices, end).is_err(),
            "a missing end-date price must error, matching terminal_value"
        );
    }

    /// Drift guard: the shared-realization `investment_values_multi` must return,
    /// per scope, exactly what per-scope `investment_values_at` returns — the
    /// booking is shared, but each scope's values are unchanged. Two scopes with
    /// overlapping but different date sets.
    #[test]
    fn investment_values_multi_matches_per_scope() {
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:AAPL", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Broker:MSFT", amt(dec!(10), "MSFT")),
                    Posting::new("Assets:Bank", amt(dec!(-500), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 6, 1), dec!(110))
            .with("AAPL", "USD", d(2020, 12, 31), dec!(130))
            .with("MSFT", "USD", d(2020, 6, 1), dec!(50))
            .with("MSFT", "USD", d(2020, 12, 31), dec!(55));
        let s1 = Scope::new(vec!["Assets:Broker:AAPL".to_string()], vec![]);
        let s2 = Scope::new(vec!["Assets:Broker:MSFT".to_string()], vec![]);
        let dates1 = [d(2020, 1, 1), d(2020, 6, 1), d(2020, 12, 31)];
        let dates2 = [d(2020, 6, 1), d(2020, 12, 31)];

        let multi =
            investment_values_multi(&dirs, &[(&s1, &dates1), (&s2, &dates2)], "USD", &prices);
        let unwrap = |v: &[Result<Decimal, ExtractError>]| {
            v.iter().map(|r| r.clone().unwrap()).collect::<Vec<_>>()
        };
        assert_eq!(
            unwrap(&multi[0]),
            unwrap(&investment_values_at(&dirs, &s1, "USD", &prices, &dates1))
        );
        assert_eq!(
            unwrap(&multi[1]),
            unwrap(&investment_values_at(&dirs, &s2, "USD", &prices, &dates2))
        );
        // Not vacuous: AAPL 1000→1100→1300, MSFT 500→550.
        assert_eq!(unwrap(&multi[0]), vec![dec!(1000), dec!(1100), dec!(1300)]);
        assert_eq!(unwrap(&multi[1]), vec![dec!(500), dec!(550)]);
    }

    /// Drift guard (CLAUDE.md Canonical-Function Discipline): `compute_returns_multi`
    /// shares one realization, but each scope's result MUST equal calling
    /// `compute_returns` for that scope alone. Covers a happy single-holding scope,
    /// a scope whose EUR flow can't be priced (an independent error, skipped from
    /// the shared pass), and an income-only scope — so the error-skip alignment and
    /// the zero-capital branch are exercised, not just the happy path.
    #[test]
    fn compute_returns_multi_matches_per_scope() {
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:BrokerUS:AAPL", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            // The external EUR leg has no EUR->USD price, so extract_flows errors
            // for a scope that includes this holding.
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:BrokerEU:BND", amt(dec!(10), "BND")),
                    Posting::new("Assets:BankEUR", amt(dec!(-500), "EUR")),
                ],
            ),
            txn(
                d(2020, 6, 1),
                vec![
                    Posting::new("Assets:Bank", amt(dec!(20), "USD")),
                    Posting::new("Income:Dividends", amt(dec!(-20), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default()
            .with("AAPL", "USD", d(2020, 1, 1), dec!(100))
            .with("AAPL", "USD", d(2020, 12, 31), dec!(130)); // no EUR / BND prices
        let end = d(2020, 12, 31);
        let scopes = vec![
            Scope::new(vec!["Assets:BrokerUS".to_string()], vec![]), // ok: single holding
            Scope::new(vec!["Assets:BrokerEU".to_string()], vec![]), // err: EUR flow unpriceable
            Scope::new(vec![], vec!["Income:Dividends".to_string()]), // ok: income-only
        ];

        let multi = compute_returns_multi(&dirs, &scopes, "USD", &prices, end);
        assert_eq!(multi.len(), scopes.len());
        for (i, scope) in scopes.iter().enumerate() {
            let single = compute_returns(&dirs, scope, "USD", &prices, end);
            assert_eq!(multi[i], single, "scope {i} diverged from compute_returns");
        }
        // Not vacuous: the middle scope errors, the others succeed with real values.
        assert_eq!(multi[0].as_ref().unwrap().current_value, dec!(1300));
        assert!(
            multi[1].is_err(),
            "the EUR scope must error on the unpriceable flow"
        );
        assert_eq!(
            multi[2].as_ref().unwrap().time_weighted,
            None,
            "income-only scope has no capital → TWR None"
        );
    }

    /// The riskiest paths in the shared pass, still equal to per-scope: a scope
    /// with a flow ON `end_date` (so its `dates` list carries `end_date` twice and
    /// the union collapses it — the cursor must emit BOTH values), and a scope with
    /// no activity at all (empty flows → `dates` is just `[end_date]`).
    #[test]
    fn compute_returns_multi_matches_per_scope_edge_cases() {
        let dirs = vec![
            txn(
                d(2020, 1, 1),
                vec![
                    Posting::new("Assets:Broker:AAPL", amt(dec!(10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
                ],
            ),
            // Sale ON the report end date → a flow whose date == end_date, so the
            // scope's `dates` = [2020-01-01, 2020-12-31, 2020-12-31].
            txn(
                d(2020, 12, 31),
                vec![
                    Posting::new("Assets:Broker:AAPL", amt(dec!(-10), "AAPL")),
                    Posting::new("Assets:Bank", amt(dec!(1300), "USD")),
                ],
            ),
        ];
        let prices = MockPrices::default().with("AAPL", "USD", d(2020, 1, 1), dec!(100));
        let end = d(2020, 12, 31);
        let scopes = vec![
            Scope::new(vec!["Assets:Broker:AAPL".to_string()], vec![]), // flow on end_date
            Scope::new(vec!["Assets:Broker:NONE".to_string()], vec![]), // no activity: empty flows
        ];

        let multi = compute_returns_multi(&dirs, &scopes, "USD", &prices, end);
        for (i, scope) in scopes.iter().enumerate() {
            assert_eq!(
                multi[i],
                compute_returns(&dirs, scope, "USD", &prices, end),
                "scope {i} diverged from compute_returns"
            );
        }
        // Not vacuous: the AAPL scope closed out (invested 1000, current 0, defined
        // TWR), and the empty scope is all-none.
        let aapl = multi[0].as_ref().unwrap();
        assert_eq!(aapl.invested, dec!(1000));
        assert_eq!(aapl.current_value, dec!(0));
        assert!(aapl.time_weighted.is_some());
        let empty = multi[1].as_ref().unwrap();
        assert_eq!(empty.cash_flows, 0);
        assert_eq!(empty.money_weighted, None);
        assert_eq!(empty.time_weighted, None);
    }
}
