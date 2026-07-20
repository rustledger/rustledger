//! Cash-flow extraction: turn a booked ledger into the [`CashFlow`] series that
//! [`xirr`](crate::xirr) consumes.
//!
//! This is the correctness core of returns reporting. Given a booked directive
//! stream and a [`Scope`] that classifies accounts, it produces the dated,
//! single-currency cash-flow series an investor's money-weighted return is
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
//! Both entry points take the **booked, pad-expanded** directive stream — costs
//! resolved, amounts interpolated, and `pad`/`balance` directives already
//! expanded into their synthesized transactions (the loader's
//! `Ledger::balance_view` output, the same stream the canonical
//! `report_cmd::account_balances` consumes). This crate is a leaf and cannot
//! book or pad-expand a raw stream itself; handing it un-booked directives lets
//! the booking engine silently realize the wrong inventory (unmatched reductions and
//! elided-units postings are dropped), and handing it un-expanded directives
//! drops any position seeded by a pad.
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
use rustledger_core::{Amount, Directive, NaiveDate, is_subaccount_or_equal};

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
/// `directives` must be the **booked, pad-expanded** stream — costs resolved,
/// amounts interpolated, and `pad`/`balance` directives already expanded into
/// their synthesized transactions (the loader's `Ledger::balance_view` output,
/// the same stream `report_cmd::account_balances` consumes). This crate is a
/// leaf and cannot book or pad-expand a raw stream: an un-booked stream lets the
/// booking engine silently realize the wrong inventory, and an un-expanded stream
/// drops pad-seeded positions.
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
/// cannot be converted to `reporting_currency` on the date it is needed.
///
/// # Panics
///
/// See [`terminal_value`]: a stream that violates the booked input contract can
/// make the booking engine `debug_assert` (debug builds) instead of returning
/// `Err`.
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
/// nothing. Flows dated after `end_date` are excluded. Expects the booked,
/// pad-expanded stream described in the module-level docs.
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
/// transaction cannot be converted to `reporting_currency` on its date.
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
            // The input-contract booked stream (module docs) fills units on every
            // posting, so a None here is unreachable in practice; skipping is
            // defensive, not a silent drop of a real flow (an un-booked stream is
            // a contract violation the leaf crate cannot detect, exactly as
            // `apply`/`account_balances` also require pre-booked input).
            let Some(amount) = posting.amount() else {
                continue;
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
/// Holdings are realized through the booking engine — lots keep their cost and
/// reductions match the account's booking method — over every transaction dated
/// on or before `end_date`, then each position's units are valued at **market**
/// (`position.units`, not cost basis) via `prices`. Because market value is
/// `units × price` and every lot of a commodity shares one market price, the
/// terminal value depends only on total held units, not on which lots a
/// reduction matched; the booking method affects realized-gain reporting (a
/// later concern), not this figure. Only accounts the `scope` classifies as
/// [`Investment`](AccountRole::Investment) are counted. Positions seeded by a
/// `pad` are realized only if the input stream is pad-expanded, as
/// [`extract_cash_flows`]' input contract requires.
///
/// A net-short position (negative units) values negatively, correctly reducing
/// the terminal flow (see the [`PriceOracle`] linearity requirement). A position
/// whose currency is already the reporting currency (uninvested broker cash)
/// needs no price.
///
/// # Errors
///
/// Returns [`ExtractError::MissingPrice`] if a held commodity has no price in
/// `reporting_currency` on `end_date`.
///
/// # Panics
///
/// Requires the booked input stream of [`extract_cash_flows`]' contract. On a
/// contract-violating (un-booked) stream, the booking engine may `debug_assert`
/// in debug builds when a reduction has no matching lot; the leaf crate cannot
/// detect this, so an un-booked stream can abort rather than return `Err`.
pub fn terminal_value(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
) -> Result<Option<CashFlow>, ExtractError> {
    // Realize per-account inventories via the booking engine, applying only
    // transactions up to the valuation date. Opens carry booking methods
    // regardless of date, so the engine is registered with the full stream.
    //
    // This realization loop mirrors `report_cmd::account_balances`
    // (crates/rustledger/src/cmd/report_cmd/mod.rs) plus the `<= end_date`
    // filter — the leaf crate cannot call that CLI-side helper. Kept aligned by
    // hand until a shared realization primitive lands; the returns CLI PR is
    // the place to add a cross-crate drift-guard test comparing the two on the
    // same ledger. Like that helper, inventories are collected into a `BTreeMap`
    // so iteration order is account-sorted and stable across runs (an
    // `FxHashMap` would make which currency a `MissingPrice` names depend on
    // hash order — and differ between 32- and 64-bit targets).
    let mut engine = rustledger_booking::BookingEngine::new();
    engine.register_account_methods(directives.iter());
    for directive in directives {
        if let Directive::Transaction(txn) = directive
            && txn.date <= end_date
        {
            engine.apply(txn);
        }
    }
    let inventories: std::collections::BTreeMap<_, _> =
        engine.into_inventories().into_iter().collect();

    let mut total = Decimal::ZERO;
    for (account, inventory) in &inventories {
        if scope.classify(account.as_str()) != AccountRole::Investment {
            continue;
        }
        for position in inventory.positions() {
            if position.units.number.is_zero() {
                continue;
            }
            let converted = prices
                .convert(&position.units, reporting_currency, end_date)
                .ok_or_else(|| ExtractError::MissingPrice {
                    currency: position.units.currency.to_string(),
                    date: end_date,
                })?;
            total += converted.number;
        }
    }

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
}
