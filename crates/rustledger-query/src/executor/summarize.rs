//! `FROM ... OPEN ON`: summarize the ledger before a date, as beanquery does.
//!
//! beanquery applies `OPEN ON` with beancount's `summarize.open`: every
//! transaction before the date is replaced by one opening-balance transaction
//! per account, dated the day before, so the period's rows start from the
//! balances the ledger held and the running `balance` carries them in (#2401).
//! rledger used to drop the earlier transactions and start every balance at
//! zero.
//!
//! `summarize.open` does three things, all reproduced here:
//!
//! 1. **Conversions.** When the balances before the date do not sum to zero at
//!    cost (a price conversion `@` moves value between currencies), a
//!    conversion entry books the residual to `account_previous_conversions`.
//! 2. **Clear.** Income and expense balances are transferred, at cost, to
//!    `account_previous_earnings`, so the period's income statement starts
//!    from zero.
//! 3. **Summarize.** Each account left with a balance gets one transaction,
//!    flagged `S` and narrated `Opening balance for '<account>'
//!    (Summarization)`: a posting per position, at its cost, balanced by the
//!    position's cost against `account_previous_balances`.
//!
//! The conversion and transfer entries are themselves dated before the open
//! date, so beancount summarizes them away too. Only the summaries survive,
//! and they are all this module emits.
//!
//! The rest of the family, applied after `OPEN ON` in beanquery's order
//! (#2406):
//!
//! - **`CLOSE [ON <date>]`** is beancount's `summarize.close`: truncate at the
//!   date (the window already does), then book a conversions entry, flagged
//!   `C`, that brings the period's total at cost to zero against
//!   `account_current_conversions`. A bare `CLOSE` truncates nothing.
//! - **`CLEAR`** is beancount's `summarize.clear` with no date: transfer every
//!   income-statement balance to `account_current_earnings`, flagged `T`,
//!   dated the last entry's date.
//!
//! One deliberate difference: beancount totals each account with plain
//! inventory addition, and rledger realizes it through the booking engine,
//! as `BALANCES` and `report balances` do. The two agree for every method
//! beancount has. For AVERAGE, which beancount lacks, plain addition leaves
//! a reduction booked at the pooled cost as a dangling lot (#1985), and the
//! engine gives the holding the account actually has.

use std::collections::BTreeMap;
use std::sync::Arc;

use rustledger_core::{
    Amount, CostNumber, CostSpec, Directive, Inventory, NaiveDate, Position, Posting, Transaction,
};

use super::Executor;
use crate::error::QueryError;

/// The equity accounts `FROM ... OPEN ON` summarizes into: beancount's
/// `account_previous_balances`, `account_previous_earnings` and
/// `account_previous_conversions` options.
///
/// [`Default`] is beancount's defaults. A host with a loaded ledger should
/// pass the ledger's own names through [`SummaryAccounts::from_options`] and
/// [`Executor::set_summary_accounts`], or a ledger that renames them gets
/// summaries booked to accounts it does not have.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SummaryAccounts {
    /// Contra account of every opening balance (`account_previous_balances`).
    pub previous_balances: String,
    /// Where income and expenses before the period go
    /// (`account_previous_earnings`).
    pub previous_earnings: String,
    /// Where a conversion residual before the period goes
    /// (`account_previous_conversions`).
    pub previous_conversions: String,
    /// Where `CLEAR` moves the period's income and expenses
    /// (`account_current_earnings`).
    pub current_earnings: String,
    /// Where `CLOSE` books the period's conversion residual
    /// (`account_current_conversions`).
    pub current_conversions: String,
    /// The currency a conversions entry prices its postings in
    /// (`conversion_currency`, `NOTHING` by default).
    pub conversion_currency: String,
}

impl Default for SummaryAccounts {
    fn default() -> Self {
        Self::from_options(&rustledger_loader::Options::default())
    }
}

impl SummaryAccounts {
    /// The summary accounts a loaded ledger's options name.
    #[must_use]
    pub fn from_options(options: &rustledger_loader::Options) -> Self {
        Self {
            previous_balances: options.previous_balances_account(),
            previous_earnings: options.previous_earnings_account(),
            previous_conversions: options.previous_conversions_account(),
            current_earnings: options.current_earnings_account(),
            current_conversions: options.current_conversions_account(),
            conversion_currency: options.conversion_currency_or_default(),
        }
    }
}

/// A position's cost amount: units times per-unit cost, or the units
/// themselves when the position is held without cost. beancount's
/// `convert.get_cost`.
fn cost_amount(position: &Position) -> Result<Amount, QueryError> {
    let Some(cost) = position.cost.as_ref() else {
        return Ok(position.units.clone());
    };
    let number = position
        .units
        .number
        .checked_mul(cost.number)
        .ok_or_else(|| {
            QueryError::Evaluation(format!(
                "OPEN ON: the cost of {} overflows",
                position.units.currency
            ))
        })?;
    Ok(Amount::new(number, cost.currency.clone()))
}

/// Add `amount` to a cost-less inventory, as a position held without cost.
fn add_amount(inventory: &mut Inventory, amount: Amount) -> Result<(), QueryError> {
    inventory
        .add(Position::simple(amount))
        .map_err(|e| QueryError::Evaluation(format!("OPEN ON: {e}")))
}

/// A running balance with Python beancount's `Inventory` ordering: positions
/// keyed by `(currency, cost)` in the order they first appear, a key DROPPED
/// when its units reach zero and appended again if it comes back.
///
/// beancount's conversions entry lists its postings, and names its balance,
/// in exactly this order, so bean-query's `C` rows come out in it (on the
/// #2406 conversions ledger, the USD posting before the EUR one, although EUR
/// appeared first: its balance crossed zero on the way).
#[derive(Default)]
struct OrderedBalance {
    positions: Vec<Position>,
}

impl OrderedBalance {
    fn add(&mut self, position: &Position) -> Result<(), QueryError> {
        let slot = self.positions.iter().position(|held| {
            held.units.currency == position.units.currency && held.cost == position.cost
        });
        match slot {
            Some(i) => {
                let held = &mut self.positions[i];
                held.units.number = rustledger_core::checked_add_python_scale(
                    held.units.number,
                    position.units.number,
                )
                .ok_or_else(|| {
                    QueryError::Evaluation(format!(
                        "CLOSE: the balance of {} overflows",
                        position.units.currency
                    ))
                })?;
                if held.units.number.is_zero() {
                    self.positions.remove(i);
                }
            }
            None if position.units.number.is_zero() => {}
            None => self.positions.push(position.clone()),
        }
        Ok(())
    }

    /// Python's `str(Inventory)`: `(55.00 USD, 10 AAPL {150.00 USD,
    /// 2024-01-03})`, SORTED by beancount's `Position.sortkey`, not in the
    /// balance's own order. The key is a currency rank (USD, EUR, JPY, CAD,
    /// GBP, AUD, NZD, CHF first; any other currency `8 + len(code)`), then the
    /// cost number, the cost currency and the units. The sort is stable, as
    /// Python's is. So bean-query names `(-55.00 USD, 50.00 EUR)` while
    /// listing the EUR posting first.
    fn render(&self) -> String {
        const CURRENCY_ORDER: [&str; 8] = ["USD", "EUR", "JPY", "CAD", "GBP", "AUD", "NZD", "CHF"];
        let rank = |currency: &str| {
            CURRENCY_ORDER
                .iter()
                .position(|c| *c == currency)
                .unwrap_or(CURRENCY_ORDER.len() + currency.len())
        };
        let mut sorted: Vec<&Position> = self.positions.iter().collect();
        sorted.sort_by(|a, b| {
            let key = |p: &Position| {
                (
                    rank(p.units.currency.as_str()),
                    p.cost
                        .as_ref()
                        .map_or(rustledger_core::Decimal::ZERO, |c| c.number),
                    p.cost
                        .as_ref()
                        .map_or_else(String::new, |c| c.currency.to_string()),
                    p.units.number,
                )
            };
            key(a).cmp(&key(b))
        });
        let positions: Vec<String> = sorted
            .into_iter()
            .map(|p| match &p.cost {
                None => p.units.to_string(),
                Some(cost) => {
                    let mut parts = vec![format!("{} {}", cost.number, cost.currency)];
                    if let Some(date) = cost.date {
                        parts.push(date.to_string());
                    }
                    if let Some(label) = &cost.label {
                        parts.push(format!("\"{label}\""));
                    }
                    format!("{} {{{}}}", p.units, parts.join(", "))
                }
            })
            .collect();
        format!("({})", positions.join(", "))
    }
}

/// The cost spec of a held position: its per-unit cost, date and label, so a
/// summary posting names the same lot the account holds.
fn position_cost_spec(position: &Position) -> Option<CostSpec> {
    position.cost.as_ref().map(|cost| CostSpec {
        number: Some(CostNumber::PerUnit { value: cost.number }),
        currency: Some(cost.currency.clone()),
        date: cost.date,
        label: cost.label.clone(),
        merge: false,
    })
}

impl Executor<'_> {
    /// The opening-balance transactions `FROM ... OPEN ON open` starts from:
    /// one per account holding a balance before `open`, in account order,
    /// dated the day before. See the module docs for what is summarized.
    ///
    /// # Errors
    ///
    /// When a transaction before `open` cannot be realized, or a balance's
    /// cost leaves the `Decimal` range.
    pub(super) fn open_summaries(
        &self,
        open: NaiveDate,
    ) -> Result<Vec<Arc<Transaction>>, QueryError> {
        // Realize everything before the date, through the same engine and
        // default booking method as the rest of the scan.
        let mut engine = rustledger_booking::BookingEngine::for_ledger(
            self.booking_method,
            self.resolved_directives(),
        );
        for directive in self.resolved_directives() {
            if let Directive::Transaction(txn) = directive
                && txn.date < open
            {
                engine
                    .replay_transaction(txn)
                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
            }
        }
        let mut balances: BTreeMap<String, Inventory> = engine
            .inventories()
            .map(|(account, inventory)| (account.to_string(), inventory.clone()))
            .collect();

        // 1. Conversions: the balances' total at cost, booked negated to the
        //    conversions account when it is not zero.
        let mut at_cost = Inventory::new();
        for inventory in balances.values() {
            for position in inventory.positions() {
                add_amount(&mut at_cost, cost_amount(position)?)?;
            }
        }
        let residual: Vec<Amount> = at_cost
            .positions()
            .filter(|p| !p.units.number.is_zero())
            .map(|p| Amount::new(-p.units.number, p.units.currency.clone()))
            .collect();
        if !residual.is_empty() {
            let conversions = balances
                .entry(self.summary_accounts.previous_conversions.clone())
                .or_default();
            for amount in residual {
                add_amount(conversions, amount)?;
            }
        }

        // 2. Clear: income and expenses move to earnings, at cost.
        let income_statement: Vec<String> = balances
            .keys()
            .filter(|account| self.account_types.is_income_statement(account))
            .cloned()
            .collect();
        let mut earnings = Vec::new();
        for account in income_statement {
            if let Some(inventory) = balances.remove(&account) {
                for position in inventory.positions() {
                    earnings.push(cost_amount(position)?);
                }
            }
        }
        if !earnings.is_empty() {
            let target = balances
                .entry(self.summary_accounts.previous_earnings.clone())
                .or_default();
            for amount in earnings {
                add_amount(target, amount)?;
            }
        }

        // 3. Summarize: one transaction per account with a balance.
        let date = open
            .yesterday()
            .map_err(|e| QueryError::Evaluation(format!("OPEN ON {open}: {e}")))?;
        let mut summaries = Vec::new();
        for (account, inventory) in &balances {
            let mut txn = Transaction::new(
                date,
                format!("Opening balance for '{account}' (Summarization)"),
            )
            .with_flag('S');
            for position in inventory.positions() {
                if position.units.number.is_zero() {
                    continue;
                }
                let mut held = Posting::new(account.as_str(), position.units.clone());
                if let Some(spec) = position_cost_spec(position) {
                    held = held.with_cost(spec);
                }
                let cost = cost_amount(position)?;
                txn = txn
                    .with_synthesized_posting(held)
                    .with_synthesized_posting(Posting::new(
                        self.summary_accounts.previous_balances.as_str(),
                        Amount::new(-cost.number, cost.currency),
                    ));
            }
            if !txn.postings.is_empty() {
                summaries.push(Arc::new(txn));
            }
        }
        Ok(summaries)
    }
}

impl Executor<'_> {
    /// `CLOSE`'s conversions entry: dated `date`, the period's balance at
    /// cost negated into `account_current_conversions`, each posting priced
    /// at zero in `conversion_currency` as beancount prices it (the one
    /// place its balance rule is bent; see beancount's `conversions`).
    /// `None` when the balance at cost is already zero.
    ///
    /// # Errors
    ///
    /// A balance or cost that leaves the `Decimal` range.
    pub(super) fn close_conversions(
        &self,
        stream: &[(Option<usize>, super::TransactionRef<'_>)],
        date: NaiveDate,
    ) -> Result<Option<Arc<Transaction>>, QueryError> {
        let mut balance = OrderedBalance::default();
        for (_, txn) in stream {
            for posting in &txn.postings {
                if let Some(units) = posting.amount() {
                    balance.add(&Position::from_posting(
                        units,
                        posting.cost.as_deref(),
                        txn.date,
                    ))?;
                }
            }
        }
        let mut at_cost = OrderedBalance::default();
        for position in &balance.positions {
            at_cost.add(&Position::simple(cost_amount(position)?))?;
        }
        if at_cost.positions.is_empty() {
            return Ok(None);
        }
        let mut txn =
            Transaction::new(date, format!("Conversion for {}", balance.render())).with_flag('C');
        for position in &at_cost.positions {
            txn = txn.with_synthesized_posting(
                Posting::new(
                    self.summary_accounts.current_conversions.as_str(),
                    Amount::new(-position.units.number, position.units.currency.clone()),
                )
                .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                    rustledger_core::Decimal::ZERO,
                    self.summary_accounts.conversion_currency.as_str(),
                ))),
            );
        }
        Ok(Some(Arc::new(txn)))
    }

    /// `CLEAR`'s transfers: one transaction per income-statement account
    /// holding a balance over `stream`, in account order, dated `date`, moving
    /// the balance at cost to `account_current_earnings`. Balances are
    /// realized through the booking engine, as `open_summaries` realizes them.
    ///
    /// # Errors
    ///
    /// A transaction the engine cannot realize, or a cost out of range.
    pub(super) fn clear_transfers(
        &self,
        stream: &[(Option<usize>, super::TransactionRef<'_>)],
        date: NaiveDate,
    ) -> Result<Vec<Arc<Transaction>>, QueryError> {
        let mut engine = rustledger_booking::BookingEngine::for_ledger(
            self.booking_method,
            self.resolved_directives(),
        );
        for (_, txn) in stream {
            engine
                .replay_transaction(txn)
                .map_err(|e| QueryError::Evaluation(e.to_string()))?;
        }
        let balances: BTreeMap<String, Inventory> = engine
            .inventories()
            .filter(|(account, _)| self.account_types.is_income_statement(account))
            .map(|(account, inventory)| (account.to_string(), inventory.clone()))
            .collect();
        let mut transfers = Vec::new();
        for (account, inventory) in &balances {
            let mut txn = Transaction::new(
                date,
                format!("Transfer balance for '{account}' (Transfer balance)"),
            )
            .with_flag('T');
            for position in inventory.positions() {
                if position.units.number.is_zero() {
                    continue;
                }
                let mut moved = Posting::new(
                    account.as_str(),
                    Amount::new(-position.units.number, position.units.currency.clone()),
                );
                if let Some(spec) = position_cost_spec(position) {
                    moved = moved.with_cost(spec);
                }
                let cost = cost_amount(position)?;
                txn = txn
                    .with_synthesized_posting(moved)
                    .with_synthesized_posting(Posting::new(
                        self.summary_accounts.current_earnings.as_str(),
                        cost,
                    ));
            }
            if !txn.postings.is_empty() {
                transfers.push(Arc::new(txn));
            }
        }
        Ok(transfers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    fn amount(n: rustledger_core::Decimal, c: &str) -> Position {
        Position::simple(Amount::new(n, c))
    }

    /// Python drops a key that reaches zero, and never adds one that starts
    /// there: a zero-amount posting leaves no trace in the balance or in the
    /// conversions narration.
    #[test]
    fn a_zero_position_never_enters_the_balance() {
        let mut balance = OrderedBalance::default();
        balance.add(&amount(dec!(0), "USD")).unwrap();
        balance.add(&amount(dec!(5.00), "EUR")).unwrap();
        assert_eq!(balance.render(), "(5.00 EUR)");
        balance.add(&amount(dec!(-5.00), "EUR")).unwrap();
        assert_eq!(balance.render(), "()");
    }

    /// beancount's `Position.sortkey`: the eight ranked currencies first in
    /// their order, then any other by the LENGTH of its code, then units.
    #[test]
    fn the_narration_sorts_as_beancount_sorts_an_inventory() {
        let mut balance = OrderedBalance::default();
        for (n, c) in [
            (dec!(1), "ABCD"),
            (dec!(2), "XYZ"),
            (dec!(3), "EUR"),
            (dec!(4), "CHF"),
            (dec!(5), "USD"),
        ] {
            balance.add(&amount(n, c)).unwrap();
        }
        assert_eq!(balance.render(), "(5 USD, 3 EUR, 4 CHF, 2 XYZ, 1 ABCD)");
    }
}
