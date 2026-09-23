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
//! `CLOSE ON`'s conversions entry and `CLEAR`'s transfer, the rest of the
//! `summarize` family, are not implemented yet (#2406).
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
