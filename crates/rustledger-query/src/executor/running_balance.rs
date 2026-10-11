//! The running `balance` column of `SELECT` and `JOURNAL`.

use std::collections::BTreeMap;

use rustledger_booking::BookingEngine;
use rustledger_core::{
    Account, BookingMethod, Inventory, NaiveDate, Position, Posting, Spanned, Transaction,
};

use crate::error::QueryError;

/// The positions of the rows so far, as one inventory: the running `balance`
/// column, bean-query's "everything selected so far".
///
/// A plain sum of positions, except that an AVERAGE account is presented as
/// its pool, as `BALANCES` and `sum(position)` present it (#2543). Summed
/// plainly, a sale from an AVERAGE account is a negative lot at the pool's
/// cost, which matches none of the lots bought, so after a sale the column
/// listed both lots bought plus the sale as a negative lot: `2 X {200 USD}
/// 1 X {100 USD} -1 X {167 USD}` for an account holding `2 X {167 USD}`.
///
/// So each AVERAGE account's rows are realized as `sum(position)` realizes a
/// group of them (`realize_average_group`): each transaction's rows on the
/// account, as one transaction, replayed through an AVERAGE engine in
/// booking's order, then presented by `rustledger_booking::present_inventory`.
/// A row partway through a transaction shows that transaction's rows so far,
/// tried on a copy of the engine; the transaction is committed when the
/// caller ends it ([`Self::end_transaction`]). Replaying row by row instead
/// read a short and a long bought in one transaction as a short and its
/// cover.
///
/// The rows of an account that booking cannot realize (a WHERE keeping a sale
/// but not what it sold from) keep the plain sum, unmerged, as `sum(position)`
/// does. A longer run of rows cannot be realized either, so the account stays
/// on the plain sum.
///
/// Every other account's positions are summed as before, in one shared
/// inventory cloned per row (#1086). An AVERAGE account's view is rebuilt only
/// when one of its own rows arrives, so a row costs a clone of the plain sum
/// plus each AVERAGE account's (pooled, so small) view.
#[derive(Debug)]
pub(super) struct RunningBalance {
    /// Positions of the rows on accounts not booked AVERAGE.
    plain: Inventory,
    /// Each AVERAGE account with a row so far. Ordered, so a row's positions
    /// come out in one order every run.
    average: BTreeMap<Account, AverageAccount>,
}

/// One AVERAGE account's rows.
#[derive(Debug)]
struct AverageAccount {
    /// The account's rows of the transactions already ended, realized.
    committed: BookingEngine,
    /// The current transaction's rows on the account so far.
    pending: Vec<Spanned<Posting>>,
    /// `committed` with `pending` replayed: committed when the transaction
    /// ends.
    tried: Option<BookingEngine>,
    /// The plain sum of the rows: the view once they cannot be realized.
    plain: Inventory,
    /// Booking could not realize the rows.
    unrealized: bool,
    /// What the account shows, rebuilt when one of its rows arrives.
    view: Inventory,
}

impl RunningBalance {
    /// An empty running balance.
    pub(super) fn new() -> Self {
        Self {
            plain: Inventory::new_shared(),
            average: BTreeMap::new(),
        }
    }

    /// Add a row: `posting`, whose position is `position`, in a transaction
    /// dated `date`. `is_average` says whether its account books AVERAGE.
    /// Every row of one transaction comes before that transaction's
    /// [`Self::end_transaction`].
    pub(super) fn add(
        &mut self,
        posting: &Spanned<Posting>,
        date: NaiveDate,
        position: Position,
        is_average: bool,
    ) -> Result<(), QueryError> {
        let eval = |e: rustledger_core::OverflowError| QueryError::Evaluation(e.to_string());
        if !is_average {
            return self.plain.add(position).map_err(eval);
        }
        let account = &posting.account;
        let acc = self
            .average
            .entry(account.clone())
            .or_insert_with(|| AverageAccount {
                committed: BookingEngine::with_method(BookingMethod::Average),
                pending: Vec::new(),
                tried: None,
                plain: Inventory::new(),
                unrealized: false,
                view: Inventory::new(),
            });
        acc.plain.add(position).map_err(eval)?;
        if !acc.unrealized {
            acc.pending.push(posting.clone());
            let mut rows = Transaction::new(date, "");
            rows.postings.clone_from(&acc.pending);
            let mut tried = acc.committed.clone();
            if tried.replay_transaction(&rows).is_ok() {
                let mut realized = tried.inventory(account).cloned().unwrap_or_default();
                rustledger_booking::present_inventory(BookingMethod::Average, &mut realized)
                    .map_err(eval)?;
                acc.view = realized;
                acc.tried = Some(tried);
            } else {
                acc.unrealized = true;
                acc.pending.clear();
                acc.tried = None;
            }
        }
        if acc.unrealized {
            acc.view = acc.plain.clone();
        }
        Ok(())
    }

    /// End the current transaction: its rows on each AVERAGE account are
    /// committed, as one transaction.
    pub(super) fn end_transaction(&mut self) {
        for acc in self.average.values_mut() {
            if let Some(tried) = acc.tried.take() {
                acc.committed = tried;
            }
            acc.pending.clear();
        }
    }

    /// The balance as of the rows added so far.
    pub(super) fn snapshot(&self) -> Result<Inventory, QueryError> {
        let mut out = self.plain.clone();
        for acc in self.average.values() {
            out.merge(&acc.view)
                .map_err(|e| QueryError::Evaluation(e.to_string()))?;
        }
        Ok(out)
    }
}
