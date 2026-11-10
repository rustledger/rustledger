//! Balance and pad validation.

// ratchet: fxhash-only — hot path; use FxHashMap/FxHashSet, not std SipHash collections (#1237).
use rustledger_booking::balance_tolerance;
use rustledger_core::{Account, Amount, Balance, Inventory, OverflowError, Pad, Position};
use std::collections::BTreeSet;

use super::helpers::require_account_open;
use crate::LedgerState;
use crate::error::{ErrorCode, ValidationError};

/// Validate a Pad directive, and apply its padding (the late stream's
/// [`crate::PadState`] plan; `index` is the pad's index in that stream).
pub fn validate_pad(
    state: &mut LedgerState,
    pad: &Pad,
    index: usize,
    location: Option<(rustledger_parser::Span, u16)>,
    errors: &mut Vec<ValidationError>,
) {
    // Check that both accounts exist. Both are checked before either fails
    // the pad, as beancount reports each (`Invalid account name` or `unknown
    // account`): stopping at an unopened target hid an invalid source name
    // (#2809).
    require_account_open(state, &pad.account, pad.date, "Pad target account", errors);
    require_account_open(
        state,
        &pad.source_account,
        pad.date,
        "Pad source account",
        errors,
    );
    // Deliberate, known divergence in COUNT (decided in #2895): each account
    // is reported once, here at the pad. bean-check reports an unknown or
    // inactive pad account a second time, against the padding transaction it
    // synthesizes, whenever the padding is non-zero; rledger adds the padding
    // to its inventories below, with no such transaction, and the second
    // error would say nothing the first does not. The error lines agree.
    // Pinned by `test_validate_pad_reports_a_closed_account` and
    // `test_validate_pad_with_an_unopened_account_still_pads`.
    //
    // A pad dated after an account's close references an inactive account,
    // as beancount reports it (`Invalid reference to inactive account`). On
    // the close date itself the account is still active: a `close` sorts
    // after the other entries of its day, as for a posting
    // (`lifecycle_errors`).
    for (account, subject) in [
        (&pad.account, "Pad target account"),
        (&pad.source_account, "Pad source account"),
    ] {
        if let Some(closed) = state.accounts.get(account).and_then(|a| a.closed)
            && pad.date > closed
        {
            errors.push(ValidationError::new(
                ErrorCode::AccountClosed,
                format!(
                    "{subject} {account} is inactive on {} (closed on {closed})",
                    pad.date
                ),
                pad.date,
            ));
        }
    }

    // The padding applies whatever the accounts' state: beancount inserts it
    // before it validates anything, so a balance after the pad is checked
    // against the padded amount, and an unopened or closed account in the
    // pad is reported above but adds no balance failure. Both halves land
    // whatever the accounts' state, as beancount's padding entry posts to
    // both.
    //
    // It applies HERE, at the pad, as beancount dates and inserts its
    // padding entry: a balance on the source account between the pad and
    // the balance it satisfies sees it. The amounts are
    // `rustledger_booking::plan_pads`', the same `process_pads` writes out
    // (`crate::PadState`).
    let LedgerState {
        pads,
        inventories,
        inventory_accounts,
        ..
    } = state;
    for padding in pads.padding_of(index) {
        let number = padding.units.number;
        let currency = &padding.units.currency;
        // A pad amount that cannot be represented is reported, not clamped:
        // padding to a clamped figure would silently satisfy the very
        // assertion being checked (#1863).
        let mut pad_into = |account, number| {
            crate::account_inventory(inventories, inventory_accounts, account)
                .add(Position::simple(Amount::new(number, currency)))
                .err()
        };
        // Add to the target account, subtract from the source. A pad is two
        // halves of one entry, so if the source half overflows the target
        // half is UNDONE; otherwise the target carries a credit with no
        // matching debit, and a later assertion on it could pass off a pad
        // that never happened. The undo restores a total that existed a
        // moment ago, so it cannot itself overflow.
        let overflow = pad_into(&padding.target, number).or_else(|| {
            pad_into(&padding.source, -number).inspect(|_| {
                drop(pad_into(&padding.target, -number));
            })
        });
        if let Some(e) = overflow {
            errors.push(
                ValidationError::new(ErrorCode::ArithmeticOverflow, e.to_string(), pad.date)
                    .with_context(format!("account: {}", padding.target)),
            );
        }
    }
    if pads.is_unused(index) {
        pads.unused_found.push(crate::UnusedPadFound {
            date: pad.date,
            target: pad.account.clone(),
            source: pad.source_account.clone(),
            location,
        });
    }
}

/// Balance account checks — account presence (E1001) and the open's
/// currency constraint (E5002). Runs in the late phase's walk, on the
/// post-plugin stream, immediately before [`validate_balance_late`]'s
/// actual-vs-asserted comparison: a `balance` a plugin renamed is judged
/// under its new name (#2648), and one a plugin inserted (`check_drained`)
/// gets the currency check a written one gets (#2651).
pub fn validate_balance_account(
    state: &LedgerState,
    bal: &Balance,
    errors: &mut Vec<ValidationError>,
) {
    if !require_account_open(state, &bal.account, bal.date, "Account", errors) {
        return;
    }

    // Flag a balance asserted in a currency the account doesn't allow. Without
    // this, the only signal is a confusing "Balance failed ... got 0 EUR" (the
    // account simply holds no EUR); beancount emits a dedicated "invalid
    // currency for Balance" diagnostic. Only when the account constrains its
    // currencies (empty set = any currency allowed), matching the transaction
    // currency check — #1668.
    if let Some(account_state) = state.accounts.get(&bal.account)
        && !account_state.currencies.is_empty()
        && !account_state.currencies.contains(&bal.amount.currency)
    {
        let mut allowed: Vec<String> = account_state
            .currencies
            .iter()
            .map(std::string::ToString::to_string)
            .collect();
        allowed.sort();
        errors.push(ValidationError::new(
            ErrorCode::CurrencyNotAllowed,
            format!(
                "Invalid currency {} for Balance directive on {} (account holds {})",
                bal.amount.currency,
                bal.account,
                allowed.join(", ")
            ),
            bal.date,
        ));
    }
}

/// Late-phase balance validation — runs after booking + plugins.
///
/// Compares the asserted balance against the accumulated inventory state,
/// which already holds any padding (applied at its `pad`, see
/// [`validate_pad`]).
pub fn validate_balance_late(
    state: &mut LedgerState,
    bal: &Balance,
    index: usize,
    errors: &mut Vec<ValidationError>,
) {
    // `validate_balance_account`, called just before this, already reported
    // an account that is not open. The balance is still compared whatever
    // the account's state, as beancount compares it (it reports both the
    // account and a `Balance failed`): an unopened account's postings are in
    // its inventory (`crate::account_inventory`).
    //
    // A pad amount for this balance that could not be computed or applied is
    // reported, not clamped, and nothing was padded; comparing would only
    // add a balance failure for the same cause (#1863).
    if let Some(failure) = state.pads.failure_of(index) {
        errors.push(
            ValidationError::new(
                ErrorCode::ArithmeticOverflow,
                failure.message.clone(),
                bal.date,
            )
            .with_context(format!("account: {}", bal.account)),
        );
        return;
    }

    check_padding_at_cost(state, bal, index, errors);

    // Get inventory and check balance (no padding case).
    // In beancount, balance assertions include sub-accounts
    // e.g., balance Assets:Checking includes Assets:Checking:Sub1, etc.
    let actual = crate::sum_account_subtree(
        &state.inventories,
        &state.inventory_accounts,
        &bal.account,
        &bal.amount.currency,
    );

    // Always check balance assertions, even for accounts with no transactions.
    // This matches Python beancount behavior where `balance Account 1 USD` fails
    // if the account has 0 USD (no transactions).
    let expected = bal.amount.number;
    let difference = (actual - expected).abs();

    // Determine tolerance via the shared helper so out-of-pipeline
    // consumers (LSP code lens) and the validator stay in lockstep.
    let is_explicit = bal.tolerance.is_some();
    let tolerance = balance_tolerance(expected, bal.tolerance, state.options.tolerance_multiplier);
    let exceeds_tolerance = difference > tolerance;

    // Record the computed result so consumers can render per-assertion pass/fail
    // without re-deriving the balance (#1663). `diff` is signed (`computed −
    // asserted`); this is the validator's own `actual`, so the load/validate
    // surfaces can't diverge from the check.
    //
    // Recorded AFTER the tolerance is resolved so `exceeds_tolerance` comes
    // from the same comparison that raises the error below. A consumer that
    // re-derived "did this fail" from `diff` alone would be a second
    // implementation of the tolerance rule, and would disagree the moment
    // either changed (#2180).
    state.balance_actuals.push(crate::BalanceActual {
        date: bal.date,
        account: bal.account.clone(),
        currency: bal.amount.currency.clone(),
        asserted: expected,
        diff: actual - expected,
        exceeds_tolerance,
    });

    if exceeds_tolerance {
        // Use E2002 for explicit tolerance, E2001 for inferred
        let error_code = if is_explicit {
            ErrorCode::BalanceToleranceExceeded
        } else {
            ErrorCode::BalanceAssertionFailed
        };

        let message = if is_explicit {
            format!(
                "Balance exceeds explicit tolerance for {}: expected {} {} ~ {}, got {} {} (difference: {})",
                bal.account,
                expected,
                bal.amount.currency,
                tolerance,
                actual,
                bal.amount.currency,
                difference
            )
        } else {
            format!(
                "Balance failed for {}: expected {} {}, got {} {}",
                bal.account, expected, bal.amount.currency, actual, bal.amount.currency
            )
        };

        errors.push(
            ValidationError::new(error_code, message, bal.date)
                .with_context(format!("difference: {difference}, tolerance: {tolerance}")),
        );
    }
}

/// Beancount's "Attempt to pad an entry with cost" (`beancount/ops/pad.py`):
/// when padding is inserted for the `balance` at `index`, every position of
/// the padded currency that the padded account and its sub-accounts hold at
/// cost is an error, once per position, as beancount reports it (the same
/// lot held in two sub-accounts is one position there, as here). The padding
/// still applies (it was added at the pad), as beancount still inserts it.
///
/// The padding plan has units only (`rustledger_booking::plan_pads`), so the
/// lots are read here, from the booked inventories, which hold the lots
/// beancount's `pad_balance` holds: padding adds none at cost. The rest of
/// the message, what the group held without cost, is the plan's
/// ([`rustledger_booking::PlannedPadding::held`]): the booked inventories
/// also hold other pads' padding, which beancount's group does not see.
///
/// Only accounts a posting at cost was booked to are read, and only those
/// under the padded account (`LedgerState::cost_accounts`): a lot at cost
/// elsewhere in the ledger, or none, costs a padded balance nothing, as
/// beancount, reading its running `pad_balance`, pays nothing for it.
fn check_padding_at_cost(
    state: &LedgerState,
    bal: &Balance,
    index: usize,
    errors: &mut Vec<ValidationError>,
) {
    for (target, units, held) in state.pads.padded_for(index) {
        // The plan copies `held` only when a posting at cost in this
        // currency was made under `target`.
        let Some(held) = held else {
            continue;
        };
        let Some(accounts) = state.cost_accounts.get(&units.currency) else {
            continue;
        };
        let lots = match lots_at_cost(state, &units.currency, accounts, target) {
            Ok(lots) => lots,
            Err(e) => {
                errors.push(
                    ValidationError::new(
                        ErrorCode::PadWithCost,
                        format!("Attempt to pad an entry with cost ({e})"),
                        bal.date,
                    )
                    .with_context(format!("account: {target}")),
                );
                continue;
            }
        };
        let count = lots.positions().count();
        if count == 0 {
            continue;
        }
        let message = match shown_balance(state, target, &units.currency, lots, held) {
            // Beancount's `str(Inventory)`, sorted as it sorts.
            Ok(shown) => format!(
                "Attempt to pad an entry with cost for balance: {}",
                rustledger_core::python_inventory_str(shown.positions())
            ),
            Err(e) => format!("Attempt to pad an entry with cost ({e})"),
        };
        for _ in 0..count {
            errors.push(
                ValidationError::new(ErrorCode::PadWithCost, message.clone(), bal.date)
                    .with_context(format!("account: {target}")),
            );
        }
    }
}

/// The positions held at cost by those of `accounts` that are `target` or
/// under it, merged as one inventory merges them (one lot held in two
/// sub-accounts is one position).
fn lots_at_cost(
    state: &LedgerState,
    currency: &rustledger_core::Currency,
    accounts: &BTreeSet<Account>,
    target: &Account,
) -> Result<Inventory, OverflowError> {
    let mut lots = Inventory::new();
    let under =
        accounts
            .get(target.as_str())
            .into_iter()
            .chain(rustledger_core::strict_subaccounts(
                accounts,
                target.as_str(),
            ));
    for account in under {
        #[cfg(test)]
        tests::COST_ACCOUNTS_READ.with(|n| n.set(n.get() + 1));
        if let Some(inventory) = state.inventories.get(account) {
            for position in inventory
                .positions()
                .filter(|p| p.cost.is_some() && p.units.currency == *currency)
            {
                lots.add(position.clone())?;
            }
        }
    }
    Ok(lots)
}

/// What the message shows: the pad group's lots at cost in every currency
/// (`lots` already holds those of the padded one) and what it held without
/// cost, its units per currency (`held`) less the units at cost.
fn shown_balance(
    state: &LedgerState,
    target: &Account,
    padded: &rustledger_core::Currency,
    mut lots: Inventory,
    held: &[Amount],
) -> Result<Inventory, OverflowError> {
    for (currency, accounts) in &state.cost_accounts {
        if currency != padded {
            for position in lots_at_cost(state, currency, accounts, target)?.positions() {
                lots.add(position.clone())?;
            }
        }
    }
    let at_cost: Vec<rust_decimal::Decimal> =
        held.iter().map(|a| lots.units(&a.currency)).collect();
    for (amount, cost_units) in held.iter().zip(at_cost) {
        let plain = amount
            .number
            .checked_sub(cost_units)
            .ok_or_else(|| OverflowError {
                currency: amount.currency.clone(),
            })?;
        if !plain.is_zero() {
            lots.add(Position::simple(Amount::new(plain, &amount.currency)))?;
        }
    }
    Ok(lots)
}

#[cfg(test)]
mod tests {
    use crate::{ErrorCode, ValidationOptions, ValidationSession};

    std::thread_local! {
        /// Accounts the "pad an entry with cost" check has read on this
        /// thread, for the tests below.
        pub static COST_ACCOUNTS_READ: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
    }

    /// `n` sub-accounts of `Assets:P` holding 1 STK each without cost, a
    /// lot at cost in `lot_account`, then a `pad` on the parent before each
    /// sub-account's balance, each a different amount so every one pads.
    /// Returns the `E2005` count and the accounts the check read.
    fn run(n: usize, lot_account: &str) -> (usize, usize) {
        let mut source = format!(
            "2024-01-01 open Equity:O\n2024-01-01 open Assets:Cash\n2024-01-01 open {lot_account}\n\
             2024-01-01 * \"lot\"\n  {lot_account}  1 STK {{10.00 USD}}\n  Assets:Cash  -10.00 USD\n"
        );
        for i in 0..n {
            source.push_str(&format!(
                "2024-01-01 open Assets:P:C{i:05}\n2024-01-01 * \"x\"\n  Assets:P:C{i:05}  1.00 STK\n  Equity:O\n"
            ));
        }
        let mut day = rustledger_core::naive_date(2024, 1, 1).expect("date");
        for i in 0..n {
            day = day.tomorrow().expect("in range");
            source.push_str(&format!("{day} pad Assets:P Equity:O\n"));
            day = day.tomorrow().expect("in range");
            source.push_str(&format!(
                "{day} balance Assets:P:C{i:05} {}.00 STK\n",
                i + 2
            ));
        }
        let parsed = rustledger_parser::parse(&source);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let directives: Vec<_> = parsed.directives.into_iter().map(|d| d.value).collect();
        let today = rustledger_core::naive_date(2030, 1, 1).expect("date");
        COST_ACCOUNTS_READ.with(|c| c.set(0));
        let session = ValidationSession::new(ValidationOptions::default());
        let (session, mut errors) = session.run_early(&directives, today);
        let (session, late) = session.run_late(&directives, today);
        errors.extend(late);
        errors.extend(session.finalize());
        let cost_errors = errors
            .iter()
            .filter(|e| e.code == ErrorCode::PadWithCost)
            .count();
        (cost_errors, COST_ACCOUNTS_READ.with(std::cell::Cell::get))
    }

    /// A lot at cost OUTSIDE the padded account's subtree costs its padded
    /// balances nothing: no account is read. A ledger-wide "any lot at cost
    /// in this currency" gate read the whole subtree at every padded balance
    /// (#2920 review: 10k sub-accounts took 14.8 s where main took 0.29 s).
    #[test]
    fn test_padding_at_cost_reads_nothing_for_a_lot_outside_the_subtree() {
        let n = 300;
        let (cost_errors, read) = run(n, "Assets:Broker");
        assert_eq!(cost_errors, 0);
        assert_eq!(read, 0, "no account under Assets:P holds a lot at cost");
    }

    /// A lot at cost INSIDE the subtree is read once per padded balance, and
    /// no other account is: the check reads the accounts that hold a lot at
    /// cost, not the subtree.
    #[test]
    fn test_padding_at_cost_reads_only_the_accounts_with_a_lot() {
        let n = 300;
        let (cost_errors, read) = run(n, "Assets:P:Lot");
        assert_eq!(
            cost_errors, n,
            "every padded balance pads a currency held at cost"
        );
        assert_eq!(read, n, "one account read per padded balance");
    }
}
