//! Balance and pad validation.

// ratchet: fxhash-only — hot path; use FxHashMap/FxHashSet, not std SipHash collections (#1237).
use rustledger_booking::balance_tolerance;
use rustledger_core::{Amount, Balance, Pad, Position};

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

/// Beancount's "Attempt to pad an entry with cost" (`beancount/ops/pad.py`),
/// reported at the `balance` at `index`, once per lot, as beancount reports
/// it. The padding still applies (it was added at the pad), as beancount
/// still inserts it.
///
/// The plan derives it (`rustledger_booking::PaddedAtCost`) from each pad
/// group's own running inventory, beancount's `pad_balance`, so this only
/// reports it: the one rule lives in the plan, which `process_pads` reports
/// from too.
fn check_padding_at_cost(
    state: &LedgerState,
    bal: &Balance,
    index: usize,
    errors: &mut Vec<ValidationError>,
) {
    for (target, at_cost) in state.pads.at_cost_of(index) {
        let message = at_cost.message();
        for _ in 0..at_cost.lots {
            errors.push(
                ValidationError::new(ErrorCode::PadWithCost, message.clone(), bal.date)
                    .with_context(format!("account: {target}")),
            );
        }
    }
}
