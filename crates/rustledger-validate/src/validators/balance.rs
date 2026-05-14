//! Balance and pad validation.

use rust_decimal::{Decimal, MathematicalOps};
use rustledger_core::{Amount, Balance, Pad, Position};

use crate::error::{ErrorCode, ValidationError};
use crate::{LedgerState, PendingPad};

use rustc_hash::FxHashMap;
use rustledger_core::{InternedStr, Inventory};

/// Multiplier for balance assertion tolerance (matches Python beancount).
/// Balance assertions use 2x the `tolerance_multiplier` option.
const BALANCE_TOLERANCE_MULTIPLIER: Decimal = Decimal::TWO;

/// Sum the units of a given currency across an account and all its sub-accounts.
///
/// In beancount, `balance Assets:Bank` includes `Assets:Bank:Checking`,
/// `Assets:Bank:Savings`, etc. This function checks for exact match or
/// sub-account prefix (account followed by `:`) without allocating.
fn sum_account_and_subaccounts(
    inventories: &FxHashMap<InternedStr, Inventory>,
    account: &InternedStr,
    currency: &InternedStr,
) -> Decimal {
    let account_str = account.as_str();
    let mut total = Decimal::ZERO;
    for (inv_account, inv) in inventories {
        if inv_account == account
            || (inv_account.starts_with(account_str)
                && inv_account.as_bytes().get(account_str.len()) == Some(&b':'))
        {
            total += inv.units(currency);
        }
    }
    total
}

/// Base 10 for tolerance scale calculation.
const DECIMAL_TEN: Decimal = Decimal::TEN;

/// Validate a Pad directive.
pub fn validate_pad(state: &mut LedgerState, pad: &Pad, errors: &mut Vec<ValidationError>) {
    // Check that the target account exists
    if !state.accounts.contains_key(&pad.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Pad target account {} was never opened", pad.account),
            pad.date,
        ));
        return;
    }

    // Check that the source account exists
    if !state.accounts.contains_key(&pad.source_account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Pad source account {} was never opened", pad.source_account),
            pad.date,
        ));
        return;
    }

    // Add to pending pads list for this account
    let pending_pad = PendingPad {
        source_account: pad.source_account.clone(),
        date: pad.date,
        used: false,
    };
    state
        .pending_pads
        .entry(pad.account.clone())
        .or_default()
        .push(pending_pad);
}

/// Early-phase balance validation — runs on pre-booking directives.
///
/// Only checks account presence (E1001). The actual-vs-asserted
/// comparison is deferred to the late phase, since it depends on the
/// inventory state that booking + the late-phase transaction validator
/// build up.
pub fn validate_balance_early(
    state: &LedgerState,
    bal: &Balance,
    errors: &mut Vec<ValidationError>,
) {
    if !state.accounts.contains_key(&bal.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!("Account {} was never opened", bal.account),
            bal.date,
        ));
    }
}

/// Late-phase balance validation — runs after booking + plugins.
///
/// Applies pending pads if any (E2004 multi-pad warning), then compares
/// the asserted balance against the accumulated inventory state.
pub fn validate_balance_late(
    state: &mut LedgerState,
    bal: &Balance,
    errors: &mut Vec<ValidationError>,
) {
    // The early phase already verified the account exists. If somehow
    // it disappeared between phases (it shouldn't), bail out quietly —
    // the early error is already in the report.
    if !state.accounts.contains_key(&bal.account) {
        return;
    }

    // Check if there are pending pads for this account
    // Use get_mut instead of remove - a pad can apply to multiple currencies
    if let Some(pending_pads) = state.pending_pads.get_mut(&bal.account) {
        // Drop pads that already served a previous balance assertion.
        // Without this, the vec grows for the lifetime of the session
        // and the E2003 finalize sweep scans every pad ever pushed.
        pending_pads.retain(|p| !p.used);

        // A Pad on date D is effective for the NEXT Balance on the
        // target account dated strictly after D (Python beancount
        // semantics — Pad creates an entry "between" D and the next
        // balance). Filter `pending_pads` to those whose date precedes
        // this balance; later-dated pads are still pending for some
        // future balance and must not be considered here. Required
        // because the phase split pre-registers ALL pads during Early
        // before any Balance runs in Late.
        let effective_idx: Vec<usize> = pending_pads
            .iter()
            .enumerate()
            .filter(|(_, p)| p.date < bal.date)
            .map(|(i, _)| i)
            .collect();

        // Check for multiple effective pads (E2004) — every effective
        // pad is unused (retain ran above), so we just need to count.
        if effective_idx.len() > 1 {
            errors.push(
                ValidationError::new(
                    ErrorCode::MultiplePadForBalance,
                    format!(
                        "Multiple pad directives for {} {} before balance assertion",
                        bal.account, bal.amount.currency
                    ),
                    bal.date,
                )
                .with_context(format!(
                    "pad dates: {}",
                    effective_idx
                        .iter()
                        .map(|&i| pending_pads[i].date.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )),
            );
        }

        // Use the most recent effective pad
        if let Some(pending_pad) = effective_idx.last().and_then(|&i| pending_pads.get_mut(i)) {
            // Apply padding: calculate difference and add to both accounts
            // Balance assertions include sub-accounts, so sum them all up
            let actual =
                sum_account_and_subaccounts(&state.inventories, &bal.account, &bal.amount.currency);
            {
                let expected = bal.amount.number;
                let difference = expected - actual;

                if difference != Decimal::ZERO {
                    // Add padding amount to target account
                    if let Some(target_inv) = state.inventories.get_mut(&bal.account) {
                        target_inv.add(Position::simple(Amount::new(
                            difference,
                            &bal.amount.currency,
                        )));
                    }

                    // Subtract padding amount from source account
                    if let Some(source_inv) = state.inventories.get_mut(&pending_pad.source_account)
                    {
                        source_inv.add(Position::simple(Amount::new(
                            -difference,
                            &bal.amount.currency,
                        )));
                    }

                    // Mark pad as used only if padding was actually needed
                    pending_pad.used = true;
                }
            }
            // An effective pad applied (or matched a zero difference);
            // either way, the regular balance check below would be
            // redundant.
            return;
        }
        // No effective pad for this balance — fall through to the
        // regular balance check so the user gets a real assertion
        // result instead of silent skip.
    }

    // Get inventory and check balance (no padding case).
    // In beancount, balance assertions include sub-accounts
    // e.g., balance Assets:Checking includes Assets:Checking:Sub1, etc.
    let actual =
        sum_account_and_subaccounts(&state.inventories, &bal.account, &bal.amount.currency);

    // Always check balance assertions, even for accounts with no transactions.
    // This matches Python beancount behavior where `balance Account 1 USD` fails
    // if the account has 0 USD (no transactions).
    let expected = bal.amount.number;
    let difference = (actual - expected).abs();

    // Determine tolerance. Use explicit tolerance if specified, otherwise derive
    // from the balance assertion amount's decimal precision (Python beancount behavior).
    // See: https://github.com/beancount/beancount/blob/master/beancount/ops/balance.py
    let (tolerance, is_explicit) = if let Some(t) = bal.tolerance {
        (t, true)
    } else {
        // Python beancount derives tolerance from the balance amount's decimal places:
        //   expo = balance_entry.amount.number.as_tuple().exponent
        //   tolerance = tolerance_multiplier * 2 * 10^expo
        // In rust_decimal, scale() gives number of decimal places (positive), so we negate it.
        let scale = expected.scale();
        if scale > 0 {
            let quantum = DECIMAL_TEN.powi(-i64::from(scale));
            (
                state.options.tolerance_multiplier * BALANCE_TOLERANCE_MULTIPLIER * quantum,
                false,
            )
        } else {
            // Integer amount: exact match required
            (Decimal::ZERO, false)
        }
    };

    if difference > tolerance {
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
