//! Balance and pad validation.

// ratchet: fxhash-only — hot path; use FxHashMap/FxHashSet, not std SipHash collections (#1237).
use rust_decimal::{Decimal, MathematicalOps};
use rustledger_core::{Amount, Balance, Pad, Position};

use super::helpers::require_account_open;
use crate::error::{ErrorCode, ValidationError};
use crate::{LedgerState, PendingPad};

/// Multiplier for balance assertion tolerance (matches Python beancount).
/// Balance assertions use 2x the `tolerance_multiplier` option.
const BALANCE_TOLERANCE_MULTIPLIER: Decimal = Decimal::TWO;

/// Compute the tolerance to apply when comparing a balance assertion's
/// expected amount against the booked actual.
///
/// - `expected`: the asserted amount from the balance directive.
/// - `explicit`: the `~ tolerance` from the directive, if any (always
///   wins).
/// - `tolerance_multiplier`: the active `inferred_tolerance_multiplier`
///   option (default 0.5; overridable via `option
///   "inferred_tolerance_multiplier" "..."`).
///
/// Mirrors the inline logic in `validate_balance_late` (private) so
/// out-of-pipeline consumers (currently the LSP code-lens path)
/// produce the same verdict as the validator without re-deriving the
/// rule from the Beancount spec.
///
/// Matches Python beancount:
/// <https://github.com/beancount/beancount/blob/master/beancount/ops/balance.py>
#[must_use]
pub fn balance_tolerance(
    expected: Decimal,
    explicit: Option<Decimal>,
    tolerance_multiplier: Decimal,
) -> Decimal {
    if let Some(t) = explicit {
        return t;
    }
    let scale = expected.scale();
    if scale > 0 {
        let quantum = DECIMAL_TEN.powi(-i64::from(scale));
        tolerance_multiplier * BALANCE_TOLERANCE_MULTIPLIER * quantum
    } else {
        Decimal::ZERO
    }
}

/// Base 10 for tolerance scale calculation.
const DECIMAL_TEN: Decimal = Decimal::TEN;

/// Validate a Pad directive.
pub fn validate_pad(
    state: &mut LedgerState,
    pad: &Pad,
    location: Option<(rustledger_parser::Span, u16)>,
    errors: &mut Vec<ValidationError>,
) {
    // Check that the target account exists
    if !require_account_open(state, &pad.account, pad.date, "Pad target account", errors) {
        return;
    }

    // Check that the source account exists
    if !require_account_open(
        state,
        &pad.source_account,
        pad.date,
        "Pad source account",
        errors,
    ) {
        return;
    }

    // Add to pending pads list for this account
    let pending_pad = PendingPad {
        source_account: pad.source_account.clone(),
        date: pad.date,
        padded_currencies: rustc_hash::FxHashSet::default(),
        location,
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
    require_account_open(state, &bal.account, bal.date, "Account", errors);

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
        // Drop pads that have already served a balance in THIS specific
        // currency. A single Pad can still serve multiple
        // currency-specific Balance assertions on the same target —
        // we only remove pads that have nothing left to offer for the
        // currency being asserted right now. Without this, the vec grows
        // for the lifetime of the session and E2003 / E2004 detection
        // fires against pads that already served their purpose.
        pending_pads.retain(|p| !p.padded_currencies.contains(&bal.amount.currency));

        // A Pad on date D is effective for the NEXT Balance on the
        // target account dated strictly after D (Python beancount
        // semantics — Pad creates an entry "between" D and the next
        // balance). Filter `pending_pads` to those whose date precedes
        // this balance; later-dated pads are still pending for some
        // future balance and must not be considered here. Required
        // because the phase split pre-registers ALL pads during Early
        // before any Balance runs in Late.
        //
        // The early-phase iteration sorts pads by date (see
        // `validate_phase_inner`), so `pending_pads` is itself in
        // date-sorted push order — `effective_idx.last()` is therefore
        // the most recent effective pad (Python's `active_pad`).
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
            // Balance assertions include sub-accounts; the prefix index answers
            // this without scanning every account (disjoint borrow from the
            // `pending_pad` mutable borrow held here).
            let actual = crate::sum_account_subtree(
                &state.inventories,
                &state.inventory_accounts,
                &bal.account,
                &bal.amount.currency,
            );
            {
                let expected = bal.amount.number;
                let difference = expected - actual;

                if difference != Decimal::ZERO {
                    // A pad amount that cannot be represented is reported, not
                    // clamped — padding to a clamped figure would silently
                    // satisfy the very assertion being checked (#1863).
                    let mut pad_into = |account, number| {
                        state
                            .inventories
                            .get_mut(account)
                            .map(|inv| {
                                inv.add(Position::simple(Amount::new(number, &bal.amount.currency)))
                            })
                            .transpose()
                            .err()
                    };
                    // Add to the target account, subtract from the source. A
                    // pad is two halves of one entry, so if the source half
                    // overflows the target half is UNDONE — otherwise the
                    // target carries a credit with no matching debit, and a
                    // later assertion on it could pass off a pad that never
                    // happened. The undo restores a total that existed a
                    // moment ago, so it cannot itself overflow.
                    let overflow = pad_into(&bal.account, difference).or_else(|| {
                        pad_into(&pending_pad.source_account, -difference).inspect(|_| {
                            drop(pad_into(&bal.account, -difference));
                        })
                    });

                    if let Some(e) = overflow {
                        errors.push(
                            ValidationError::new(
                                ErrorCode::ArithmeticOverflow,
                                e.to_string(),
                                bal.date,
                            )
                            .with_context(format!("account: {}", bal.account)),
                        );
                    }

                    // Record that this pad covered the asserted currency.
                    pending_pad
                        .padded_currencies
                        .insert(bal.amount.currency.clone());
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

    // Record the computed result so consumers can render per-assertion pass/fail
    // without re-deriving the balance (#1663). `diff` is signed (`computed −
    // asserted`); this is the validator's own `actual`, so the load/validate
    // surfaces can't diverge from the check.
    state.balance_actuals.push(crate::BalanceActual {
        date: bal.date,
        account: bal.account.clone(),
        currency: bal.amount.currency.clone(),
        diff: actual - expected,
    });

    // Determine tolerance via the shared helper so out-of-pipeline
    // consumers (LSP code lens) and the validator stay in lockstep.
    let is_explicit = bal.tolerance.is_some();
    let tolerance = balance_tolerance(expected, bal.tolerance, state.options.tolerance_multiplier);

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

#[cfg(test)]
mod tolerance_tests {
    use super::*;
    use rust_decimal_macros::dec;

    /// Default `tolerance_multiplier` from `ValidationOptions::default()`
    /// (also the loader's default via `Options::new()`).
    fn default_mul() -> Decimal {
        dec!(0.5)
    }

    #[test]
    fn explicit_tolerance_always_wins() {
        // Even an absurdly-small / absurdly-large explicit tolerance
        // overrides the scale-derived default. This is the
        // contract `~ tolerance` on a Balance directive provides.
        assert_eq!(
            balance_tolerance(dec!(100.00), Some(dec!(0.001)), default_mul()),
            dec!(0.001)
        );
        assert_eq!(
            balance_tolerance(dec!(100.00), Some(dec!(50)), default_mul()),
            dec!(50)
        );
    }

    #[test]
    fn integer_amount_requires_exact_match() {
        // scale == 0 means the asserted amount has no decimal places.
        // Python beancount requires an exact match in that case; the
        // helper returns ZERO to make `difference > 0` strict.
        assert_eq!(
            balance_tolerance(dec!(100), None, default_mul()),
            Decimal::ZERO
        );
    }

    #[test]
    fn two_decimal_amount_uses_default_quantum() {
        // For `100.00 USD` with the default multiplier 0.5:
        //   tolerance = 0.5 * 2 * 0.01 = 0.01
        // This is the Beancount-spec rule the LSP and the validator
        // both depend on; if this changes, every balance assertion
        // shifts pass/fail.
        assert_eq!(
            balance_tolerance(dec!(100.00), None, default_mul()),
            dec!(0.01)
        );
    }

    #[test]
    fn higher_precision_scales_down() {
        // 4 decimal places: tolerance = 0.5 * 2 * 0.0001 = 0.0001
        assert_eq!(
            balance_tolerance(dec!(100.0000), None, default_mul()),
            dec!(0.0001)
        );
    }

    #[test]
    fn multiplier_one_doubles_default() {
        // File overrides `option "inferred_tolerance_multiplier" "1.0"`:
        //   tolerance = 1.0 * 2 * 0.01 = 0.02
        assert_eq!(balance_tolerance(dec!(100.00), None, dec!(1.0)), dec!(0.02));
    }

    #[test]
    fn multiplier_zero_forces_strict_match() {
        // `option "inferred_tolerance_multiplier" "0.0"` is the
        // canonical way to force strict equality on a decimal
        // amount. The helper must yield zero so the validator emits
        // a diagnostic on any rounding drift.
        assert_eq!(
            balance_tolerance(dec!(100.00), None, dec!(0.0)),
            Decimal::ZERO
        );
    }

    #[test]
    fn negative_amount_uses_same_scale_logic() {
        // Tolerance is sign-independent (the validator applies it
        // against `(actual - expected).abs()`), but the helper does
        // not flip sign on negative expected — scale() is unsigned.
        assert_eq!(
            balance_tolerance(dec!(-100.00), None, default_mul()),
            dec!(0.01)
        );
    }
}
