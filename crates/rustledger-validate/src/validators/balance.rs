//! Balance and pad validation.

// ratchet: fxhash-only — hot path; use FxHashMap/FxHashSet, not std SipHash collections (#1237).
use rust_decimal::{Decimal, MathematicalOps};
use rustledger_core::{Amount, Balance, Pad, Position};

use super::helpers::require_account_open;
use crate::LedgerState;
use crate::error::{ErrorCode, ValidationError};
use rustledger_booking::PadAction;

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
    // synthesizes, whenever the padding is non-zero; rledger pads inline
    // (`validate_balance_late`) with no such transaction, and the second
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

    // Registered whatever the accounts' state: beancount inserts the padding
    // before it validates anything, so a balance after the pad is checked
    // against the padded amount, and an unopened or closed account in the
    // pad is reported above but adds no balance failure. Skipping the pad
    // here added a spurious E2001 on top of the account error. Both halves of
    // the padding land whatever the accounts' state, as beancount's padding
    // entry posts to both (`validate_balance_late`).
    state
        .pads
        .add(&pad.account, pad.date, pad.source_account.clone(), location);
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
/// Applies pending pads if any (E2004 multi-pad warning), then compares
/// the asserted balance against the accumulated inventory state.
pub fn validate_balance_late(
    state: &mut LedgerState,
    bal: &Balance,
    errors: &mut Vec<ValidationError>,
) {
    // `validate_balance_account`, called just before this, already reported
    // an account that is not open. The balance is still padded and compared
    // whatever the account's state, as beancount pads and compares it (it
    // reports both the account and a `Balance failed`): an unopened
    // account's postings are in its inventory (`crate::account_inventory`).
    //
    // Which pad this balance uses, and whether it pads, is the rule
    // `rustledger_booking::process_pads` applies (`PadTracker`): the latest
    // pad dated strictly before the balance, once per currency, a zero
    // difference using the currency up without using the pad. Only the
    // inventories differ: these are the validator's booked ones. The
    // `pad_parity_test` drift guard compares the two end to end.
    let LedgerState {
        pads,
        inventories,
        inventory_accounts,
        ..
    } = state;
    if let Some(step) = pads.balance(&bal.account, bal.date, &bal.amount, || {
        // Balance assertions include sub-accounts; the prefix index answers
        // this without scanning every account.
        Some(crate::sum_account_subtree(
            inventories,
            inventory_accounts,
            &bal.account,
            &bal.amount.currency,
        ))
    }) {
        push_multiple_pads_error(&step.contenders, bal, errors);
        if let PadAction::Pad(difference) = step.action {
            let source = step.pad.source_account.clone();
            // A pad amount that cannot be represented is reported, not
            // clamped: padding to a clamped figure would silently satisfy
            // the very assertion being checked (#1863).
            let mut pad_into = |account, number| {
                crate::account_inventory(inventories, inventory_accounts, account)
                    .add(Position::simple(Amount::new(number, &bal.amount.currency)))
                    .err()
            };
            // Add to the target account, subtract from the source. A pad is
            // two halves of one entry, so if the source half overflows the
            // target half is UNDONE; otherwise the target carries a credit
            // with no matching debit, and a later assertion on it could pass
            // off a pad that never happened. The undo restores a total that
            // existed a moment ago, so it cannot itself overflow.
            let overflow = pad_into(&bal.account, difference).or_else(|| {
                pad_into(&source, -difference).inspect(|_| {
                    drop(pad_into(&bal.account, -difference));
                })
            });

            if let Some(e) = overflow {
                errors.push(
                    ValidationError::new(ErrorCode::ArithmeticOverflow, e.to_string(), bal.date)
                        .with_context(format!("account: {}", bal.account)),
                );
            }
        }
        // The pad applied (or the account already held the amount); either
        // way, the regular balance check below would be redundant.
        return;
    }
    // No pad applies to this balance: fall through to the regular balance
    // check so the user gets a real assertion result instead of silent skip.

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

/// Report a balance with more than one pad before it (E2004): `contenders`
/// are the dates of the pads that no balance in its currency had reached yet
/// (`rustledger_booking::PadStep::contenders`). The balance uses only the
/// latest; the earlier ones are superseded, and also come out unused (E2003),
/// as beancount reports them.
fn push_multiple_pads_error(
    contenders: &[rustledger_core::NaiveDate],
    bal: &Balance,
    errors: &mut Vec<ValidationError>,
) {
    if contenders.len() > 1 {
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
                contenders
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
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
