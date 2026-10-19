//! Account lifecycle validation.

use rustledger_core::{BookingMethod, Close, Inventory, Open};

use crate::error::{ErrorCode, ValidationError};
use crate::{AccountState, LedgerState};

use super::helpers::{invalid_account_name_error, push_account_not_open, validate_account_name};

/// Validate an Open directive.
pub fn validate_open(state: &mut LedgerState, open: &Open, errors: &mut Vec<ValidationError>) {
    // Validate account name format
    if let Some(reason) = validate_account_name(&open.account, &state.options.account_types) {
        errors.push(invalid_account_name_error(
            &open.account,
            &reason,
            open.date,
        ));
        // Continue anyway to allow further validation
    }

    // Check if already open
    if let Some(existing) = state.accounts.get(&open.account) {
        errors.push(ValidationError::new(
            ErrorCode::AccountAlreadyOpen,
            format!(
                "Account {} is already open (opened on {})",
                open.account, existing.opened
            ),
            open.date,
        ));
        return;
    }

    // Fall back to the file-level default booking method (set from
    // `option "booking_method"`) rather than `BookingMethod::default()`
    // (STRICT). Without this, opening `2000-01-01 open Assets:Foo` under
    // `option "booking_method" "NONE"` would still validate against
    // STRICT semantics and re-raise the lot-matching errors the booker
    // just skipped — see issue #1182.
    let booking = open
        .booking
        .as_ref()
        .and_then(|b| b.parse::<BookingMethod>().ok())
        .unwrap_or(state.options.default_booking_method);

    state.accounts.insert(
        open.account.clone(),
        AccountState {
            opened: open.date,
            closed: None,
            currencies: open.currencies.iter().cloned().collect(),
            booking,
        },
    );

    state
        .inventories
        .insert(open.account.clone(), Inventory::new());
    // Keep the sub-account prefix index in lockstep with `inventories`.
    state.inventory_accounts.insert(open.account.clone());
}

/// Close registration — runs in the late phase's open/close pre-pass, on
/// the post-plugin stream (so a renamed or plugin-inserted close counts).
///
/// Checks that the account being closed exists and isn't already
/// closed, then marks it as closed in the ledger state so the
/// date-ordered walk judges postings against it.
///
/// The "is the closing account balance non-zero?" check is
/// [`validate_close_late`], in the walk itself, because it depends on the
/// inventory state the walk builds up.
pub fn validate_close(state: &mut LedgerState, close: &Close, errors: &mut Vec<ValidationError>) {
    match state.accounts.get_mut(&close.account) {
        Some(account_state) => {
            if account_state.closed.is_some() {
                errors.push(ValidationError::new(
                    ErrorCode::AccountClosed,
                    format!("Account {} already closed", close.account),
                    close.date,
                ));
            } else {
                account_state.closed = Some(close.date);
            }
        }
        None => push_account_not_open(state, &close.account, close.date, "Account", errors),
    }
}

/// Close balance check — runs in the late phase's date-ordered walk.
///
/// Reads `state.inventories[account]` (populated by late-phase
/// `validate_transaction_late`'s `update_inventories` step in
/// date-sorted order) and warns if the account being closed still
/// holds a non-zero balance.
pub fn validate_close_late(
    state: &mut LedgerState,
    close: &Close,
    errors: &mut Vec<ValidationError>,
) {
    // Only check accounts that actually got closed (i.e., not those
    // the pre-pass already flagged with E1001 or AccountClosed).
    // `validate_close` sets `account_state.closed = Some(close.date)`
    // on a successful close.
    let Some(account_state) = state.accounts.get(&close.account) else {
        return;
    };
    if account_state.closed != Some(close.date) {
        return;
    }
    // Skip the duplicate Close that `validate_close` already rejected
    // with `AccountClosed`. Without this guard, two same-day closes
    // for the same account would both pass the `closed == Some(close.date)`
    // check and double-emit `AccountCloseNotEmpty`. Keyed by
    // (account, date) so that a legitimate later close after a reopen
    // (if that's ever supported) still runs the inventory check.
    if !state
        .late_close_processed
        .insert((close.account.clone(), close.date))
    {
        return;
    }
    if let Some(inv) = state.inventories.get(&close.account)
        && !inv.is_empty()
    {
        let positions: Vec<String> = inv
            .positions()
            .map(|p| format!("{} {}", p.units.number, p.units.currency))
            .collect();
        errors.push(
            ValidationError::new(
                ErrorCode::AccountCloseNotEmpty,
                format!(
                    "Cannot close account {} with non-zero balance",
                    close.account
                ),
                close.date,
            )
            .with_context(format!("balance: {}", positions.join(", "))),
        );
    }
}
