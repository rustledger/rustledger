//! Account lifecycle validation.

use rustledger_core::{BookingMethod, Close, Inventory, Open};

use crate::error::{ErrorCode, ValidationError};
use crate::{AccountState, LedgerState};

use super::helpers::validate_account_name;

/// Validate an Open directive.
pub fn validate_open(state: &mut LedgerState, open: &Open, errors: &mut Vec<ValidationError>) {
    // Validate account name format
    if let Some(reason) = validate_account_name(&open.account, &state.options.account_types) {
        errors.push(
            ValidationError::new(
                ErrorCode::InvalidAccountName,
                format!("Invalid account name \"{}\": {}", open.account, reason),
                open.date,
            )
            .with_context(open.account.to_string()),
        );
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

    let booking = open
        .booking
        .as_ref()
        .and_then(|b| b.parse::<BookingMethod>().ok())
        .unwrap_or_default();

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
}

/// Early-phase Close validation — runs on pre-booking directives.
///
/// Checks that the account being closed exists and isn't already
/// closed, then marks it as closed in the ledger state so subsequent
/// transactions (in date-sorted order) correctly see it as inactive.
///
/// The "is the closing account balance non-zero?" check is deferred to
/// [`validate_close_late`] because it depends on inventory state the
/// late phase builds up.
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
        None => {
            errors.push(ValidationError::new(
                ErrorCode::AccountNotOpen,
                format!("Account {} was never opened", close.account),
                close.date,
            ));
        }
    }
}

/// Late-phase Close validation — runs after booking + plugins.
///
/// Reads `state.inventories[account]` (populated by late-phase
/// `validate_transaction_late`'s `update_inventories` step in
/// date-sorted order) and warns if the account being closed still
/// holds a non-zero balance.
pub fn validate_close_late(state: &LedgerState, close: &Close, errors: &mut Vec<ValidationError>) {
    // Only check accounts that actually got closed (i.e., not those
    // the early phase already flagged with E1001 or AccountClosed).
    // The early phase sets `account_state.closed = Some(close.date)`
    // on a successful close.
    let Some(account_state) = state.accounts.get(&close.account) else {
        return;
    };
    if account_state.closed != Some(close.date) {
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
