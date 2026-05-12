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

/// Validate a Close directive.
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
                // Check if account has non-zero balance (warning)
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
