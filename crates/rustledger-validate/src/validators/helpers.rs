//! Helper functions for validation.

use rustledger_core::{Account, NaiveDate};

use crate::LedgerState;
use crate::error::{ErrorCode, ValidationError};

/// The `E1005` (`InvalidAccountName`) error for `account`, with `reason` from
/// [`validate_account_name`]. The one definition of that message, shared by
/// the `open` check and the unknown-account checks below.
pub fn invalid_account_name_error(
    account: &Account,
    reason: &str,
    date: NaiveDate,
) -> ValidationError {
    ValidationError::new(
        ErrorCode::InvalidAccountName,
        format!("Invalid account name \"{account}\": {reason}"),
        date,
    )
    .with_context(account.to_string())
}

/// Report a reference to an account that is not open.
///
/// When the name itself is invalid under this ledger's roots (say
/// `Actifs:CCM:Courant` without `option "name_assets" "Actifs"`), that is the
/// error: `E1005` naming the configured roots and the option that renames
/// one. Reporting `E1001` "never opened" there pointed at the wrong fix, since
/// the `open` it suggests is rejected too (#2514). Beancount reports
/// `Invalid account name` for such an account as well. Otherwise this pushes
/// `E1001` with `unopened_message`.
///
/// Every unknown-account report goes through here, so the name check cannot
/// be skipped by one directive kind.
pub fn push_unknown_account(
    state: &LedgerState,
    account: &Account,
    date: NaiveDate,
    unopened_message: impl FnOnce() -> String,
    errors: &mut Vec<ValidationError>,
) {
    if let Some(reason) = validate_account_name(account, &state.options.account_types) {
        errors.push(invalid_account_name_error(account, &reason, date));
        return;
    }
    errors.push(ValidationError::new(
        ErrorCode::AccountNotOpen,
        unopened_message(),
        date,
    ));
}

/// Push an `E1001` (`AccountNotOpen`) error for `account` at `date` (or
/// `E1005` for an invalid name, see [`push_unknown_account`]). `subject`
/// names the account's role in the message — `"Account"`, `"Pad target
/// account"`, `"Pad source account"` — producing
/// `"<subject> <account> was never opened"`. This is the single definition of
/// the E1001 message and code, shared by every directive validator that reports
/// an unopened account.
pub fn push_account_not_open(
    state: &LedgerState,
    account: &Account,
    date: NaiveDate,
    subject: &str,
    errors: &mut Vec<ValidationError>,
) {
    push_unknown_account(
        state,
        account,
        date,
        || format!("{subject} {account} was never opened"),
        errors,
    );
}

/// Account-presence check for E1001. `state.accounts` is populated in date
/// order, so an account absent from it has not been opened on or before `date`.
/// Returns `true` when the account is open; otherwise pushes the E1001 error
/// (via [`push_account_not_open`]) and returns `false`. Callers that need to
/// bail out on an unopened account branch on the returned `bool`.
pub fn require_account_open(
    state: &LedgerState,
    account: &Account,
    date: NaiveDate,
    subject: &str,
    errors: &mut Vec<ValidationError>,
) -> bool {
    if state.accounts.contains_key(account) {
        return true;
    }
    push_account_not_open(state, account, date, subject, errors);
    false
}

/// Validate an account name according to beancount rules.
/// Returns None if valid, or Some(reason) if invalid.
///
/// The `account_types` parameter specifies valid account type prefixes (from options
/// like `name_assets`, `name_liabilities`, etc.). Defaults are: Assets, Liabilities,
/// Equity, Income, Expenses.
///
/// The character-level rule delegates to the canonical
/// [`rustledger_parser::is_valid_account_name`] (the lexer itself), so the
/// validator accepts exactly the set of names that can round-trip through
/// the parser — no more (the old hand-written check here admitted digit-start
/// roots and arbitrary non-ASCII characters mid-component, which the parser
/// rejects), and no less. The root-type membership check on top is ledger
/// semantics, not lexing, and stays here.
pub fn validate_account_name(account: &str, account_types: &[String]) -> Option<String> {
    if account.is_empty() {
        return Some("account name is empty".to_string());
    }

    // Check root account type (first component) — ledger semantics.
    let root = account.split(':').next()?;
    if !account_types.iter().any(|t| t == root) {
        return Some(format!(
            "account must start with one of: {}. To use a different root name, \
             rename a type via an option, e.g. `option \"name_income\" \"Revenue\"`",
            account_types.join(", ")
        ));
    }

    // Character/structure rule — the canonical parser predicate.
    if !rustledger_parser::is_valid_account_name(account) {
        return Some(format!(
            "'{account}' is not a valid account name: expected two or more \
             colon-separated components, each starting with an uppercase or \
             caseless letter (sub-components may start with a digit), \
             containing only letters, digits, and hyphens"
        ));
    }

    None // Valid
}

#[cfg(test)]
mod tests {
    use super::validate_account_name;

    fn types() -> Vec<String> {
        ["Assets", "Liabilities", "Equity", "Income", "Expenses"]
            .iter()
            .map(ToString::to_string)
            .collect()
    }

    #[test]
    fn accepts_parser_valid_names() {
        let t = types();
        assert_eq!(validate_account_name("Assets:Cash", &t), None);
        assert_eq!(validate_account_name("Assets:2024-Bonus", &t), None);
        assert_eq!(validate_account_name("Assets:US:BofA:Checking", &t), None);
    }

    #[test]
    fn respects_renamed_roots() {
        let t = vec!["Activa".to_string(), "Revenue".to_string()];
        assert_eq!(validate_account_name("Activa:Kas", &t), None);
        assert!(validate_account_name("Assets:Cash", &t).is_some());
    }

    #[test]
    fn rejects_what_the_lexer_rejects() {
        // Pre-L4 this validator hand-implemented the character rule and
        // accepted all of these; none can round-trip through the parser.
        // The rule now IS the lexer (rustledger_parser::is_valid_account_name).
        let t = types();
        // Single component: an account is Type:Component+.
        assert!(validate_account_name("Assets", &t).is_some());
        // Non-ASCII mid-component is VALID as of #1930 — beancount accepts it,
        // and this validator's rule IS the lexer, so it follows automatically.
        // These two assertions used to require rejection; they were pinning a
        // stricter-than-beancount rule, checked against beancount before being
        // flipped.
        assert!(validate_account_name("Assets:N\u{2116}1", &t).is_none()); // №
        assert!(validate_account_name("Assets:Cash\u{1F600}", &t).is_none()); // emoji
        // Lowercase sub-component start.
        assert!(validate_account_name("Assets:cash", &t).is_some());
        // Empty / structural.
        assert!(validate_account_name("", &t).is_some());
        assert!(validate_account_name("Assets:", &t).is_some());
        assert!(validate_account_name("Assets::Cash", &t).is_some());
    }

    #[test]
    fn digit_start_root_rejected_even_if_renamed() {
        // A digit-start root can never begin an Account token, so even a
        // matching renamed type is unusable (the loader warns E7008 at the
        // option site; this is the same rule seen from the validator).
        let t = vec!["1Assets".to_string()];
        assert!(validate_account_name("1Assets:Cash", &t).is_some());
    }
}
