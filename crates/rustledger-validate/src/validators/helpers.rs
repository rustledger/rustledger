//! Helper functions for validation.

/// Validate an account name according to beancount rules.
/// Returns None if valid, or Some(reason) if invalid.
///
/// The `account_types` parameter specifies valid account type prefixes (from options
/// like `name_assets`, `name_liabilities`, etc.). Defaults are: Assets, Liabilities,
/// Equity, Income, Expenses.
pub fn validate_account_name(account: &str, account_types: &[String]) -> Option<String> {
    if account.is_empty() {
        return Some("account name is empty".to_string());
    }

    // Iterate components without allocating a Vec
    let mut components = account.split(':');

    // Check root account type (first component)
    let root = components.next()?;
    if root.is_empty() {
        return Some("component 1 is empty".to_string());
    }
    if !account_types.iter().any(|t| t == root) {
        return Some(format!(
            "account must start with one of: {}. To use a different root name, \
             rename a type via an option, e.g. `option \"name_income\" \"Revenue\"`",
            account_types.join(", ")
        ));
    }

    // Check each component (starting from root)
    // We already validated root's content will be checked below
    for (i, part) in std::iter::once(root).chain(components).enumerate() {
        if part.is_empty() {
            return Some(format!("component {} is empty", i + 1));
        }

        // First character must be an uppercase letter (any script) or digit.
        // Unicode uppercase (\p{Lu}) covers Latin A-Z, Cyrillic А-Я, etc.
        // Non-ASCII non-letter characters (CJK ideographs, etc.) are also
        // accepted as they have no case distinction.
        let Some(first_char) = part.chars().next() else {
            return Some(format!("component {} is empty", i + 1));
        };
        // Accept: uppercase letters (any script), digits, or non-ASCII
        // letters without case (CJK ideographs, etc.). Matches the lexer
        // regex [\p{Lu}\p{Lo}\p{Lt}0-9].
        let is_valid_start = first_char.is_uppercase()
            || first_char.is_ascii_digit()
            || (!first_char.is_ascii() && first_char.is_alphabetic());
        if !is_valid_start {
            return Some(format!(
                "component '{part}' must start with uppercase letter or digit"
            ));
        }

        // Remaining characters: letters (any script), digits, or hyphens.
        for c in part.chars().skip(1) {
            if !c.is_ascii_alphanumeric() && c != '-' && c.is_ascii() {
                return Some(format!(
                    "component '{part}' contains invalid character '{c}'"
                ));
            }
        }
    }

    None // Valid
}
