//! Go-to-definition support for the editor.

use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use crate::types::EditorLocation;

use super::helpers::{get_word_at_position, is_currency_like};
use super::line_index::{EditorCache, LineIndex};

/// Get the definition location for the symbol at the given position (using cached data).
pub fn get_definition_cached(
    source: &str,
    line: u32,
    character: u32,
    parse_result: &ParseResult,
    cache: &EditorCache,
) -> Option<EditorLocation> {
    let word = get_word_at_position(source, line, character)?;

    // Check if it's an account name
    if (word.contains(':') || rustledger_core::is_default_account_root(&word))
        && let Some(location) =
            find_account_definition_cached(&word, parse_result, &cache.line_index)
    {
        return Some(location);
    }

    // Check if it's a currency
    if is_currency_like(&word)
        && let Some(location) =
            find_currency_definition_cached(&word, parse_result, &cache.line_index)
    {
        return Some(location);
    }

    None
}

/// Find the definition of an account (the Open directive) - cached version using `LineIndex`.
fn find_account_definition_cached(
    account: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
) -> Option<EditorLocation> {
    for spanned_directive in &parse_result.directives {
        if let Directive::Open(open) = &spanned_directive.value {
            let open_account = open.account.to_string();
            if open_account == account || account.starts_with(&format!("{open_account}:")) {
                let (line, character) = line_index.offset_to_position(spanned_directive.span.start);
                return Some(EditorLocation { line, character });
            }
        }
    }
    None
}

/// Get the definition location for the symbol at the given position (non-cached, used by tests).
#[cfg(test)]
pub fn get_definition(
    source: &str,
    line: u32,
    character: u32,
    parse_result: &ParseResult,
) -> Option<EditorLocation> {
    let cache = EditorCache::new(source, parse_result);
    get_definition_cached(source, line, character, parse_result, &cache)
}

/// Find the definition of a currency (the Commodity directive) - cached version using `LineIndex`.
fn find_currency_definition_cached(
    currency: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
) -> Option<EditorLocation> {
    for spanned_directive in &parse_result.directives {
        if let Directive::Commodity(comm) = &spanned_directive.value
            && comm.currency.as_ref() == currency
        {
            let (line, character) = line_index.offset_to_position(spanned_directive.span.start);
            return Some(EditorLocation { line, character });
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_get_definition_account() {
        let source = r#"2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);

        // Get definition of Assets:Bank from line 3
        let location = get_definition(source, 3, 4, &result);
        assert!(location.is_some());
        let loc = location.unwrap();
        assert_eq!(loc.line, 0); // Open directive is on line 0
    }
}
