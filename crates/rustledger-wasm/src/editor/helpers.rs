//! Helper functions for editor features.

use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use crate::types::EditorRange;

/// Get a specific line from source.
pub fn get_line(source: &str, line_num: usize) -> &str {
    source.lines().nth(line_num).unwrap_or("")
}

/// Get the word at a given position in the source.
pub fn get_word_at_position(source: &str, line: u32, character: u32) -> Option<String> {
    let line_text = source.lines().nth(line as usize)?;
    let chars: Vec<char> = line_text.chars().collect();
    let col = character as usize;

    // `character` is a character offset and is used to index `chars`, so
    // bound it by the character count, not the byte length (they differ
    // on multi-byte lines). Bounding by `line_text.len()` (bytes) would
    // accept an out-of-range char offset and then index incorrectly.
    if col > chars.len() {
        return None;
    }

    // Find start of word
    let mut start = col;
    while start > 0 && is_word_char(chars.get(start - 1).copied()?) {
        start -= 1;
    }

    // Find end of word
    let mut end = col;
    while end < chars.len() && is_word_char(chars[end]) {
        end += 1;
    }

    if start == end {
        return None;
    }

    Some(chars[start..end].iter().collect())
}

/// Check if a character is part of a word (including account separators).
pub fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == ':' || c == '_' || c == '-'
}

/// Check if a string looks like an account type.
pub fn is_account_type(s: &str) -> bool {
    matches!(
        s,
        "Assets" | "Liabilities" | "Equity" | "Income" | "Expenses"
    )
}

/// Check if a string looks like a currency (all uppercase, 2-5 chars).
pub fn is_currency_like(s: &str) -> bool {
    s.len() >= 2
        && s.len() <= 5
        && s.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
}

/// Extract all account names from parse result.
pub fn extract_accounts(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_accounts_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract all currencies from parse result.
pub fn extract_currencies(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_currencies_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract payees from parse result.
pub fn extract_payees(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_payees_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract tags from parse result. Tag text comes back without the
/// leading `#`, the form completion inserts after the already-typed
/// sigil.
pub fn extract_tags(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_tags_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract links from parse result. Like tags, link text comes back
/// without the leading `^`.
pub fn extract_links(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_links_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Count how many times an account is used in postings.
pub fn count_account_usages(account: &str, parse_result: &ParseResult) -> usize {
    let mut count = 0;
    for spanned_directive in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned_directive.value {
            for posting in &txn.postings {
                if posting.account.as_ref() == account {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count how many times a currency is used.
#[allow(clippy::cmp_owned)]
pub fn count_currency_usages(currency: &str, parse_result: &ParseResult) -> usize {
    let mut count = 0;
    for spanned_directive in &parse_result.directives {
        match &spanned_directive.value {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(ref units) = posting.units
                        && let Some(c) = units.currency()
                        && c.to_string() == currency
                    {
                        count += 1;
                    }
                }
            }
            Directive::Balance(bal) if bal.amount.currency.as_ref() == currency => {
                count += 1;
            }
            _ => {}
        }
    }
    count
}

/// Find a quoted string in a line and return its range (including quotes).
pub fn find_quoted_string_in_line(line: &str, text: &str, line_num: u32) -> Option<EditorRange> {
    // Look for the text within quotes
    let quoted = format!("\"{text}\"");
    if let Some(pos) = line.find(&quoted) {
        return Some(EditorRange {
            start_line: line_num,
            start_character: pos as u32,
            end_line: line_num,
            end_character: (pos + quoted.len()) as u32,
        });
    }
    None
}

/// Find a word in a line and return its range.
pub fn find_word_in_line(line: &str, word: &str, line_num: u32) -> Option<EditorRange> {
    find_nth_word_in_line(line, word, line_num, 0)
}

/// Find the nth occurrence of a word in a line and return its range.
pub fn find_nth_word_in_line(
    line: &str,
    word: &str,
    line_num: u32,
    n: usize,
) -> Option<EditorRange> {
    let mut count = 0;
    let mut start = 0;

    while let Some(pos) = line[start..].find(word) {
        let abs_pos = start + pos;
        // Check word boundaries
        let before_ok = abs_pos == 0 || !is_word_char(line.chars().nth(abs_pos - 1)?);
        let after_ok = abs_pos + word.len() >= line.len()
            || !is_word_char(line.chars().nth(abs_pos + word.len())?);

        if before_ok && after_ok {
            if count == n {
                return Some(EditorRange {
                    start_line: line_num,
                    start_character: abs_pos as u32,
                    end_line: line_num,
                    end_character: (abs_pos + word.len()) as u32,
                });
            }
            count += 1;
        }
        start = abs_pos + 1;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_get_word_at_position() {
        let source = "2024-01-01 open Assets:Bank USD";

        let word = get_word_at_position(source, 0, 11);
        assert_eq!(word, Some("open".to_string()));

        let word = get_word_at_position(source, 0, 20);
        assert_eq!(word, Some("Assets:Bank".to_string()));

        let word = get_word_at_position(source, 0, 28);
        assert_eq!(word, Some("USD".to_string()));
    }

    #[test]
    fn test_get_word_at_position_out_of_bounds() {
        let source = "hello";
        let word = get_word_at_position(source, 0, 100);
        assert!(word.is_none());
    }

    #[test]
    fn test_get_word_at_position_at_space() {
        let source = "hello world";
        let word = get_word_at_position(source, 0, 5);
        // Position 5 is 'o' in "hello", still part of word
        assert_eq!(word, Some("hello".to_string()));
    }

    #[test]
    fn test_get_word_at_position_multibyte() {
        // `character` is a CHARACTER offset. "롯" is 3 bytes / 1 char.
        // Account "Assets:롯데" is 9 characters; the cursor at char 8 is
        // inside the word. Bounding by char count (not byte length) must
        // accept this and return the full word.
        let source = "  Assets:롯데  100 KRW";
        let word = get_word_at_position(source, 0, 8);
        assert_eq!(word, Some("Assets:롯데".to_string()));
    }

    #[test]
    fn test_is_currency_like() {
        assert!(is_currency_like("USD"));
        assert!(is_currency_like("EUR"));
        assert!(is_currency_like("BTC"));
        assert!(is_currency_like("AAPL"));
        assert!(!is_currency_like("U")); // Too short
        assert!(!is_currency_like("VERYLONGCURRENCY")); // Too long
        assert!(!is_currency_like("usd")); // Lowercase
    }

    #[test]
    fn test_is_account_type() {
        assert!(is_account_type("Assets"));
        assert!(is_account_type("Liabilities"));
        assert!(is_account_type("Equity"));
        assert!(is_account_type("Income"));
        assert!(is_account_type("Expenses"));
        assert!(!is_account_type("Other"));
        assert!(!is_account_type("assets")); // Case-sensitive
    }

    #[test]
    fn test_extract_accounts() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food  5.00 USD
"#;
        let result = parse(source);
        let accounts = extract_accounts(&result);

        assert!(accounts.contains(&"Assets:Bank".to_string()));
        assert!(accounts.contains(&"Expenses:Food".to_string()));
    }

    #[test]
    fn test_extract_currencies() {
        let source = r"2024-01-01 open Assets:Bank USD
2024-01-01 commodity EUR
2024-01-15 balance Assets:Bank 100.00 GBP
";
        let result = parse(source);
        let currencies = extract_currencies(&result);

        assert!(currencies.contains(&"USD".to_string()));
        assert!(currencies.contains(&"EUR".to_string()));
        assert!(currencies.contains(&"GBP".to_string()));
    }

    #[test]
    fn test_extract_payees() {
        let source = r#"2024-01-15 * "Coffee Shop" "Morning coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-16 * "Restaurant" "Lunch"
  Assets:Bank  -20.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let payees = extract_payees(&result);

        assert!(payees.contains(&"Coffee Shop".to_string()));
        assert!(payees.contains(&"Restaurant".to_string()));
    }

    #[test]
    fn test_find_word_in_line() {
        let line = "2024-01-01 open Assets:Bank USD";
        let range = find_word_in_line(line, "open", 5);
        assert!(range.is_some());
        let r = range.unwrap();
        assert_eq!(r.start_line, 5);
        assert_eq!(r.start_character, 11);
        assert_eq!(r.end_character, 15);
    }

    #[test]
    fn test_find_nth_word_in_line() {
        let line = "USD EUR USD GBP";
        let first = find_nth_word_in_line(line, "USD", 0, 0);
        assert!(first.is_some());
        assert_eq!(first.unwrap().start_character, 0);

        let second = find_nth_word_in_line(line, "USD", 0, 1);
        assert!(second.is_some());
        assert_eq!(second.unwrap().start_character, 8);
    }

    #[test]
    fn test_find_quoted_string_in_line() {
        let line = r#"2024-01-15 * "Coffee Shop" "Morning coffee""#;
        let range = find_quoted_string_in_line(line, "Coffee Shop", 0);
        assert!(range.is_some());
        let r = range.unwrap();
        assert_eq!(r.start_character, 13);
        assert_eq!(r.end_character, 26);
    }
}
