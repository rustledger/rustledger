//! Shared utility functions for LSP handlers.
//!
//! This module contains common utilities used across multiple handlers,
//! including position conversion, word extraction, and type checking.

use lsp_types::Position;
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

/// A line index for efficient offset-to-position conversion.
///
/// Building the index is O(n) where n is the source length, but subsequent
/// lookups are O(log(lines)) using binary search. This is much faster than
/// the naive O(n) approach when doing multiple conversions on the same source.
///
/// # Example
///
/// ```ignore
/// let index = LineIndex::new(source);
/// let (line, col) = index.offset_to_position(offset);
/// ```
#[derive(Debug, Clone)]
pub struct LineIndex {
    /// Byte offset of the start of each line (including line 0 at offset 0).
    line_starts: Vec<usize>,
    /// Total length of the source in bytes.
    len: usize,
}

impl LineIndex {
    /// Build a line index from source text.
    ///
    /// This is O(n) where n is the source length.
    pub fn new(source: &str) -> Self {
        let mut line_starts = vec![0]; // Line 0 starts at offset 0

        for (i, ch) in source.char_indices() {
            if ch == '\n' {
                line_starts.push(i + 1); // Next line starts after the newline
            }
        }

        Self {
            line_starts,
            len: source.len(),
        }
    }

    /// Convert a byte offset to a (line, column) position (0-based).
    ///
    /// This is O(log(lines)) using binary search.
    pub fn offset_to_position(&self, offset: usize) -> (u32, u32) {
        let offset = offset.min(self.len);

        // Binary search for the line containing this offset
        let line = match self.line_starts.binary_search(&offset) {
            Ok(line) => line,                    // Exact match: offset is at line start
            Err(line) => line.saturating_sub(1), // Between lines: use previous line
        };

        let line_start = self.line_starts[line];
        let col = offset - line_start;

        (line as u32, col as u32)
    }

    /// Convert a (line, column) position to a byte offset.
    ///
    /// Returns None if the position is out of bounds.
    pub fn position_to_offset(&self, line: u32, col: u32) -> Option<usize> {
        let line = line as usize;
        if line >= self.line_starts.len() {
            return None;
        }

        let line_start = self.line_starts[line];
        let offset = line_start + col as usize;

        if offset <= self.len {
            Some(offset)
        } else {
            None
        }
    }

    /// Get the number of lines in the source.
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }
}

/// Convert a byte offset to a line/column position (0-based for LSP).
///
/// Note: This is O(n) where n is the offset. For handlers that do multiple
/// conversions on the same source, use [`LineIndex`] instead for O(log n) lookups.
pub fn byte_offset_to_position(source: &str, offset: usize) -> (u32, u32) {
    let mut line = 0u32;
    let mut col = 0u32;

    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }

    (line, col)
}

/// Convert an LSP character offset (UTF-16 code units) to a byte offset in a UTF-8 line.
///
/// LSP `Position.character` counts UTF-16 code units. For BMP characters (ASCII,
/// CJK, Korean, Cyrillic, etc.) one code point = one UTF-16 unit, but non-BMP
/// characters (many emoji) use two UTF-16 units (a surrogate pair).
/// Returns `line.len()` if the offset is past the end.
pub fn char_offset_to_byte(line: &str, utf16_offset: usize) -> usize {
    let mut utf16_count = 0usize;
    for (byte_offset, ch) in line.char_indices() {
        if utf16_count >= utf16_offset {
            return byte_offset;
        }
        utf16_count += ch.len_utf16();
    }
    line.len()
}

/// Get the word at a given column position in a line.
///
/// Returns the word, its start column, and end column (0-based).
/// Words include alphanumeric characters, colons, hyphens, and underscores.
pub fn get_word_at_position(line: &str, col: usize) -> Option<(String, usize, usize)> {
    let chars: Vec<char> = line.chars().collect();
    if col > chars.len() {
        return None;
    }

    // Find word start
    let mut start = col;
    while start > 0 && is_word_char(chars.get(start - 1).copied().unwrap_or(' ')) {
        start -= 1;
    }

    // Find word end
    let mut end = col;
    while end < chars.len() && is_word_char(chars[end]) {
        end += 1;
    }

    if start == end {
        return None;
    }

    let word: String = chars[start..end].iter().collect();
    Some((word, start, end))
}

/// Get the word at a position in a source document.
///
/// This is a convenience wrapper that handles line extraction.
pub fn get_word_at_source_position(source: &str, position: Position) -> Option<String> {
    let line = source.lines().nth(position.line as usize)?;
    let col = position.character as usize;

    // Handle UTF-8: convert character offset to byte offset for the line
    let byte_col = line
        .char_indices()
        .nth(col)
        .map(|(i, _)| i)
        .unwrap_or(line.len());

    if byte_col > line.len() {
        return None;
    }

    let chars: Vec<char> = line.chars().collect();

    // Find word boundaries
    let mut start = col.min(chars.len());
    while start > 0 && is_word_char(chars.get(start - 1).copied().unwrap_or(' ')) {
        start -= 1;
    }

    let mut end = col.min(chars.len());
    while end < chars.len() && is_word_char(chars[end]) {
        end += 1;
    }

    if start == end {
        return None;
    }

    Some(chars[start..end].iter().collect())
}

/// Check if a character is part of a word (for Beancount identifiers).
pub fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == ':' || c == '-' || c == '_'
}

/// Check if a string looks like an account name.
///
/// Account names start with a standard account type and contain colons.
pub fn is_account_like(s: &str) -> bool {
    s.contains(':')
        && (s.starts_with("Assets")
            || s.starts_with("Liabilities")
            || s.starts_with("Equity")
            || s.starts_with("Income")
            || s.starts_with("Expenses"))
}

/// Check if a string is a standard account type.
pub fn is_account_type(s: &str) -> bool {
    matches!(
        s,
        "Assets" | "Liabilities" | "Equity" | "Income" | "Expenses"
    )
}

/// Check if a string looks like a currency (simple format check).
///
/// Currencies are typically 2-5 uppercase letters/digits (e.g., USD, EUR, BTC).
pub fn is_currency_like_simple(s: &str) -> bool {
    s.len() >= 2
        && s.len() <= 5
        && s.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
}

/// Check if a string looks like a currency, validating against known currencies.
///
/// This checks the format AND verifies the currency exists in the document.
pub fn is_currency_like(s: &str, parse_result: &ParseResult) -> bool {
    // First check format: uppercase letters/numbers, 2-24 chars
    if !s.chars().all(|c| c.is_uppercase() || c.is_numeric()) || s.len() < 2 || s.len() > 24 {
        return false;
    }

    // Then verify it's a known currency in the document
    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Commodity(comm) if comm.currency.as_ref() == s => {
                return true;
            }
            Directive::Open(open) => {
                for curr in &open.currencies {
                    if curr.as_ref() == s {
                        return true;
                    }
                }
            }
            Directive::Balance(bal) if bal.amount.currency.as_ref() == s => {
                return true;
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units
                        && let Some(currency) = units.currency()
                        && currency == s
                    {
                        return true;
                    }
                    if let Some(cost) = &posting.cost
                        && let Some(currency) = &cost.currency
                        && currency.as_ref() == s
                    {
                        return true;
                    }
                    if let Some(price) = &posting.price
                        && let Some(amount) = price.amount()
                        && amount.currency.as_ref() == s
                    {
                        return true;
                    }
                }
            }
            Directive::Price(price)
                if price.currency.as_ref() == s || price.amount.currency.as_ref() == s =>
            {
                return true;
            }
            _ => {}
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_index_basic() {
        let source = "line1\nline2\nline3";
        let index = LineIndex::new(source);

        // Same tests as byte_offset_to_position
        assert_eq!(index.offset_to_position(0), (0, 0));
        assert_eq!(index.offset_to_position(5), (0, 5));
        assert_eq!(index.offset_to_position(6), (1, 0));
        assert_eq!(index.offset_to_position(10), (1, 4));
        assert_eq!(index.offset_to_position(12), (2, 0));
        assert_eq!(index.offset_to_position(17), (2, 5));

        // Line count
        assert_eq!(index.line_count(), 3);
    }

    #[test]
    fn test_line_index_empty() {
        let index = LineIndex::new("");
        assert_eq!(index.offset_to_position(0), (0, 0));
        assert_eq!(index.line_count(), 1);
    }

    #[test]
    fn test_line_index_single_line() {
        let index = LineIndex::new("hello world");
        assert_eq!(index.offset_to_position(0), (0, 0));
        assert_eq!(index.offset_to_position(5), (0, 5));
        assert_eq!(index.offset_to_position(11), (0, 11));
        assert_eq!(index.line_count(), 1);
    }

    #[test]
    fn test_line_index_trailing_newline() {
        let source = "line1\nline2\n";
        let index = LineIndex::new(source);
        assert_eq!(index.offset_to_position(11), (1, 5));
        assert_eq!(index.offset_to_position(12), (2, 0)); // Empty line 3
        assert_eq!(index.line_count(), 3);
    }

    #[test]
    fn test_line_index_position_to_offset() {
        let source = "line1\nline2\nline3";
        let index = LineIndex::new(source);

        assert_eq!(index.position_to_offset(0, 0), Some(0));
        assert_eq!(index.position_to_offset(0, 5), Some(5));
        assert_eq!(index.position_to_offset(1, 0), Some(6));
        assert_eq!(index.position_to_offset(1, 4), Some(10));
        assert_eq!(index.position_to_offset(2, 0), Some(12));

        // Out of bounds
        assert_eq!(index.position_to_offset(3, 0), None);
        assert_eq!(index.position_to_offset(0, 100), None);
    }

    #[test]
    fn test_line_index_matches_naive() {
        // Verify LineIndex matches the naive implementation
        let source = "2024-01-01 open Assets:Bank USD\n2024-01-15 * \"Coffee\"\n  Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let index = LineIndex::new(source);

        for offset in 0..source.len() {
            let naive = byte_offset_to_position(source, offset);
            let indexed = index.offset_to_position(offset);
            assert_eq!(naive, indexed, "Mismatch at offset {}", offset);
        }
    }

    #[test]
    fn test_byte_offset_to_position() {
        let source = "line1\nline2\nline3";
        assert_eq!(byte_offset_to_position(source, 0), (0, 0));
        assert_eq!(byte_offset_to_position(source, 5), (0, 5));
        assert_eq!(byte_offset_to_position(source, 6), (1, 0));
        assert_eq!(byte_offset_to_position(source, 10), (1, 4));
    }

    #[test]
    fn test_get_word_at_position() {
        let line = "  Assets:Bank  -100.00 USD";

        // At "Assets:Bank"
        let result = get_word_at_position(line, 5);
        assert!(result.is_some());
        let (word, start, end) = result.unwrap();
        assert_eq!(word, "Assets:Bank");
        assert_eq!(start, 2);
        assert_eq!(end, 13);

        // At "USD"
        let result = get_word_at_position(line, 24);
        assert!(result.is_some());
        let (word, _, _) = result.unwrap();
        assert_eq!(word, "USD");
    }

    #[test]
    fn test_is_account_like() {
        assert!(is_account_like("Assets:Bank"));
        assert!(is_account_like("Expenses:Food:Groceries"));
        assert!(!is_account_like("USD"));
        assert!(!is_account_like("Bank"));
        assert!(!is_account_like("Random:Thing"));
    }

    #[test]
    fn test_is_account_type() {
        assert!(is_account_type("Assets"));
        assert!(is_account_type("Liabilities"));
        assert!(is_account_type("Income"));
        assert!(!is_account_type("Bank"));
        assert!(!is_account_type("assets"));
    }

    #[test]
    fn test_is_currency_like_simple() {
        assert!(is_currency_like_simple("USD"));
        assert!(is_currency_like_simple("EUR"));
        assert!(is_currency_like_simple("BTC"));
        assert!(!is_currency_like_simple("usd"));
        assert!(!is_currency_like_simple("U"));
        assert!(!is_currency_like_simple("TOOLONGCURRENCY"));
    }

    #[test]
    fn test_is_word_char() {
        assert!(is_word_char('a'));
        assert!(is_word_char('Z'));
        assert!(is_word_char('0'));
        assert!(is_word_char(':'));
        assert!(is_word_char('-'));
        assert!(is_word_char('_'));
        assert!(!is_word_char(' '));
        assert!(!is_word_char('"'));
    }
}
