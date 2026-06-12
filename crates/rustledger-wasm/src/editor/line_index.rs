//! Line index and editor cache for efficient position lookups.

use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use super::helpers::{
    extract_accounts, extract_currencies, extract_links, extract_payees, extract_tags,
};

/// Cached data for editor features to avoid repeated extraction.
///
/// This is built once when a `ParsedLedger` is created and reused for all
/// completion, hover, and other editor requests.
#[derive(Debug, Clone)]
pub struct EditorCache {
    /// All unique account names in the document.
    pub accounts: Vec<String>,
    /// All unique currencies in the document.
    pub currencies: Vec<String>,
    /// All unique payees in the document.
    pub payees: Vec<String>,
    /// All unique tags in the document (without the leading `#`).
    pub tags: Vec<String>,
    /// All unique links in the document (without the leading `^`).
    pub links: Vec<String>,
    /// Line index for efficient offset-to-position conversion.
    pub line_index: LineIndex,
}

impl EditorCache {
    /// Build the editor cache from source and parse result.
    pub fn new(source: &str, parse_result: &ParseResult) -> Self {
        Self {
            accounts: extract_accounts(parse_result),
            currencies: extract_currencies(parse_result),
            payees: extract_payees(parse_result),
            tags: extract_tags(parse_result),
            links: extract_links(parse_result),
            line_index: LineIndex::new(source),
        }
    }

    /// Build a completions-only editor cache from booked directives.
    ///
    /// This provides account, currency, and payee data for completions
    /// on multi-file ledgers where raw parse results aren't available.
    /// The `LineIndex` is empty since position-based features aren't supported.
    pub fn from_directives(directives: &[Directive]) -> Self {
        Self {
            accounts: rustledger_core::extract_accounts(directives),
            currencies: rustledger_core::extract_currencies(directives),
            payees: rustledger_core::extract_payees(directives),
            tags: rustledger_core::extract_tags(directives),
            links: rustledger_core::extract_links(directives),
            line_index: LineIndex::empty(),
        }
    }
}

/// Line index for efficient offset-to-position conversion.
///
/// Building the index is O(n), but lookups are O(log(lines)).
#[derive(Debug, Clone)]
pub struct LineIndex {
    /// Byte offset of the start of each line.
    line_starts: Vec<usize>,
    /// Total length of the source.
    len: usize,
}

impl LineIndex {
    /// Build a line index from source text.
    /// Create an empty line index (for multi-file where position lookups aren't used).
    pub fn empty() -> Self {
        Self {
            line_starts: vec![0],
            len: 0,
        }
    }

    pub fn new(source: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, ch) in source.char_indices() {
            if ch == '\n' {
                line_starts.push(i + 1);
            }
        }
        Self {
            line_starts,
            len: source.len(),
        }
    }

    /// Convert a byte offset to (line, column) position (0-based).
    pub fn offset_to_position(&self, offset: usize) -> (u32, u32) {
        let offset = offset.min(self.len);
        let line = match self.line_starts.binary_search(&offset) {
            Ok(line) => line,
            Err(line) => line.saturating_sub(1),
        };
        let line_start = self.line_starts[line];
        let col = offset - line_start;
        (line as u32, col as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_index_empty_source() {
        let index = LineIndex::new("");
        let (line, col) = index.offset_to_position(0);
        assert_eq!(line, 0);
        assert_eq!(col, 0);
    }

    #[test]
    fn test_line_index_single_line() {
        let source = "hello world";
        let index = LineIndex::new(source);

        let (line, col) = index.offset_to_position(0);
        assert_eq!(line, 0);
        assert_eq!(col, 0);

        let (line, col) = index.offset_to_position(6);
        assert_eq!(line, 0);
        assert_eq!(col, 6);
    }

    #[test]
    fn test_line_index_multiple_lines() {
        let source = "line1\nline2\nline3";
        let index = LineIndex::new(source);

        // Start of line 0
        let (line, col) = index.offset_to_position(0);
        assert_eq!(line, 0);
        assert_eq!(col, 0);

        // Start of line 1 (after first newline)
        let (line, col) = index.offset_to_position(6);
        assert_eq!(line, 1);
        assert_eq!(col, 0);

        // Start of line 2
        let (line, col) = index.offset_to_position(12);
        assert_eq!(line, 2);
        assert_eq!(col, 0);

        // Middle of line 2
        let (line, col) = index.offset_to_position(15);
        assert_eq!(line, 2);
        assert_eq!(col, 3);
    }

    #[test]
    fn test_line_index_beyond_length() {
        let source = "hello";
        let index = LineIndex::new(source);

        // Beyond source length should clamp
        let (line, col) = index.offset_to_position(1000);
        assert_eq!(line, 0);
        assert_eq!(col, 5);
    }
}
