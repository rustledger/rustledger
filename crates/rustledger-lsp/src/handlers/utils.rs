//! Shared utility functions for LSP handlers.
//!
//! This module contains common utilities used across multiple handlers,
//! including position conversion, word extraction, and type checking.

use lsp_types::{FormattingOptions, Position};
use rustledger_core::FormatConfig;
use rustledger_parser::ParseResult;

/// Resolve the `FormatConfig` the LSP server uses for a given request.
///
/// Today both `textDocument/formatting` (which has client-supplied
/// `FormattingOptions`) and the `rledger.alignAmounts`
/// `workspace/executeCommand` (which does NOT — the LSP protocol
/// doesn't pass formatting preferences with commands) come through
/// this single function. That keeps the two paths producing identical
/// edits even though their inputs differ.
///
/// When the LSP server gains real config plumbing (server-wide
/// settings via initializationOptions, or per-document settings via
/// `workspace/configuration`), update this one function: derive the
/// [`rustledger_core::Alignment`] / `indent` from the client `tab_size`,
/// `insert_spaces`, and any alignment-column extension; for the
/// executeCommand path (`opts == None`), fall back to the server-wide
/// configured value rather than `FormatConfig::default()`. Both call
/// sites then benefit automatically.
#[must_use]
pub fn document_format_config(_opts: Option<&FormattingOptions>) -> FormatConfig {
    // Intentionally ignores the supplied options for now: the LSP
    // server has no config layer yet, so honoring `tab_size` /
    // `insert_spaces` would mean the executeCommand path (which
    // can't see them) diverged from `textDocument/formatting` for
    // no upside. Wire both at once when the config layer lands.
    FormatConfig::default()
}

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

    /// Get the text of a single line (0-indexed), excluding the
    /// terminating newline. Returns None if `line` is out of bounds.
    ///
    /// Cheaper than `source.lines().collect::<Vec<_>>()` for handlers
    /// that only need a few specific lines.
    pub fn line_text<'a>(&self, source: &'a str, line: u32) -> Option<&'a str> {
        let line = line as usize;
        let start = *self.line_starts.get(line)?;
        let end = self.line_starts.get(line + 1).copied().unwrap_or(self.len);
        // `start..end` includes any trailing `\n` (and `\r` if CRLF);
        // strip both so the returned slice mirrors `str::lines()`.
        Some(
            source
                .get(start..end)?
                .trim_end_matches('\n')
                .trim_end_matches('\r'),
        )
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

/// Convert a byte offset in `source` to an LSP [`Position`]
/// (`character` is UTF-16 code units per LSP 3.17 default encoding).
///
/// Convenience wrapper that builds a [`ropey::Rope`] for the conversion;
/// callers doing multiple conversions on the same string should use
/// [`rope_byte_to_lsp_position`] instead and share the rope.
#[must_use]
pub fn byte_to_lsp_position(source: &str, byte: usize) -> Position {
    let rope = ropey::Rope::from_str(source);
    rope_byte_to_lsp_position(&rope, byte)
}

/// Convert a byte offset to an LSP [`Position`] using a pre-built
/// [`ropey::Rope`]. The hot-path variant for handlers that do many
/// conversions per request (formatting, range formatting).
#[must_use]
pub fn rope_byte_to_lsp_position(rope: &ropey::Rope, byte: usize) -> Position {
    let byte = byte.min(rope.len_bytes());
    let line = rope.byte_to_line(byte);
    let line_start_byte = rope.line_to_byte(line);
    let char_at = rope.byte_to_char(byte);
    let line_start_char = rope.byte_to_char(line_start_byte);
    let character = rope.char_to_utf16_cu(char_at) - rope.char_to_utf16_cu(line_start_char);
    Position::new(line as u32, character as u32)
}

/// Convert an LSP [`Position`] (line, UTF-16 character) to a byte offset
/// in `source`. Inverse of [`byte_to_lsp_position`].
///
/// Convenience wrapper that builds a [`ropey::Rope`]. Callers doing
/// multiple conversions should use [`rope_lsp_position_to_byte`].
#[must_use]
pub fn lsp_position_to_byte(source: &str, pos: Position) -> usize {
    let rope = ropey::Rope::from_str(source);
    rope_lsp_position_to_byte(&rope, pos)
}

/// Convert an LSP [`Position`] to a byte offset using a pre-built
/// [`ropey::Rope`].
///
/// Per the LSP spec a position past the last line (line == line_count,
/// character == 0) is the end-of-document position; this function
/// returns `rope.len_bytes()` in that case. Within-document positions
/// clamp the character field to the end of the addressed line so we
/// never cross a `\n`.
#[must_use]
pub fn rope_lsp_position_to_byte(rope: &ropey::Rope, pos: Position) -> usize {
    let line_count = rope.len_lines();
    if line_count == 0 {
        return 0;
    }
    let pos_line = pos.line as usize;
    // EOF position: line == line_count, character == 0 means
    // "end of document" per LSP spec; clamp to len_bytes.
    if pos_line >= line_count {
        return rope.len_bytes();
    }
    let line_start_byte = rope.line_to_byte(pos_line);
    let line_start_char = rope.byte_to_char(line_start_byte);
    let line_start_utf16 = rope.char_to_utf16_cu(line_start_char);

    let line_end_byte = if pos_line + 1 < line_count {
        rope.line_to_byte(pos_line + 1).saturating_sub(1)
    } else {
        rope.len_bytes()
    };
    let line_end_char = rope.byte_to_char(line_end_byte);
    let line_end_utf16 = rope.char_to_utf16_cu(line_end_char);

    let target_utf16 = line_start_utf16 + pos.character as usize;
    let clamped_utf16 = target_utf16.min(line_end_utf16);
    let char_idx = rope.utf16_cu_to_char(clamped_utf16);
    rope.char_to_byte(char_idx)
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

/// Spans of the actual *declared* currency token in each
/// `Commodity` directive — exactly one per Commodity directive,
/// namely the first `Currency` token within that directive's
/// source span.
///
/// Used to disambiguate "declaration" from "use" in the LSP
/// references and document-highlight handlers. A naive
/// "occurrence span is contained within a Commodity directive
/// span" check is wrong because Commodity directives can carry
/// metadata whose values tokenize as `Currency` or `Amount`
/// (e.g. `2024-01-01 commodity USD\n  alias: EUR` — `EUR` here
/// is a metadata reference, not a declaration). The first
/// currency within each Commodity span is unambiguously the
/// declared one because the parser is strictly forward-advancing
/// and the declared currency is parsed before the indented
/// metadata block.
///
/// Returns a `HashSet` so callers can ask "is this occurrence a
/// declaration?" in O(1).
#[must_use]
pub fn commodity_declaration_spans(
    parse_result: &ParseResult,
) -> std::collections::HashSet<rustledger_parser::Span> {
    parse_result
        .directives
        .iter()
        .filter_map(|d| {
            if !matches!(&d.value, rustledger_core::Directive::Commodity(_)) {
                return None;
            }
            parse_result
                .currency_occurrences
                .iter()
                .find(|o| o.span.start >= d.span.start && o.span.end <= d.span.end)
                .map(|o| o.span)
        })
        .collect()
}

/// Check if a string looks like a currency, validating against known currencies.
///
/// Validates the format (uppercase-and-digits, 2-24 chars) and then
/// confirms the string actually appears as a parsed `Currency` token
/// in the document by looking it up in `parse_result.currency_occurrences`.
///
/// The previous implementation manually walked the AST testing each
/// position that can carry a currency (Commodity.currency,
/// Open.currencies, Balance.amount, Posting.units / cost / price,
/// Price directive). That had two problems:
///
/// 1. Any position the walk forgot — or any future directive type
///    that carries a currency — would silently be excluded, and
///    rename / references / document-highlight would refuse to fire
///    on a real currency only mentioned there.
/// 2. Code duplication: the parser already records every `Currency`
///    token in `currency_occurrences`; the walk was a parallel and
///    necessarily-incomplete reimplementation.
///
/// Consulting the parser's index makes the check exact by
/// construction and shrinks the function from ~50 lines to ~5.
pub fn is_currency_like(s: &str, parse_result: &ParseResult) -> bool {
    if !s.chars().all(|c| c.is_uppercase() || c.is_numeric()) || s.len() < 2 || s.len() > 24 {
        return false;
    }
    parse_result
        .currency_occurrences
        .iter()
        .any(|occ| occ.value == s)
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

    /// `is_currency_like` validates format AND confirms the string
    /// actually appears as a parsed `Currency` token in the
    /// document. This test pins both behaviors.
    ///
    /// Includes a coverage case for the latent gap the previous
    /// manual-AST-walk implementation had: a currency mentioned
    /// only in a `Price` directive returns true. (Whether the old
    /// walk happened to cover `Price` doesn't matter for the new
    /// implementation — it queries `currency_occurrences`, which
    /// is exhaustive by construction.)
    #[test]
    fn test_is_currency_like() {
        use rustledger_parser::parse;

        let source = r#"2024-01-01 commodity USD
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food  5.00 USD
2024-01-20 price GBP  1.27 USD
"#;
        let parse_result = parse(source);

        // Format check: must be uppercase/digits, length 2-24.
        assert!(
            !is_currency_like("usd", &parse_result),
            "lowercase rejected"
        );
        assert!(!is_currency_like("U", &parse_result), "too short rejected");

        // Format-valid but not present in document.
        assert!(
            !is_currency_like("XYZ", &parse_result),
            "unknown currency rejected"
        );

        // Format-valid and present as Currency token.
        assert!(is_currency_like("USD", &parse_result));

        // Currency that appears ONLY in a Price directive (the
        // latent gap of the previous manual AST walk if it had
        // missed Price). `currency_occurrences` is exhaustive.
        assert!(is_currency_like("GBP", &parse_result));
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
