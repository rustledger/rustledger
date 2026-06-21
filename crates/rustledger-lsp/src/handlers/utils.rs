//! Shared utility functions for LSP handlers.
//!
//! This module contains common utilities used across multiple handlers,
//! including position conversion, word extraction, and type checking.

use lsp_types::{Position, Range};
use rustledger_parser::ParseResult;

/// Trim a directive span's end offset back over trailing whitespace.
///
/// A directive's parser span runs up to the *start of the next directive*, so
/// it swallows any trailing blank lines. Mapping that raw end to a `Position`
/// makes ranges (folding, document symbols, …) overshoot into the following
/// directive. This returns the offset just past the directive's last
/// non-whitespace byte, so the range ends at the directive's real content.
pub(crate) fn trim_span_end(source: &str, end: usize) -> usize {
    let clamped = end.min(source.len());
    source
        .get(..clamped)
        .map_or(clamped, |s| s.trim_end().len())
}

/// Whether two LSP `Range`s overlap, using LSP half-open semantics
/// (`Range.end` is EXCLUSIVE per the spec).
///
/// Two ranges where `a.end == b.start` are adjacent, NOT overlapping
/// — hence the `<=` (rather than strict `<`). A zero-width range
/// (cursor position) at exactly `r.end` is past `r`, not inside it;
/// a zero-width range at exactly `r.start` IS inside `r`.
///
/// Single canonical implementation. Previously two private copies
/// existed (`handlers/import.rs` and `handlers/code_actions.rs`) with
/// opposite semantics — one strict-`<`, one `<=`. Hoisting here
/// removes the inconsistency.
#[must_use]
pub fn ranges_overlap(a: Range, b: Range) -> bool {
    !(a.end <= b.start || b.end <= a.start)
}

/// LSP position-encoding negotiated with the client at initialization.
///
/// Per LSP 3.17, a client advertises which encodings it accepts via
/// `InitializeParams.capabilities.general.positionEncodings`. The
/// server replies with the encoding it will use; clients that don't
/// negotiate get the default (UTF-16). Modern editors (VS Code,
/// neovim, helix, zed) negotiate UTF-8 because that's cheaper than
/// re-encoding every diagnostic position.
///
/// All position emission paths in the LSP layer should consult this
/// type — emitting LSP positions in a different encoding than the
/// negotiated one will misalign on non-ASCII content. Today most
/// handlers in this crate emit byte (UTF-8) offsets via
/// [`LineIndex::offset_to_position`]; that works under UTF-8
/// negotiation but is wrong for UTF-16-only clients. See
/// `server.rs::run` for the negotiation site and `MainLoopState`
/// for the storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PositionEncoding {
    /// UTF-8 byte offsets. The native unit of the underlying source
    /// representation; preferred by modern editors.
    Utf8,
    /// UTF-16 code units. The LSP 3.17 default for clients that
    /// don't negotiate.
    Utf16,
}

impl PositionEncoding {
    /// Decide the negotiated encoding from a `ServerCapabilities`-
    /// shaped value. `Some(UTF8)` → UTF-8; `None` → UTF-16 (the
    /// LSP default).
    #[must_use]
    pub fn from_negotiated(negotiated: Option<&lsp_types::PositionEncodingKind>) -> Self {
        match negotiated {
            Some(kind) if *kind == lsp_types::PositionEncodingKind::UTF8 => Self::Utf8,
            _ => Self::Utf16,
        }
    }
}

/// A line index for efficient offset-to-position conversion, encoding-aware.
///
/// Borrows the source via `&'a str` — the index does NOT allocate a copy.
/// Construction is O(n) for the `line_starts` table walk; subsequent
/// lookups are O(log lines) for line resolution. Column resolution
/// under UTF-16 encoding is also O(log n) via a lazily-built
/// [`ropey::Rope`] that's only paid for under UTF-16 negotiation;
/// under UTF-8 encoding the column math is constant time after line
/// resolution (the column equals the byte delta from line start).
///
/// **Architecture (round-18).** Previous iterations alternated
/// between full-rope-only (O(log n) lookups but O(n) construction
/// for both encodings), no-rope-only (O(line_length) UTF-16 lookups
/// with no rope cost), and owned-Arc-source (gratuitous O(n) clone).
/// This design picks the right cost for each path: UTF-8 paths pay
/// no rope cost; UTF-16 paths pay one rope construction per index
/// and get O(log n) lookups.
///
/// **Line-break semantics.** Only `\n` is treated as a line break,
/// matching the LSP-spec-implied convention that `Position.line` is
/// indexed by `\n` boundaries. Bare `\r` (legacy macOS line endings)
/// is NOT a line break. CRLF is recognized via the `\r` being part
/// of the preceding line content (trimmed in `position_to_offset`
/// and `line_text`).
///
/// # Example
///
/// ```ignore
/// let index = LineIndex::new(source, PositionEncoding::Utf16);
/// let (line, col) = index.offset_to_position(offset);
/// ```
#[derive(Debug)]
pub struct LineIndex<'a> {
    /// Borrowed source — the index lives only as long as the source.
    source: &'a str,
    /// Byte offset of the start of each line (including line 0 at offset 0).
    line_starts: Vec<usize>,
    /// Negotiated LSP position encoding.
    encoding: PositionEncoding,
    /// Lazily-built rope used ONLY for UTF-16 column conversions.
    /// `None` until the first UTF-16-encoded lookup; `None` forever
    /// under [`PositionEncoding::Utf8`]. Single-threaded interior
    /// mutability via [`std::cell::OnceCell`] — handlers build a
    /// LineIndex per request, no cross-thread sharing.
    utf16_rope: std::cell::OnceCell<ropey::Rope>,
}

impl<'a> LineIndex<'a> {
    /// Build a line index from source text.
    ///
    /// O(n) for the line-starts table walk. The UTF-16 rope is NOT
    /// built here — it's deferred to the first UTF-16 column lookup
    /// via `utf16_rope`'s [`std::cell::OnceCell`]. Under UTF-8
    /// encoding the rope is never built at all.
    ///
    /// `encoding` is the LSP position encoding negotiated with the
    /// client (see [`PositionEncoding`]). Pass
    /// [`PositionEncoding::Utf16`] for the LSP spec default, or the
    /// value stored on the main-loop state for the negotiated wire
    /// encoding.
    pub fn new(source: &'a str, encoding: PositionEncoding) -> Self {
        let mut line_starts = vec![0]; // Line 0 starts at offset 0

        for (i, ch) in source.char_indices() {
            if ch == '\n' {
                line_starts.push(i + 1); // Next line starts after the newline
            }
        }

        Self {
            source,
            line_starts,
            encoding,
            utf16_rope: std::cell::OnceCell::new(),
        }
    }

    /// Get or build the UTF-16 rope on demand.
    fn rope(&self) -> &ropey::Rope {
        self.utf16_rope
            .get_or_init(|| ropey::Rope::from_str(self.source))
    }

    /// Locate the line containing `byte` via binary search over
    /// `line_starts`. Saturating-sub on the `Err` branch handles a
    /// byte that falls strictly between line starts (the common
    /// case).
    fn byte_to_line(&self, byte: usize) -> usize {
        match self.line_starts.binary_search(&byte) {
            Ok(line) => line,
            Err(line) => line.saturating_sub(1),
        }
    }

    /// Convert a byte offset to a (line, column) position (0-based).
    ///
    /// `column` is in the negotiated encoding — UTF-8 byte offsets
    /// under [`PositionEncoding::Utf8`], UTF-16 code units under
    /// [`PositionEncoding::Utf16`]. UTF-8 is O(log lines) total;
    /// UTF-16 is O(log lines) line resolution + O(log n) rope
    /// conversion (after a one-time O(n) rope construction).
    pub fn offset_to_position(&self, offset: usize) -> (u32, u32) {
        let offset = offset.min(self.source.len());
        let line = self.byte_to_line(offset);
        let line_start = self.line_starts[line];
        let col: u32 = match self.encoding {
            PositionEncoding::Utf8 => (offset - line_start) as u32,
            PositionEncoding::Utf16 => {
                let rope = self.rope();
                let char_at = rope.byte_to_char(offset);
                let line_start_char = rope.byte_to_char(line_start);
                (rope.char_to_utf16_cu(char_at) - rope.char_to_utf16_cu(line_start_char)) as u32
            }
        };
        (line as u32, col)
    }

    /// Convert a (line, column) position to a byte offset.
    ///
    /// `col` is interpreted in the negotiated encoding (UTF-8 bytes
    /// vs. UTF-16 code units). Returns `None` when:
    /// - `line` is past the last line in the source, OR
    /// - `col` overshoots the line's content in the negotiated
    ///   encoding, OR
    /// - `col` lands inside a surrogate pair (UTF-16) or off a
    ///   UTF-8 char boundary (UTF-8).
    ///
    /// The strict-overshoot contract is symmetric across encodings
    /// so callers can rely on `None` as a uniform "malformed client
    /// position" signal regardless of negotiation.
    pub fn position_to_offset(&self, line: u32, col: u32) -> Option<usize> {
        let line_usize = line as usize;
        if line_usize >= self.line_starts.len() {
            return None;
        }
        let line_start = self.line_starts[line_usize];
        let line_end_raw = self
            .line_starts
            .get(line_usize + 1)
            .copied()
            .unwrap_or(self.source.len());
        // Exclude only the trailing '\n' from the addressable-content
        // range. The '\r' under CRLF is treated as line content (it
        // sits inside the byte range `source.split('\n')` yields for
        // the line), so handlers can address positions immediately
        // before the `\n`. Strict `\n`-only stripping mirrors the
        // `\n`-only line-break policy enforced in `line_starts`.
        let line_text_end = {
            let bytes = self.source.as_bytes();
            if line_end_raw > line_start && bytes.get(line_end_raw - 1) == Some(&b'\n') {
                line_end_raw - 1
            } else {
                line_end_raw
            }
        };
        match self.encoding {
            PositionEncoding::Utf8 => {
                let offset = line_start.checked_add(col as usize)?;
                if offset > line_text_end {
                    return None;
                }
                if offset < self.source.len() && !self.source.is_char_boundary(offset) {
                    return None;
                }
                Some(offset)
            }
            PositionEncoding::Utf16 => {
                // Route through ropey for O(log n) lookup. The rope
                // helper translates a UTF-16 code-unit offset into a
                // byte offset; we still validate the result lies
                // within the addressed line's content (strict
                // overshoot returns None).
                let rope = self.rope();
                let line_start_char = rope.byte_to_char(line_start);
                let line_start_utf16 = rope.char_to_utf16_cu(line_start_char);
                let line_text_end_char = rope.byte_to_char(line_text_end);
                let line_text_end_utf16 = rope.char_to_utf16_cu(line_text_end_char);
                let target_utf16 = line_start_utf16.checked_add(col as usize)?;
                if target_utf16 > line_text_end_utf16 {
                    return None;
                }
                let char_idx = rope.utf16_cu_to_char(target_utf16);
                // Round-trip check: if `col` landed in a surrogate
                // pair, utf16_cu_to_char snaps to the surrounding
                // char, and re-converting gives a different code-
                // unit count. That's the malformed-input signal.
                if rope.char_to_utf16_cu(char_idx) != target_utf16 {
                    return None;
                }
                Some(rope.char_to_byte(char_idx))
            }
        }
    }

    /// Get the number of lines in the source.
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    /// Byte offset of the start of `line` in the source. Returns
    /// `None` if `line` is past the last line.
    #[must_use]
    pub fn line_start_byte(&self, line: u32) -> Option<usize> {
        self.line_starts.get(line as usize).copied()
    }

    /// Convert a `(line, byte_offset_within_line)` pair to an LSP
    /// `Position` in the negotiated encoding.
    ///
    /// The common pattern this serves: a handler calls
    /// `line.find(needle)` to locate a substring, getting a BYTE
    /// offset within the line. Emitting that offset directly as a
    /// `Position::character` is wrong under UTF-16 negotiation on
    /// non-ASCII content (round-19 reviewer-flagged hazard across
    /// references / rename / document_highlight / linked_editing /
    /// call_hierarchy / type_hierarchy / selection_range). This
    /// helper routes through the index's encoding-aware
    /// `offset_to_position` so the emitted `Position.character` is
    /// correct under both negotiations.
    ///
    /// Returns `None` if:
    /// - `line` is past the last line, OR
    /// - `byte_in_line` would overflow `usize` when added to the
    ///   line start, OR
    /// - `byte_in_line` strictly overshoots the line's addressable
    ///   content (i.e. exceeds `line_text(line).len()`). The
    ///   strict-overshoot reject mirrors `position_to_offset`'s
    ///   contract: silently routing into the next line via
    ///   `offset_to_position`'s `min(source.len())` clamp would
    ///   hide caller bugs where the byte offset came from a stale
    ///   cached value rather than a fresh `line.find()`.
    #[must_use]
    pub fn byte_in_line_to_position(&self, line: u32, byte_in_line: usize) -> Option<Position> {
        let line_start = self.line_start_byte(line)?;
        let line_text = self.line_text(line)?;
        if byte_in_line > line_text.len() {
            return None;
        }
        let abs_byte = line_start.checked_add(byte_in_line)?;
        let (l, c) = self.offset_to_position(abs_byte);
        Some(Position::new(l, c))
    }

    /// Negotiated LSP position encoding the index was built with.
    #[must_use]
    pub fn encoding(&self) -> PositionEncoding {
        self.encoding
    }

    /// Get the text of a single line (0-indexed), excluding the
    /// terminating newline. Returns None if `line` is out of bounds.
    ///
    /// Borrows from the index's source — same lifetime as the
    /// LineIndex itself.
    pub fn line_text(&self, line: u32) -> Option<&'a str> {
        let line = line as usize;
        let start = *self.line_starts.get(line)?;
        let end = self
            .line_starts
            .get(line + 1)
            .copied()
            .unwrap_or(self.source.len());
        // `start..end` includes any trailing `\n` (and `\r` if CRLF);
        // strip both so the returned slice mirrors `str::lines()`.
        Some(
            self.source
                .get(start..end)?
                .trim_end_matches('\n')
                .trim_end_matches('\r'),
        )
    }
}

/// Get the word at a given column position in a line, interpreting
/// `col` in the negotiated LSP position encoding.
///
/// Returns the word and its start/end columns in the **same encoding
/// as `col`** — so callers can splice the returned `(start, end)`
/// directly into LSP `Position` / `Range` values without further
/// conversion. Words include alphanumeric characters, colons,
/// hyphens, and underscores.
///
/// Pre-round-17 this helper treated `col` as a raw char index, which
/// is neither UTF-8 bytes nor UTF-16 code units. The result misfired
/// on any non-ASCII line under EITHER negotiated encoding, breaking
/// rename / references / document-highlight / linked-editing on
/// Cyrillic / CJK / emoji content.
pub fn get_word_at_position(
    line: &str,
    col: usize,
    encoding: PositionEncoding,
) -> Option<(String, usize, usize)> {
    // Walk the line accumulating (byte_offset, char_count, units_seen)
    // tuples so we can map `col` (in the negotiated encoding) to a
    // char index. Then find the word boundary at that char index and
    // map the boundary back to the same encoding so the returned
    // columns are wire-ready.
    let chars: Vec<char> = line.chars().collect();

    // Mapping from char index → encoded col, in O(line length).
    let encoded_col_at_char = |char_idx: usize| -> usize {
        chars
            .iter()
            .take(char_idx)
            .map(|c| match encoding {
                PositionEncoding::Utf8 => c.len_utf8(),
                PositionEncoding::Utf16 => c.len_utf16(),
            })
            .sum()
    };

    // Mapping `col` → char index. Returns None if `col` lands inside
    // a multi-byte char (UTF-8) or surrogate pair (UTF-16).
    let mut acc = 0usize;
    let mut cursor_char_idx = 0usize;
    for (i, c) in chars.iter().enumerate() {
        if acc == col {
            cursor_char_idx = i;
            break;
        }
        let u = match encoding {
            PositionEncoding::Utf8 => c.len_utf8(),
            PositionEncoding::Utf16 => c.len_utf16(),
        };
        if acc + u > col {
            // `col` lands inside the char `c`.
            return None;
        }
        acc += u;
        cursor_char_idx = i + 1;
    }
    if acc < col {
        // `col` past end of line.
        return None;
    }

    let mut start = cursor_char_idx;
    while start > 0 && is_word_char(chars[start - 1]) {
        start -= 1;
    }
    let mut end = cursor_char_idx;
    while end < chars.len() && is_word_char(chars[end]) {
        end += 1;
    }
    if start == end {
        return None;
    }

    let word: String = chars[start..end].iter().collect();
    Some((word, encoded_col_at_char(start), encoded_col_at_char(end)))
}

/// Get the word at a position in a source document, interpreting
/// `position.character` in the negotiated encoding.
///
/// Convenience wrapper that extracts the addressed line and delegates
/// to [`get_word_at_position`]. Returns only the word text (not its
/// columns) since most callers (hover, goto-definition) don't need
/// the column values.
pub fn get_word_at_source_position(
    source: &str,
    position: Position,
    encoding: PositionEncoding,
) -> Option<String> {
    let line = source.lines().nth(position.line as usize)?;
    let (word, _, _) = get_word_at_position(line, position.character as usize, encoding)?;
    Some(word)
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

/// Check if a string is a standard root account type.
#[must_use]
pub fn is_account_type(s: &str) -> bool {
    rustledger_core::ACCOUNT_TYPES.contains(&s)
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

/// The spans of every `Open` directive's declared account token.
///
/// Account references in beancount come from six directive kinds
/// (`open` / `close` / `balance` / `pad` / `note` / `document`)
/// PLUS posting accounts in transactions PLUS ACCOUNT-typed
/// metadata values. Of those, the two "declaration-like"
/// directives — the ones that establish or end the account's
/// lifecycle — are `open` and `close`. Both surface as `WRITE`
/// in document-highlight and both honor the
/// `Find References > Include Declaration` toggle. The remaining
/// four directive shapes + posting accounts + ACCOUNT-typed
/// metadata are all references (`READ`).
///
/// **Pre-#1262-phase-5.5 behavior, retained.** The legacy
/// substring-search implementation marked both `Open` AND `Close`
/// as `WRITE`. The phase-5.5 rewrite preserves that policy; only
/// the underlying mechanism changed from per-directive substring
/// search to per-token CST classification.
///
/// **Why we walk the CST instead of the typed-AST `directives`.**
/// A directive that parses *syntactically* but whose typed
/// conversion errors — most commonly an `open` with an invalid
/// booking method (`InvalidBookingMethod`) — is dropped from
/// `parse_result.directives`, but its `ACCOUNT` token is still
/// present in `parse_result.account_occurrences` (the lexer's
/// classification is independent of typed-AST validity, per the
/// `account_occurrences` rustdoc). If we walked `directives` we
/// would silently re-classify the failed-Open's account as a
/// reference, breaking the `include_declaration: false` filter
/// exactly when the user is debugging a broken directive. The
/// CST walk sees the `OPEN_DIRECTIVE` node regardless of typed
/// conversion success.
///
/// **Performance.** O(number of CST nodes) traversal, no
/// quadratic walk over `account_occurrences`. The previous
/// implementation was O(N_opens × N_occurrences) because it
/// re-scanned the full occurrences list for each Open directive.
///
/// Returns a `HashSet` so callers can ask "is this occurrence a
/// declaration?" in O(1).
#[must_use]
pub fn account_declaration_spans(
    parse_result: &ParseResult,
) -> std::collections::HashSet<rustledger_parser::Span> {
    use rustledger_parser::SyntaxKind;
    let bom_offset: usize = if parse_result.has_leading_bom { 3 } else { 0 };
    let mut declarations = std::collections::HashSet::new();

    for node in parse_result.syntax_node().descendants() {
        let kind = node.kind();
        if kind != SyntaxKind::OPEN_DIRECTIVE && kind != SyntaxKind::CLOSE_DIRECTIVE {
            continue;
        }
        // Skip directives wrapped by error-recovery. The first
        // ACCOUNT token inside an ERROR_NODE is also excluded
        // from `account_occurrences` (per its rustdoc), so adding
        // such a span here would not match any occurrence anyway
        // — but the cleaner contract is "declarations come from
        // recognized directives only", which the parent-ancestor
        // check enforces.
        if node
            .ancestors()
            .skip(1)
            .any(|a| a.kind() == SyntaxKind::ERROR_NODE)
        {
            continue;
        }
        let Some(account_token) = node
            .descendants_with_tokens()
            .filter_map(|n| n.into_token())
            .find(|t| t.kind() == SyntaxKind::ACCOUNT)
        else {
            continue;
        };
        let range = account_token.text_range();
        let start = u32::from(range.start()) as usize + bom_offset;
        let end = u32::from(range.end()) as usize + bom_offset;
        declarations.insert(rustledger_parser::Span::new(start, end));
    }

    declarations
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
        let index = LineIndex::new(source, PositionEncoding::Utf8);

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
        let index = LineIndex::new("", PositionEncoding::Utf8);
        assert_eq!(index.offset_to_position(0), (0, 0));
        assert_eq!(index.line_count(), 1);
    }

    #[test]
    fn test_line_index_single_line() {
        let index = LineIndex::new("hello world", PositionEncoding::Utf8);
        assert_eq!(index.offset_to_position(0), (0, 0));
        assert_eq!(index.offset_to_position(5), (0, 5));
        assert_eq!(index.offset_to_position(11), (0, 11));
        assert_eq!(index.line_count(), 1);
    }

    #[test]
    fn test_line_index_trailing_newline() {
        let source = "line1\nline2\n";
        let index = LineIndex::new(source, PositionEncoding::Utf8);
        assert_eq!(index.offset_to_position(11), (1, 5));
        assert_eq!(index.offset_to_position(12), (2, 0)); // Empty line 3
        assert_eq!(index.line_count(), 3);
    }

    #[test]
    fn test_line_index_position_to_offset() {
        let source = "line1\nline2\nline3";
        let index = LineIndex::new(source, PositionEncoding::Utf8);

        assert_eq!(index.position_to_offset(0, 0), Some(0));
        assert_eq!(index.position_to_offset(0, 5), Some(5));
        assert_eq!(index.position_to_offset(1, 0), Some(6));
        assert_eq!(index.position_to_offset(1, 4), Some(10));
        assert_eq!(index.position_to_offset(2, 0), Some(12));

        // Out of bounds
        assert_eq!(index.position_to_offset(3, 0), None);
        assert_eq!(index.position_to_offset(0, 100), None);
    }

    /// Cross-check the indexed UTF-8 column math against a simple
    /// inline walk over the source. Both should land on the same
    /// (line, col) for every byte offset in a typical beancount
    /// fixture.
    #[test]
    fn test_line_index_utf8_matches_inline_walk() {
        let source = "2024-01-01 open Assets:Bank USD\n2024-01-15 * \"Coffee\"\n  Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let index = LineIndex::new(source, PositionEncoding::Utf8);

        for offset in 0..source.len() {
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
            let indexed = index.offset_to_position(offset);
            assert_eq!((line, col), indexed, "Mismatch at offset {}", offset);
        }
    }

    /// `position_to_offset` returns `None` symmetrically across
    /// encodings on column overshoot. Pins the round-17 fix for the
    /// reviewer-flagged divergence (UTF-8 was strict, UTF-16 silently
    /// clamped via ropey).
    #[test]
    fn test_line_index_position_to_offset_overshoot_symmetric() {
        let source = "line1\nline2\nline3";

        let utf8 = LineIndex::new(source, PositionEncoding::Utf8);
        assert_eq!(utf8.position_to_offset(0, 5), Some(5));
        assert_eq!(utf8.position_to_offset(0, 6), None);
        assert_eq!(utf8.position_to_offset(0, 100), None);

        let utf16 = LineIndex::new(source, PositionEncoding::Utf16);
        assert_eq!(utf16.position_to_offset(0, 5), Some(5));
        assert_eq!(utf16.position_to_offset(0, 6), None);
        assert_eq!(utf16.position_to_offset(0, 100), None);
    }

    /// Non-BMP scalars (emoji) take TWO UTF-16 code units (surrogate
    /// pair) but FOUR UTF-8 bytes. The encoding-aware `LineIndex`
    /// must emit different `character` values for the two encodings —
    /// this test pins both directions.
    #[test]
    fn test_line_index_utf16_columns() {
        // "💰" = U+1F4B0, 4 UTF-8 bytes, 2 UTF-16 code units.
        let source = "💰 USD";
        let after_emoji_byte = '💰'.len_utf8();

        let utf8 = LineIndex::new(source, PositionEncoding::Utf8);
        assert_eq!(utf8.offset_to_position(after_emoji_byte), (0, 4));

        let utf16 = LineIndex::new(source, PositionEncoding::Utf16);
        assert_eq!(utf16.offset_to_position(after_emoji_byte), (0, 2));

        // Inverse: a UTF-16 col=2 maps back to byte offset 4.
        assert_eq!(utf16.position_to_offset(0, 2), Some(after_emoji_byte));
        // ASCII content past the emoji: byte 8 = UTF-16 col 6.
        assert_eq!(utf16.offset_to_position(8), (0, 6));
    }

    /// Bare CR is NOT a line break — only `\n` is. Source `"a\rb"`
    /// is one line; the LineIndex emits column 2 (UTF-8) / column 2
    /// (UTF-16) for byte 2. Pre-round-18 ropey-based impls treated
    /// bare CR as a line break, which diverges from the LSP spec's
    /// implicit `\n`-only convention. Pinning this prevents an
    /// accidental ropey-revert from silently shifting positions in
    /// legacy-Mac files.
    #[test]
    fn test_line_index_bare_cr_not_a_line_break() {
        let source = "a\rb";
        let index = LineIndex::new(source, PositionEncoding::Utf8);
        assert_eq!(index.line_count(), 1);
        // Byte 2 (the 'b') is on line 0 col 2 — NOT line 1 col 0.
        assert_eq!(index.offset_to_position(2), (0, 2));
        // CRLF is still recognized as ONE line break (the '\n'), and
        // the '\r' is trimmed from the line's visible content range.
        let crlf = LineIndex::new("a\r\nb", PositionEncoding::Utf8);
        assert_eq!(crlf.line_count(), 2);
        assert_eq!(crlf.offset_to_position(3), (1, 0));
    }

    #[test]
    fn test_line_index_basic_offsets() {
        let source = "line1\nline2\nline3";
        let index = LineIndex::new(source, PositionEncoding::Utf8);
        assert_eq!(index.offset_to_position(0), (0, 0));
        assert_eq!(index.offset_to_position(5), (0, 5));
        assert_eq!(index.offset_to_position(6), (1, 0));
        assert_eq!(index.offset_to_position(10), (1, 4));
    }

    /// `byte_in_line_to_position` must reject byte offsets that
    /// strictly overshoot the addressed line's content. Pre-round-20
    /// it silently routed overshoots through `offset_to_position`'s
    /// `min(source.len())` clamp, emitting a Position pointing into
    /// the NEXT line — masking caller bugs (stale cached offsets,
    /// off-by-one in needle arithmetic) as wrong-line edits.
    #[test]
    fn test_byte_in_line_to_position_strict_overshoot() {
        let source = "abc\ndefgh\nij";
        let index = LineIndex::new(source, PositionEncoding::Utf8);

        // In-range on line 0 ("abc", len=3): 0..=3 succeed.
        assert_eq!(
            index.byte_in_line_to_position(0, 0),
            Some(Position::new(0, 0))
        );
        assert_eq!(
            index.byte_in_line_to_position(0, 3),
            Some(Position::new(0, 3))
        );
        // Overshoot line 0: 4 would have addressed line 1 col 0 under
        // the old clamp; strict reject is None.
        assert_eq!(index.byte_in_line_to_position(0, 4), None);
        assert_eq!(index.byte_in_line_to_position(0, 100), None);

        // In-range on line 1 ("defgh", len=5): 0..=5 succeed.
        assert_eq!(
            index.byte_in_line_to_position(1, 5),
            Some(Position::new(1, 5))
        );
        assert_eq!(index.byte_in_line_to_position(1, 6), None);

        // Past-last-line still None via line_text.
        assert_eq!(index.byte_in_line_to_position(99, 0), None);
    }

    #[test]
    fn test_get_word_at_position() {
        let line = "  Assets:Bank  -100.00 USD";

        // At "Assets:Bank"
        let result = get_word_at_position(line, 5, PositionEncoding::Utf8);
        assert!(result.is_some());
        let (word, start, end) = result.unwrap();
        assert_eq!(word, "Assets:Bank");
        assert_eq!(start, 2);
        assert_eq!(end, 13);

        // At "USD"
        let result = get_word_at_position(line, 24, PositionEncoding::Utf8);
        assert!(result.is_some());
        let (word, _, _) = result.unwrap();
        assert_eq!(word, "USD");
    }

    /// `get_word_at_position` returns columns in the same encoding as
    /// the input `col`. On a Cyrillic account, UTF-16 col=12 lands on
    /// the space before `USD`; the word `USD` starts at UTF-16 col=13
    /// (one Cyrillic char = 1 UTF-16 unit but 2 UTF-8 bytes, so the
    /// UTF-8 column for the same byte is larger). Pins both encodings.
    #[test]
    fn test_get_word_at_position_encoding_aware() {
        let line = "Активы:Банк USD";
        // "Активы:Банк " is 12 chars / 12 UTF-16 units / 22 UTF-8
        // bytes (each Cyrillic char is 2 UTF-8 bytes / 1 UTF-16
        // unit). "USD" starts at char 12.

        let (word, s, e) = get_word_at_position(line, 12, PositionEncoding::Utf16)
            .expect("word at UTF-16 col 12 should resolve");
        assert_eq!(word, "USD");
        assert_eq!((s, e), (12, 15));

        let (word, s, e) = get_word_at_position(line, 22, PositionEncoding::Utf8)
            .expect("word at UTF-8 col 22 should resolve");
        assert_eq!(word, "USD");
        assert_eq!((s, e), (22, 25));

        // A col that lands inside a multi-byte char under UTF-8 returns None.
        // Byte 1 is in the middle of "А" (2 bytes).
        assert!(get_word_at_position(line, 1, PositionEncoding::Utf8).is_none());
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

    /// `account_declaration_spans` includes both `Open` and `Close`
    /// header accounts (lifecycle boundaries) and excludes balance /
    /// pad / note / document / posting / ACCOUNT-typed metadata.
    #[test]
    fn account_declaration_spans_covers_open_and_close() {
        use rustledger_parser::parse;
        let source = "\
2024-01-01 open Assets:Bank USD
2024-06-15 * \"Coffee\"
  Assets:Bank  -5.00 USD
2024-08-01 balance Assets:Bank 95.00 USD
2024-12-31 close Assets:Bank
";
        let result = parse(source);
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        let decls = account_declaration_spans(&result);

        // Two declarations expected: Open header (line 0) and
        // Close header (line 4). The posting and balance are
        // references, not declarations.
        assert_eq!(decls.len(), 2, "got {decls:?}");

        // Match against `account_occurrences`: occurrences whose
        // span is in `decls` are declarations.
        let decl_occurrences: Vec<&rustledger_parser::Spanned<rustledger_core::Account>> = result
            .account_occurrences
            .iter()
            .filter(|o| decls.contains(&o.span))
            .collect();
        assert_eq!(decl_occurrences.len(), 2);
        // First decl = source byte offset of Open's Assets:Bank
        // (line 0, col 16 == byte 16); Second = Close's
        // (line 4, col 17). The exact byte math is the contract.
        let mut starts: Vec<usize> = decl_occurrences.iter().map(|o| o.span.start).collect();
        starts.sort_unstable();
        assert_eq!(
            starts[0], 16,
            "Open's Assets:Bank starts at byte 16 of the source",
        );
        // Line 4 starts after "2024-12-31 close " preceded by lines
        // 0..3. Sanity-check the offset against the source bytes
        // rather than hardcoding.
        let close_offset = source.find("close Assets:Bank").unwrap() + "close ".len();
        assert_eq!(starts[1], close_offset);
    }

    /// An `Open` directive whose typed-AST conversion fails
    /// (`InvalidBookingMethod` here) is dropped from
    /// `parse_result.directives`, but its ACCOUNT token IS in
    /// `account_occurrences` and the CST node is intact (not
    /// inside an `ERROR_NODE`). The CST walk must still classify
    /// it as a declaration. The previous typed-AST walk silently
    /// regressed in this case — `include_declaration: false`
    /// stopped filtering the open, exactly when the user is
    /// debugging a broken directive.
    #[test]
    fn account_declaration_spans_handles_failed_open_conversion() {
        use rustledger_core::Directive;
        use rustledger_parser::parse;
        // Invalid booking method - parser emits
        // `InvalidBookingMethod`, drops the Open from
        // `directives`, but keeps the CST node + ACCOUNT token.
        let source = "2024-01-01 open Assets:Bank USD \"GARBAGE\"\n";
        let result = parse(source);
        // The directive was dropped (no Open in typed AST):
        assert!(
            !result
                .directives
                .iter()
                .any(|d| matches!(&d.value, Directive::Open(_))),
            "expected the Open to be dropped from directives, got {:?}",
            result.directives
        );
        // But the ACCOUNT token IS in occurrences:
        let has_account = result
            .account_occurrences
            .iter()
            .any(|o| o.value.as_str() == "Assets:Bank");
        assert!(has_account, "{:?}", result.account_occurrences);
        // And the CST walk classifies it as a declaration.
        let decls = account_declaration_spans(&result);
        assert_eq!(
            decls.len(),
            1,
            "expected the failed-Open's ACCOUNT to still be a declaration; got {decls:?}",
        );
    }

    /// An ACCOUNT-typed metadata value inside an `Open` directive
    /// (e.g. `payee_account: Assets:Other`) tokenizes as ACCOUNT
    /// at the lexer level, BUT it is not the directive header
    /// account. The helper takes the FIRST ACCOUNT token in the
    /// directive's source span, which is always the header
    /// (parser is forward-advancing; the metadata block is parsed
    /// after the header). This test pins that contract.
    #[test]
    fn account_declaration_spans_skips_metadata_account_value() {
        use rustledger_parser::parse;
        let source = "\
2024-01-01 open Assets:Bank USD
  payee_account: Assets:Other
";
        let result = parse(source);
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        let decls = account_declaration_spans(&result);
        assert_eq!(decls.len(), 1, "got {decls:?}");

        // The single declaration is the header (Assets:Bank), NOT
        // the metadata value (Assets:Other). Find the occurrence
        // whose span is in `decls` and assert its value.
        let decl = result
            .account_occurrences
            .iter()
            .find(|o| decls.contains(&o.span))
            .expect("at least one ACCOUNT occurrence is a declaration");
        assert_eq!(
            decl.value.as_str(),
            "Assets:Bank",
            "the declared account must be the directive header, not the metadata value",
        );
    }

    /// A bare posting account is never a declaration. Counter-test
    /// to make sure the helper isn't trivially marking every
    /// ACCOUNT token as a declaration.
    #[test]
    fn account_declaration_spans_excludes_posting_account() {
        use rustledger_parser::parse;
        let source = "\
2024-01-01 open Assets:Bank USD
2024-06-15 * \"Coffee\"
  Assets:Bank  -5.00 USD
  Expenses:Food
";
        let result = parse(source);
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        let decls = account_declaration_spans(&result);
        // Only one declaration (the Open header).
        assert_eq!(decls.len(), 1, "got {decls:?}");

        // Neither the Assets:Bank posting nor the Expenses:Food
        // posting is in `decls`.
        let posting_occurrences: Vec<_> = result
            .account_occurrences
            .iter()
            .filter(|o| !decls.contains(&o.span))
            .collect();
        assert_eq!(
            posting_occurrences.len(),
            2,
            "expected 2 non-declaration occurrences (the two postings); got {posting_occurrences:?}",
        );
    }
}
