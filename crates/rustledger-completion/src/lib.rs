//! Editor-agnostic completion logic for Beancount sources.
//!
//! This crate is the single source of truth for the completion logic
//! shared between the LSP (`rustledger-lsp`) and the WASM editor
//! (`rustledger-wasm`). It is deliberately pure: no clock access, no
//! `lsp-types`, no `wasm-bindgen`. Callers supply the live data
//! (account/currency/payee/tag/link string lists and "today's" date)
//! and map the neutral [`CompletionCandidate`] results into their own
//! editor-specific item types.
//!
//! The two responsibilities are:
//! 1. **Context detection** — [`offset_to_byte`] maps a position
//!    (under a [`PositionEncoding`]) to a byte offset, then
//!    [`classify_context`] classifies the text before the cursor into a
//!    [`CompletionContext`].
//! 2. **Candidate generation** — the `*_candidates` functions produce
//!    neutral [`CompletionCandidate`] lists for each context.

/// Standard Beancount account types.
pub const ACCOUNT_TYPES: &[&str] = &["Assets", "Liabilities", "Equity", "Income", "Expenses"];

/// Standard Beancount directives.
pub const DIRECTIVES: &[&str] = &[
    "open",
    "close",
    "commodity",
    "balance",
    "pad",
    "event",
    "query",
    "note",
    "document",
    "custom",
    "price",
    "txn",
    "*",
    "!",
];

/// Completion context detected from cursor position.
///
/// This is the LSP superset (the WASM editor previously lacked the
/// `Tag`/`Link` variants; it now gains them through this crate).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletionContext {
    /// At the start of a line (expecting date or directive).
    LineStart,
    /// After a date (expecting directive keyword or flag).
    AfterDate,
    /// After directive keyword (expecting account).
    ExpectingAccount,
    /// Inside an account name (after colon).
    AccountSegment {
        /// The prefix typed so far (e.g., "Assets:").
        prefix: String,
    },
    /// After an amount (expecting currency).
    ExpectingCurrency,
    /// Inside a string (payee/narration).
    InsideString,
    /// Typing a tag (after `#`) on a transaction header or in
    /// `pushtag`/`poptag`.
    Tag,
    /// Typing a link (after `^`) on a transaction header.
    Link,
    /// Unknown context.
    Unknown,
}

/// How a position offset is encoded by the caller.
///
/// The LSP negotiates UTF-8 byte offsets or UTF-16 code units; the WASM
/// editor passes character (Unicode scalar value) offsets. All three map
/// to a byte offset via [`offset_to_byte`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PositionEncoding {
    /// UTF-8 byte offsets.
    Utf8,
    /// UTF-16 code units (the LSP 3.17 default).
    Utf16,
    /// Unicode scalar value (character) offsets — the WASM editor's
    /// convention (see issue #1289).
    Char,
}

/// The kind of a completion candidate.
///
/// One variant per distinct item kind emitted by either adapter, so the
/// neutral candidate can be mapped back to the exact LSP
/// `CompletionItemKind` / WASM `CompletionKind` it replaces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionKind {
    /// Today's date template (line start).
    Date,
    /// A directive keyword (after a date).
    Directive,
    /// A standard account type (`Assets:`, `Expenses:`, …).
    AccountType,
    /// A fully-qualified known account name.
    Account,
    /// An intermediate account segment that has further sub-segments
    /// (rendered as a folder).
    AccountSegmentFolder,
    /// A currency/commodity.
    Currency,
    /// A known payee name.
    Payee,
    /// A tag (after `#`).
    Tag,
    /// A link (after `^`).
    Link,
}

/// A neutral, editor-agnostic completion candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionCandidate {
    /// The label shown in the completion popup.
    pub label: String,
    /// The text to insert. Distinguished from `label` (e.g. tags keep
    /// the `#` in `label` but drop it in `insert_text`). When equal to
    /// `label` (no special insert behavior) adapters may treat it as
    /// "no explicit insert text".
    pub insert_text: String,
    /// The kind of candidate.
    pub kind: CompletionKind,
    /// Human-readable detail string, if any.
    pub detail: Option<String>,
}

/// Map a position `offset` (in the given `encoding`) into a byte offset
/// into `line`, clamped to a char boundary.
///
/// - [`PositionEncoding::Utf8`] / [`PositionEncoding::Utf16`] walk the
///   line's chars once accumulating the encoded length, bailing at the
///   start of the char a mid-char offset would land in (the LSP
///   behavior).
/// - [`PositionEncoding::Char`] treats `offset` as a character index and
///   maps to the byte offset of that char, clamping past end-of-line to
///   the line length (the #1289 WASM behavior).
///
/// The result is always a valid char boundary in `line`, so slicing
/// `&line[..offset_to_byte(...)]` never panics.
#[must_use]
pub fn offset_to_byte(line: &str, offset: usize, encoding: PositionEncoding) -> usize {
    match encoding {
        PositionEncoding::Char => line
            .char_indices()
            .nth(offset)
            .map_or(line.len(), |(b, _)| b),
        PositionEncoding::Utf8 | PositionEncoding::Utf16 => {
            let mut acc = 0usize;
            let mut byte_col = 0usize;
            for ch in line.chars() {
                if acc >= offset {
                    break;
                }
                let u = match encoding {
                    PositionEncoding::Utf8 => ch.len_utf8(),
                    PositionEncoding::Utf16 => ch.len_utf16(),
                    PositionEncoding::Char => unreachable!(),
                };
                if acc + u > offset {
                    // Position lands mid-char — bail at the start of this char.
                    break;
                }
                acc += u;
                byte_col += ch.len_utf8();
            }
            byte_col
        }
    }
}

/// Classify the completion context from the text before the cursor.
///
/// `before_cursor` is the slice of the current line up to (and not
/// including) the cursor, already mapped to a byte boundary via
/// [`offset_to_byte`].
///
/// This is the LSP classification body, ported verbatim, including the
/// `in_code_position`-gated Tag/Link detection.
#[must_use]
pub fn classify_context(before_cursor: &str) -> CompletionContext {
    let trimmed = before_cursor.trim_start();

    // Check if we're at the start of a posting (indented line)
    // This must come before the empty check since an indented line
    // with just spaces should be expecting an account.
    if before_cursor.starts_with("  ") || before_cursor.starts_with('\t') {
        // Empty indented line means expecting an account
        if trimmed.is_empty() {
            return CompletionContext::ExpectingAccount;
        }
        // Inside a posting - could be account or amount
        let posting_content = trimmed;

        // Check if there's already an account (contains colon and space after)
        if posting_content.contains(':') && posting_content.contains(' ') {
            // After account, might be expecting amount or currency
            let parts: Vec<&str> = posting_content.split_whitespace().collect();
            if parts.len() >= 2 {
                // Check if last part looks like a number
                if let Some(last) = parts.last()
                    && (last.parse::<f64>().is_ok() || last.ends_with('.'))
                {
                    return CompletionContext::ExpectingCurrency;
                }
            }
            return CompletionContext::Unknown;
        }

        // Check if typing an account segment
        if let Some(colon_pos) = posting_content.rfind(':') {
            let prefix = &posting_content[..=colon_pos];
            return CompletionContext::AccountSegment {
                prefix: prefix.to_string(),
            };
        }

        // Starting an account name
        return CompletionContext::ExpectingAccount;
    }

    // Tag (`#tag`) / link (`^link`) completion. Tags and links appear
    // on transaction header lines (after the date/flag/strings) and in
    // `pushtag`/`poptag` directives. We trigger when the token directly
    // under the cursor begins with the sigil, but only when the cursor
    // is in *code* position: not inside a string literal (a `#` in a
    // narration is just text) and not after a comment marker. The
    // cursor must also sit at the end of the token (no trailing
    // whitespace), i.e. the user is still typing it.
    if in_code_position(before_cursor)
        && !before_cursor.ends_with(char::is_whitespace)
        && let Some(token) = before_cursor.split_whitespace().next_back()
    {
        if token.starts_with('#') {
            return CompletionContext::Tag;
        }
        if token.starts_with('^') {
            return CompletionContext::Link;
        }
    }

    // Empty or whitespace only at line start (not indented)
    if trimmed.is_empty() {
        return CompletionContext::LineStart;
    }

    // Check for date at line start (YYYY-MM-DD pattern). Guard the
    // 10-byte split on a char boundary: a `YYYY-MM-DD` prefix is all
    // ASCII, so if byte 10 lands mid-character the line can't be a
    // date, and slicing there would panic on multi-byte input.
    if trimmed.len() >= 10 && trimmed.is_char_boundary(10) && is_date_like(&trimmed[..10]) {
        let after_date = trimmed[10..].trim_start();
        if after_date.is_empty() {
            return CompletionContext::AfterDate;
        }

        // Check for directive keywords
        for directive in DIRECTIVES {
            if let Some(rest) = after_date.strip_prefix(directive) {
                let after_directive = rest.trim_start();
                if after_directive.is_empty() || !after_directive.contains(' ') {
                    // After directive, expecting account for most directives
                    match *directive {
                        "open" | "close" | "balance" | "pad" | "note" | "document" => {
                            if let Some(colon_pos) = after_directive.rfind(':') {
                                return CompletionContext::AccountSegment {
                                    prefix: after_directive[..=colon_pos].to_string(),
                                };
                            }
                            return CompletionContext::ExpectingAccount;
                        }
                        _ => return CompletionContext::Unknown,
                    }
                }
            }
        }

        // After date but no recognized directive yet
        return CompletionContext::AfterDate;
    }

    // Check if inside a quoted string
    let quote_count = before_cursor.chars().filter(|&c| c == '"').count();
    if quote_count % 2 == 1 {
        return CompletionContext::InsideString;
    }

    CompletionContext::Unknown
}

/// Whether the end of `before` is in "code" position: not inside a
/// string literal and not past a comment marker. A single forward scan
/// tracks string state with backslash-escape handling, matching the
/// lexer's string rule (`"([^"\\]|\\.)*"`), so a `"` or `;` that lives
/// *inside* a narration does not flip the classification. An unescaped,
/// unquoted `;` starts a comment, after which nothing is code.
fn in_code_position(before: &str) -> bool {
    let mut in_string = false;
    let mut escaped = false;
    for ch in before.chars() {
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
        } else if ch == '"' {
            in_string = true;
        } else if ch == ';' {
            // Comment marker outside any string: rest of line is comment.
            return false;
        }
    }
    !in_string
}

/// Check if a string looks like a date (YYYY-MM-DD).
fn is_date_like(s: &str) -> bool {
    if s.len() != 10 {
        return false;
    }
    let chars: Vec<char> = s.chars().collect();
    chars[4] == '-'
        && chars[7] == '-'
        && chars.iter().enumerate().all(|(i, c)| {
            if i == 4 || i == 7 {
                *c == '-'
            } else {
                c.is_ascii_digit()
            }
        })
}

/// The detail string shown for a directive keyword.
#[must_use]
fn directive_detail(directive: &str) -> &'static str {
    match directive {
        "open" => "Open an account",
        "close" => "Close an account",
        "commodity" => "Define a commodity/currency",
        "balance" => "Assert account balance",
        "pad" => "Pad account to target",
        "event" => "Record an event",
        "query" => "Define a named query",
        "note" => "Add a note to an account",
        "document" => "Link a document",
        "custom" => "Custom directive",
        "price" => "Record a price",
        "txn" | "*" => "Transaction (complete)",
        "!" => "Transaction (incomplete)",
        _ => "",
    }
}

/// Candidates at line start: a single date template using the supplied
/// `today` string (the crate is clock-free; each adapter passes its own
/// date).
#[must_use]
pub fn line_start_candidates(today: &str) -> Vec<CompletionCandidate> {
    vec![CompletionCandidate {
        label: today.to_string(),
        insert_text: format!("{today} "),
        kind: CompletionKind::Date,
        detail: Some("Today's date".to_string()),
    }]
}

/// Candidates after a date: the directive keywords.
#[must_use]
pub fn after_date_candidates() -> Vec<CompletionCandidate> {
    DIRECTIVES
        .iter()
        .map(|&d| CompletionCandidate {
            label: d.to_string(),
            insert_text: format!("{d} "),
            kind: CompletionKind::Directive,
            detail: Some(directive_detail(d).to_string()),
        })
        .collect()
}

/// Candidates when starting an account name: the standard account types
/// followed by every known account.
///
/// `accounts` must be the full, sorted, deduplicated list of known
/// accounts — the adapters gather it the same way (file + ledger state).
/// We return every known account: the client filters by the typed
/// prefix, and capping server-side defeats that filtering (issue #1183).
#[must_use]
pub fn account_start_candidates(accounts: &[String]) -> Vec<CompletionCandidate> {
    let mut items: Vec<CompletionCandidate> = ACCOUNT_TYPES
        .iter()
        .map(|&t| CompletionCandidate {
            label: format!("{t}:"),
            insert_text: format!("{t}:"),
            kind: CompletionKind::AccountType,
            detail: Some(format!("{t} account type")),
        })
        .collect();

    for account in accounts {
        items.push(CompletionCandidate {
            label: account.clone(),
            insert_text: account.clone(),
            kind: CompletionKind::Account,
            detail: Some("Known account".to_string()),
        });
    }

    items
}

/// Candidates for the next account segment after a `prefix`.
///
/// For a `prefix` like `Assets:`, emits the unique next segments of
/// every account that starts with `prefix`; a segment that has further
/// sub-segments is a folder (inserts `segment:`), otherwise a leaf
/// account (inserts `segment`).
#[must_use]
pub fn account_segment_candidates(prefix: &str, accounts: &[String]) -> Vec<CompletionCandidate> {
    // Find accounts that start with this prefix
    let matching: Vec<_> = accounts.iter().filter(|a| a.starts_with(prefix)).collect();

    // Extract unique next segments
    let mut segments: Vec<String> = matching
        .iter()
        .filter_map(|a| {
            let after_prefix = &a[prefix.len()..];
            let next_segment = after_prefix.split(':').next()?;
            if next_segment.is_empty() {
                None
            } else {
                Some(next_segment.to_string())
            }
        })
        .collect();

    segments.sort();
    segments.dedup();

    segments
        .into_iter()
        .map(|seg| {
            let full = format!("{prefix}{seg}");
            // Check if this is a complete account or has more segments
            let has_more = matching.iter().any(|a| a.starts_with(&format!("{full}:")));
            let insert_text = if has_more {
                format!("{seg}:")
            } else {
                seg.clone()
            };
            CompletionCandidate {
                label: seg,
                insert_text,
                kind: if has_more {
                    CompletionKind::AccountSegmentFolder
                } else {
                    CompletionKind::Account
                },
                detail: Some(if has_more {
                    "Account segment".to_string()
                } else {
                    "Account".to_string()
                }),
            }
        })
        .collect()
}

/// Candidates for a currency after an amount.
#[must_use]
pub fn currency_candidates(currencies: &[String]) -> Vec<CompletionCandidate> {
    currencies
        .iter()
        .map(|c| CompletionCandidate {
            label: c.clone(),
            insert_text: c.clone(),
            kind: CompletionKind::Currency,
            detail: Some("Currency".to_string()),
        })
        .collect()
}

/// Candidates for a payee/narration inside a string. Returns all known
/// payees — the client filters (issue #1183, the `.take(20)` trap).
#[must_use]
pub fn payee_candidates(payees: &[String]) -> Vec<CompletionCandidate> {
    payees
        .iter()
        .map(|p| CompletionCandidate {
            label: p.clone(),
            insert_text: p.clone(),
            kind: CompletionKind::Payee,
            detail: Some("Known payee".to_string()),
        })
        .collect()
}

/// Candidates for a tag after `#` (issue #1268).
///
/// The `#` is a trigger character the user has already typed, so
/// `insert_text` carries the tag name *without* the `#`; `label` keeps
/// the `#` for a readable popup. `tags` come back without the leading
/// `#` from the core extractor.
#[must_use]
pub fn tag_candidates(tags: &[String]) -> Vec<CompletionCandidate> {
    tags.iter()
        .map(|tag| CompletionCandidate {
            label: format!("#{tag}"),
            insert_text: tag.clone(),
            kind: CompletionKind::Tag,
            detail: Some("Tag".to_string()),
        })
        .collect()
}

/// Candidates for a link after `^` (issue #1268). Mirrors
/// [`tag_candidates`]; the sigil is kept in `label` and dropped in
/// `insert_text`.
#[must_use]
pub fn link_candidates(links: &[String]) -> Vec<CompletionCandidate> {
    links
        .iter()
        .map(|link| CompletionCandidate {
            label: format!("^{link}"),
            insert_text: link.clone(),
            kind: CompletionKind::Link,
            detail: Some("Link".to_string()),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Classify the context at the end of `before` (the whole string is
    /// treated as the text before the cursor).
    fn ctx(before: &str) -> CompletionContext {
        classify_context(before)
    }

    #[test]
    fn test_is_date_like() {
        assert!(is_date_like("2024-01-15"));
        assert!(is_date_like("2000-12-31"));
        assert!(!is_date_like("2024/01/15"));
        assert!(!is_date_like("24-01-15"));
        assert!(!is_date_like("not-a-date"));
    }

    #[test]
    fn classify_line_start() {
        assert_eq!(ctx(""), CompletionContext::LineStart);
        // A single leading space is not the 2-space posting indent.
        assert_eq!(ctx(" "), CompletionContext::LineStart);
    }

    #[test]
    fn classify_after_date() {
        assert_eq!(ctx("2024-01-15 "), CompletionContext::AfterDate);
    }

    #[test]
    fn classify_expecting_account() {
        assert_eq!(ctx("  "), CompletionContext::ExpectingAccount);
        assert_eq!(ctx("2024-01-15 open "), CompletionContext::ExpectingAccount);
    }

    #[test]
    fn classify_account_segment() {
        assert_eq!(
            ctx("  Assets:"),
            CompletionContext::AccountSegment {
                prefix: "Assets:".to_string()
            }
        );
        assert_eq!(
            ctx("2024-01-15 open Assets:"),
            CompletionContext::AccountSegment {
                prefix: "Assets:".to_string()
            }
        );
    }

    #[test]
    fn classify_expecting_currency() {
        assert_eq!(
            ctx("  Assets:Bank  100.00 "),
            CompletionContext::ExpectingCurrency
        );
    }

    #[test]
    fn classify_inside_string() {
        assert_eq!(ctx("text \"inside"), CompletionContext::InsideString);
    }

    #[test]
    fn classify_unknown() {
        assert_eq!(ctx("some random text"), CompletionContext::Unknown);
    }

    #[test]
    fn classify_tag_on_transaction_header() {
        assert_eq!(
            ctx("2024-01-15 * \"Central Perk\" #cof"),
            CompletionContext::Tag
        );
        assert_eq!(
            ctx("2024-01-15 * \"Central Perk\" #"),
            CompletionContext::Tag
        );
    }

    #[test]
    fn classify_link_on_transaction_header() {
        assert_eq!(
            ctx("2024-01-15 * \"Central Perk\" ^trip"),
            CompletionContext::Link
        );
    }

    #[test]
    fn classify_tag_on_pushtag() {
        assert_eq!(ctx("pushtag #tr"), CompletionContext::Tag);
        assert_eq!(ctx("poptag #tr"), CompletionContext::Tag);
    }

    #[test]
    fn classify_hash_inside_string_is_not_tag() {
        let c = ctx("2024-01-15 * \"paid #5 invoice");
        assert_ne!(c, CompletionContext::Tag);
        assert_ne!(c, CompletionContext::Link);
    }

    #[test]
    fn classify_hash_in_comment_is_not_tag() {
        let c = ctx("2024-01-15 * \"Lunch\" ; see #123");
        assert_ne!(c, CompletionContext::Tag);
        assert_ne!(c, CompletionContext::Link);
    }

    #[test]
    fn classify_after_completed_tag_is_not_tag() {
        assert_eq!(
            ctx("2024-01-15 * \"Central Perk\" #coffee "),
            CompletionContext::AfterDate
        );
    }

    #[test]
    fn classify_tag_after_semicolon_inside_string() {
        assert_eq!(ctx("2024-01-15 * \"a;b\" #tr"), CompletionContext::Tag);
    }

    #[test]
    fn classify_escaped_quote_keeps_string_open() {
        let c = ctx("2024-01-15 * \"a\\\"b #tag");
        assert_ne!(c, CompletionContext::Tag);
        assert_ne!(c, CompletionContext::Link);
    }

    #[test]
    fn test_in_code_position() {
        assert!(in_code_position("2024-01-15 * \"x\" #"));
        assert!(in_code_position("pushtag #"));
        assert!(!in_code_position("2024-01-15 * \"x\" ; "));
        assert!(!in_code_position("2024-01-15 * \"open"));
        assert!(in_code_position("2024-01-15 * \"a;b\" "));
        assert!(!in_code_position("2024-01-15 * \"a\\\"b"));
    }

    // ---- offset_to_byte ----

    #[test]
    fn offset_to_byte_char_korean_partial_segment() {
        // #1289: "  Liabilities:Card:롯", char offset 20 is after "롯".
        let line = "  Liabilities:Card:롯";
        let byte = offset_to_byte(line, 20, PositionEncoding::Char);
        // The slice must not panic and must contain the colon prefix.
        let before = &line[..byte];
        assert_eq!(
            classify_context(before),
            CompletionContext::AccountSegment {
                prefix: "Liabilities:Card:".to_string()
            }
        );
        // Offset 19 (at the colon, before "롯") is the other boundary.
        let byte19 = offset_to_byte(line, 19, PositionEncoding::Char);
        assert_eq!(
            classify_context(&line[..byte19]),
            CompletionContext::AccountSegment {
                prefix: "Liabilities:Card:".to_string()
            }
        );
    }

    #[test]
    fn offset_to_byte_char_past_end_clamps() {
        let line = "abc";
        assert_eq!(offset_to_byte(line, 100, PositionEncoding::Char), 3);
    }

    #[test]
    fn offset_to_byte_utf16_surrogate_pair() {
        // "🍣" is 2 UTF-16 units, 4 UTF-8 bytes.
        let line = "a🍣b";
        // After 'a' (1 unit) + "🍣" (2 units) = 3 units -> byte 5.
        assert_eq!(offset_to_byte(line, 3, PositionEncoding::Utf16), 5);
        // Mid-surrogate (offset 2) bails at the start of "🍣" -> byte 1.
        assert_eq!(offset_to_byte(line, 2, PositionEncoding::Utf16), 1);
    }

    #[test]
    fn offset_to_byte_utf8_multibyte() {
        // "소" is 3 UTF-8 bytes.
        let line = "x소y";
        // After 'x' (1 byte) + "소" (3 bytes) = byte 4.
        assert_eq!(offset_to_byte(line, 4, PositionEncoding::Utf8), 4);
        // Mid-char (offset 2) bails at the start of "소" -> byte 1.
        assert_eq!(offset_to_byte(line, 2, PositionEncoding::Utf8), 1);
    }

    // ---- candidate algorithms ----

    #[test]
    fn line_start_candidate_uses_supplied_date() {
        let items = line_start_candidates("2026-06-12");
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].label, "2026-06-12");
        assert_eq!(items[0].insert_text, "2026-06-12 ");
        assert_eq!(items[0].kind, CompletionKind::Date);
    }

    #[test]
    fn after_date_candidates_returns_all_directives() {
        let items = after_date_candidates();
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        assert!(labels.contains(&"open"));
        assert!(labels.contains(&"close"));
        assert!(labels.contains(&"balance"));
        assert!(labels.contains(&"*"));
        assert!(labels.contains(&"!"));
        // insert_text appends a space.
        let open = items.iter().find(|i| i.label == "open").unwrap();
        assert_eq!(open.insert_text, "open ");
        assert_eq!(open.detail.as_deref(), Some("Open an account"));
    }

    #[test]
    fn account_start_candidates_includes_types_and_all_accounts() {
        let accounts: Vec<String> = (1..=30)
            .map(|n| format!("Expenses:ExpenseType{n:02}"))
            .collect();
        let items = account_start_candidates(&accounts);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        assert!(labels.contains(&"Assets:"));
        // No cap (#1183): all 30 accounts present.
        assert!(labels.contains(&"Expenses:ExpenseType19"));
        assert!(labels.contains(&"Expenses:ExpenseType20"));
        assert!(labels.contains(&"Expenses:ExpenseType30"));
        // Account-type entry is a folder kind.
        let assets = items.iter().find(|i| i.label == "Assets:").unwrap();
        assert_eq!(assets.kind, CompletionKind::AccountType);
    }

    #[test]
    fn account_segment_candidates_filters_and_marks_folders() {
        let accounts = vec![
            "Assets:Bank:Checking".to_string(),
            "Assets:Bank:Savings".to_string(),
            "Assets:Crypto".to_string(),
            "Expenses:Food".to_string(),
        ];
        let items = account_segment_candidates("Assets:Bank:", &accounts);
        assert_eq!(items.len(), 2);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        assert!(labels.contains(&"Checking"));
        assert!(labels.contains(&"Savings"));
        // Leaf segments insert without a trailing colon.
        let checking = items.iter().find(|i| i.label == "Checking").unwrap();
        assert_eq!(checking.insert_text, "Checking");
        assert_eq!(checking.kind, CompletionKind::Account);

        // Top-level prefix: "Bank" has more, "Crypto" does not.
        let top = account_segment_candidates("Assets:", &accounts);
        let bank = top.iter().find(|i| i.label == "Bank").unwrap();
        assert_eq!(bank.kind, CompletionKind::AccountSegmentFolder);
        assert_eq!(bank.insert_text, "Bank:");
        let crypto = top.iter().find(|i| i.label == "Crypto").unwrap();
        assert_eq!(crypto.kind, CompletionKind::Account);
        assert_eq!(crypto.insert_text, "Crypto");
    }

    #[test]
    fn currency_candidates_basic() {
        let items = currency_candidates(&["USD".to_string(), "EUR".to_string()]);
        assert_eq!(items.len(), 2);
        assert_eq!(items[0].kind, CompletionKind::Currency);
        assert_eq!(items[0].detail.as_deref(), Some("Currency"));
    }

    #[test]
    fn payee_candidates_returns_all() {
        let payees: Vec<String> = (1..=30).map(|n| format!("Buy{n:02}")).collect();
        let items = payee_candidates(&payees);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        assert!(labels.contains(&"Buy19"));
        assert!(labels.contains(&"Buy20"));
        assert!(labels.contains(&"Buy30"));
        assert_eq!(items[0].kind, CompletionKind::Payee);
    }

    #[test]
    fn tag_candidates_keep_sigil_in_label_only() {
        let items = tag_candidates(&["coffee".to_string(), "morning".to_string()]);
        let coffee = items.iter().find(|i| i.label == "#coffee").unwrap();
        assert_eq!(coffee.insert_text, "coffee");
        assert_eq!(coffee.kind, CompletionKind::Tag);
        assert_eq!(coffee.detail.as_deref(), Some("Tag"));
    }

    #[test]
    fn link_candidates_keep_sigil_in_label_only() {
        let items = link_candidates(&["trip-2024".to_string()]);
        let trip = items.iter().find(|i| i.label == "^trip-2024").unwrap();
        assert_eq!(trip.insert_text, "trip-2024");
        assert_eq!(trip.kind, CompletionKind::Link);
        assert_eq!(trip.detail.as_deref(), Some("Link"));
    }
}
