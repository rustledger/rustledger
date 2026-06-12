//! Completion handler for autocompletion.
//!
//! Provides context-aware completions for:
//! - Account names (after posting indentation or in directives)
//! - Currencies (after amounts)
//! - Directives (after dates)
//! - Payees and narrations (in transaction headers)

use crate::ledger_state::LedgerState;
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionParams, CompletionResponse, Position,
};
use rustledger_parser::ParseResult;

/// Standard Beancount account types.
const ACCOUNT_TYPES: &[&str] = &["Assets", "Liabilities", "Equity", "Income", "Expenses"];

/// Standard Beancount directives.
const DIRECTIVES: &[&str] = &[
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
#[derive(Debug, Clone, PartialEq)]
pub enum CompletionContext {
    /// At the start of a line (expecting date or directive)
    LineStart,
    /// After a date (expecting directive keyword or flag)
    AfterDate,
    /// After directive keyword (expecting account)
    ExpectingAccount,
    /// Inside an account name (after colon)
    AccountSegment {
        /// The prefix typed so far (e.g., "Assets:")
        prefix: String,
    },
    /// After an amount (expecting currency)
    ExpectingCurrency,
    /// Inside a string (payee/narration)
    InsideString,
    /// Typing a tag (after `#`) on a transaction header or in
    /// `pushtag`/`poptag`.
    Tag,
    /// Typing a link (after `^`) on a transaction header.
    Link,
    /// Unknown context
    Unknown,
}

/// Handle a completion request.
///
/// If `ledger_state` is provided, completions will include data from the full ledger
/// (all included files), not just the current file.
pub fn handle_completion(
    params: &CompletionParams,
    source: &str,
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
    encoding: super::utils::PositionEncoding,
) -> Option<CompletionResponse> {
    let position = params.text_document_position.position;
    let uri = &params.text_document_position.text_document.uri;
    let context = detect_context(source, position, encoding);

    tracing::debug!("Completion context: {:?} at {:?}", context, position);

    let mut items = match context {
        CompletionContext::LineStart => complete_line_start(),
        CompletionContext::AfterDate => complete_after_date(),
        CompletionContext::ExpectingAccount => complete_account_start(parse_result, ledger_state),
        CompletionContext::AccountSegment { prefix } => {
            complete_account_segment(&prefix, parse_result, ledger_state)
        }
        CompletionContext::ExpectingCurrency => complete_currency(parse_result, ledger_state),
        CompletionContext::InsideString => complete_payee(parse_result, ledger_state),
        CompletionContext::Tag => complete_tag(parse_result, ledger_state),
        CompletionContext::Link => complete_link(parse_result, ledger_state),
        CompletionContext::Unknown => return None,
    };

    // Add URI to each item's data for resolve
    let uri_data = serde_json::json!({ "uri": uri.as_str() });
    for item in &mut items {
        item.data = Some(uri_data.clone());
    }

    if items.is_empty() {
        None
    } else {
        // Visibility for the eventual `isIncomplete: true` /
        // server-side prefix filtering work — if a future bug report
        // says "autocomplete is slow on my N-thousand-account
        // ledger", this log line tells you the response size without
        // needing to instrument from scratch. Cheap because completion
        // requests are user-driven, not hot-loop. The context is
        // already logged above (line ~72) so the size alone here is
        // enough to correlate.
        tracing::debug!("Completion response: {} items", items.len());
        Some(CompletionResponse::Array(items))
    }
}

/// Detect the completion context from cursor position.
///
/// `position.character` is interpreted in the negotiated `encoding`
/// — UTF-8 byte offset or UTF-16 code-unit count. Walking `chars()`
/// once accumulates the encoded length so the conversion is correct
/// under either negotiation.
fn detect_context(
    source: &str,
    position: Position,
    encoding: super::utils::PositionEncoding,
) -> CompletionContext {
    use super::utils::PositionEncoding;
    let line = get_line(source, position.line as usize);

    // Map `position.character` (in the negotiated encoding) to a byte
    // offset into `line`. Walks chars once.
    let col = position.character as usize;
    let mut acc = 0usize;
    let mut byte_col = 0usize;
    for ch in line.chars() {
        if acc >= col {
            break;
        }
        let u = match encoding {
            PositionEncoding::Utf8 => ch.len_utf8(),
            PositionEncoding::Utf16 => ch.len_utf16(),
        };
        if acc + u > col {
            // Position lands mid-char — bail at the start of this char.
            break;
        }
        acc += u;
        byte_col += ch.len_utf8();
    }
    let before_cursor = &line[..byte_col];

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
            let prefix = &posting_content[..colon_pos + 1];
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

    // Check for date at line start (YYYY-MM-DD pattern)
    if trimmed.len() >= 10 && is_date_like(&trimmed[..10]) {
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
                                    prefix: after_directive[..colon_pos + 1].to_string(),
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

/// Get a specific line from source.
fn get_line(source: &str, line_num: usize) -> &str {
    source.lines().nth(line_num).unwrap_or("")
}

/// Whether the end of `before` is in "code" position: not inside a
/// string literal and not past a comment marker. A single forward scan
/// tracks string state with backslash-escape handling, matching the
/// lexer's string rule (`"([^"\\]|\\.)*"`), so a `"` or `;` that lives
/// *inside* a narration does not flip the classification. An unescaped,
/// unquoted `;` starts a comment, after which nothing is code.
///
/// This is what lets tag/link detection fire on `"a;b" #tag` (the `;`
/// is in the string) while staying silent on `"x" ; #note` (real
/// comment) and `"open #not-a-tag` (unterminated string).
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

/// Complete at line start (date template).
fn complete_line_start() -> Vec<CompletionItem> {
    let today = jiff::Zoned::now().date().to_string();
    vec![CompletionItem {
        label: today.clone(),
        kind: Some(CompletionItemKind::VALUE),
        detail: Some("Today's date".to_string()),
        insert_text: Some(format!("{} ", today)),
        ..Default::default()
    }]
}

/// Complete after a date (directive keywords).
fn complete_after_date() -> Vec<CompletionItem> {
    DIRECTIVES
        .iter()
        .map(|&d| {
            let detail = match d {
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
            };
            CompletionItem {
                label: d.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some(detail.to_string()),
                insert_text: Some(format!("{} ", d)),
                ..Default::default()
            }
        })
        .collect()
}

/// Complete account name start (account types).
fn complete_account_start(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    // First, offer standard account types
    let mut items: Vec<CompletionItem> = ACCOUNT_TYPES
        .iter()
        .map(|&t| CompletionItem {
            label: format!("{}:", t),
            kind: Some(CompletionItemKind::FOLDER),
            detail: Some(format!("{} account type", t)),
            ..Default::default()
        })
        .collect();

    // Collect known accounts from the current file and ledger state.
    //
    // Return every known account: the LSP client filters by the
    // user's typed prefix, and capping server-side here defeats that
    // filtering (the client never sees accounts past the cap, so any
    // prefix that matches a later-sorted account silently fails to
    // complete). The pre-fix `.take(20)` produced exactly issue
    // #1183, where `Expenses:ExpenseType20` and later accounts
    // wouldn't autocomplete because the alphabetical cut-off landed
    // at `ExpenseType19`. If completion latency on enormous ledgers
    // ever becomes a concern, switch to `isIncomplete: true` with
    // server-side prefix filtering rather than a blind cap.
    let known_accounts = get_all_accounts(parse_result, ledger_state);
    for account in &known_accounts {
        items.push(CompletionItem {
            label: account.clone(),
            kind: Some(CompletionItemKind::VARIABLE),
            detail: Some("Known account".to_string()),
            ..Default::default()
        });
    }

    items
}

/// Complete account segment after colon.
fn complete_account_segment(
    prefix: &str,
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    let known_accounts = get_all_accounts(parse_result, ledger_state);

    // Find accounts that start with this prefix
    let matching: Vec<_> = known_accounts
        .iter()
        .filter(|a| a.starts_with(prefix))
        .collect();

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
            let full = format!("{}{}", prefix, seg);
            // Check if this is a complete account or has more segments
            let has_more = matching
                .iter()
                .any(|a| a.starts_with(&format!("{}:", full)));
            CompletionItem {
                label: seg.clone(),
                kind: Some(if has_more {
                    CompletionItemKind::FOLDER
                } else {
                    CompletionItemKind::VARIABLE
                }),
                detail: Some(if has_more {
                    "Account segment".to_string()
                } else {
                    "Account".to_string()
                }),
                insert_text: Some(if has_more { format!("{}:", seg) } else { seg }),
                ..Default::default()
            }
        })
        .collect()
}

/// Complete currency after amount.
fn complete_currency(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    let currencies = get_all_currencies(parse_result, ledger_state);

    currencies
        .into_iter()
        .map(|c| CompletionItem {
            label: c.clone(),
            kind: Some(CompletionItemKind::UNIT),
            detail: Some("Currency".to_string()),
            ..Default::default()
        })
        .collect()
}

/// Complete payee/narration inside string.
fn complete_payee(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    let payees = get_all_payees(parse_result, ledger_state);

    // Same `.take(20)` trap as account completion (issue #1183):
    // the LSP client filters by the user's typed prefix, so capping
    // server-side silently drops payees that sort after the cap.
    // Return all; the client handles the volume.
    payees
        .into_iter()
        .map(|p| CompletionItem {
            label: p.clone(),
            kind: Some(CompletionItemKind::TEXT),
            detail: Some("Known payee".to_string()),
            ..Default::default()
        })
        .collect()
}

/// Complete a tag after `#` (issue #1268).
///
/// The `#` is a trigger character that the user has already typed, so
/// `insert_text`/`filter_text` carry the tag name *without* the `#` —
/// the client replaces the word it is completing (the text after the
/// sigil) and leaves the `#` in place. `label` keeps the `#` for a
/// readable popup. We return every known tag and let the client filter
/// as the user types (the same approach as `complete_account_start`),
/// rather than filtering server-side and risking a stale list under
/// `isIncomplete: false`.
fn complete_tag(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    get_all_tags(parse_result, ledger_state)
        .into_iter()
        .map(|tag| CompletionItem {
            label: format!("#{tag}"),
            kind: Some(CompletionItemKind::CONSTANT),
            detail: Some("Tag".to_string()),
            filter_text: Some(tag.clone()),
            insert_text: Some(tag),
            ..Default::default()
        })
        .collect()
}

/// Complete a link after `^` (issue #1268). Mirrors [`complete_tag`];
/// see its docs for the sigil/insert-text rationale.
fn complete_link(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    get_all_links(parse_result, ledger_state)
        .into_iter()
        .map(|link| CompletionItem {
            label: format!("^{link}"),
            kind: Some(CompletionItemKind::REFERENCE),
            detail: Some("Link".to_string()),
            filter_text: Some(link.clone()),
            insert_text: Some(link),
            ..Default::default()
        })
        .collect()
}

/// Get all accounts from the current file and ledger state.
fn get_all_accounts(parse_result: &ParseResult, ledger_state: Option<&LedgerState>) -> Vec<String> {
    let mut accounts = extract_accounts(parse_result);

    // Merge accounts from ledger state if available
    if let Some(state) = ledger_state {
        accounts.extend(state.accounts().iter().cloned());
    }

    accounts.sort();
    accounts.dedup();
    accounts
}

/// Get all currencies from the current file and ledger state.
fn get_all_currencies(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<String> {
    let mut currencies = extract_currencies(parse_result);

    // Merge currencies from ledger state if available
    if let Some(state) = ledger_state {
        currencies.extend(state.currencies().iter().cloned());
    }

    currencies.sort();
    currencies.dedup();
    currencies
}

/// Get all payees from the current file and ledger state.
fn get_all_payees(parse_result: &ParseResult, ledger_state: Option<&LedgerState>) -> Vec<String> {
    let mut payees = extract_payees(parse_result);

    // Merge payees from ledger state if available
    if let Some(state) = ledger_state {
        payees.extend(state.payees().iter().cloned());
    }

    payees.sort();
    payees.dedup();
    payees
}

/// Get all tags from the current file and ledger state.
fn get_all_tags(parse_result: &ParseResult, ledger_state: Option<&LedgerState>) -> Vec<String> {
    let mut tags = extract_tags(parse_result);

    // Merge tags from ledger state if available
    if let Some(state) = ledger_state {
        tags.extend(state.tags().iter().cloned());
    }

    tags.sort();
    tags.dedup();
    tags
}

/// Get all links from the current file and ledger state.
fn get_all_links(parse_result: &ParseResult, ledger_state: Option<&LedgerState>) -> Vec<String> {
    let mut links = extract_links(parse_result);

    // Merge links from ledger state if available
    if let Some(state) = ledger_state {
        links.extend(state.links().iter().cloned());
    }

    links.sort();
    links.dedup();
    links
}

/// Extract all account names from parse result.
fn extract_accounts(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_accounts_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract all currencies from parse result.
fn extract_currencies(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_currencies_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract payees from transactions.
fn extract_payees(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_payees_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract tags from parse result. Tag text comes back without the
/// leading `#`, which is exactly the form completion inserts after the
/// already-typed sigil. Delegates to the core visitor for exhaustive
/// position coverage (transaction/document tags, metadata, Custom).
fn extract_tags(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_tags_iter(parse_result.directives.iter().map(|s| &s.value))
}

/// Extract links from parse result. Like tags, link text comes back
/// without the leading `^`.
fn extract_links(parse_result: &ParseResult) -> Vec<String> {
    rustledger_core::extract_links_iter(parse_result.directives.iter().map(|s| &s.value))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_date_like() {
        assert!(is_date_like("2024-01-15"));
        assert!(is_date_like("2000-12-31"));
        assert!(!is_date_like("2024/01/15"));
        assert!(!is_date_like("24-01-15"));
        assert!(!is_date_like("not-a-date"));
    }

    #[test]
    fn test_detect_context_line_start() {
        let source = "\n";
        let ctx = detect_context(
            source,
            Position::new(0, 0),
            crate::handlers::utils::PositionEncoding::Utf16,
        );
        assert_eq!(ctx, CompletionContext::LineStart);
    }

    #[test]
    fn test_detect_context_after_date() {
        let source = "2024-01-15 ";
        let ctx = detect_context(
            source,
            Position::new(0, 11),
            crate::handlers::utils::PositionEncoding::Utf16,
        );
        assert_eq!(ctx, CompletionContext::AfterDate);
    }

    #[test]
    fn test_detect_context_expecting_account() {
        let source = "  ";
        let ctx = detect_context(
            source,
            Position::new(0, 2),
            crate::handlers::utils::PositionEncoding::Utf16,
        );
        assert_eq!(ctx, CompletionContext::ExpectingAccount);
    }

    #[test]
    fn test_detect_context_account_segment() {
        let source = "  Assets:";
        let ctx = detect_context(
            source,
            Position::new(0, 9),
            crate::handlers::utils::PositionEncoding::Utf16,
        );
        assert_eq!(
            ctx,
            CompletionContext::AccountSegment {
                prefix: "Assets:".to_string()
            }
        );
    }

    #[test]
    fn test_detect_context_multibyte_inline_comment_no_panic() {
        // Issue #699: cursor inside inline comment with Korean text should not panic.
        // "소" is U+C18C = 3 bytes in UTF-8, so byte offset != char offset.
        let source = "1970-01-01 open Assets:Cash:PettyCash KRW ; 소\n";
        // Position at char offset 45 — inside "소" if treated as byte index
        let pos = Position::new(0, 45);
        // Must not panic (the actual context value doesn't matter)
        let _ctx = detect_context(source, pos, crate::handlers::utils::PositionEncoding::Utf16);
    }

    #[test]
    fn test_detect_context_cjk_narration() {
        // CJK text in narration — cursor after multi-byte characters
        let source = "2024-01-15 * \"午餐\" \"中華料理\"\n  Expenses:Food  100 CNY\n";
        let pos = Position::new(0, 20);
        // Must not panic
        let _ctx = detect_context(source, pos, crate::handlers::utils::PositionEncoding::Utf16);
    }

    #[test]
    fn test_detect_context_emoji_narration_utf16_offset() {
        // Non-BMP emoji uses two UTF-16 code units in LSP positions.
        // Validates surrogate-pair handling in char_offset_to_byte.
        let source = "2024-01-15 * \"🍣\"\n";
        // UTF-16 offsets: "2024-01-15 * \"" = 14 units, "🍣" = 2 units, "\"" = 1 unit
        // Position 17 is after the closing quote
        let pos = Position::new(0, 17);
        // Must not panic
        let _ctx = detect_context(source, pos, crate::handlers::utils::PositionEncoding::Utf16);
    }

    /// Regression for #1183: pre-fix `complete_account_start` capped
    /// known-account completions at the first 20 entries (alphabetically
    /// sorted), so accounts past that cut-off would silently fail to
    /// autocomplete on the client side — the LSP client filters the
    /// list it's given by the user's typed prefix, so any account the
    /// server dropped at the cap was invisible to filtering. The
    /// reporter's exact repro: 30 `Expenses:ExpenseType01..30` opens,
    /// of which only 01..19 made the cut.
    #[test]
    fn complete_account_start_returns_all_known_accounts_above_legacy_cap() {
        let source = "\
2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary
2024-01-01 open Income:SomethingElse
2024-01-01 open Expenses:ExpenseType01
2024-01-01 open Expenses:ExpenseType02
2024-01-01 open Expenses:ExpenseType03
2024-01-01 open Expenses:ExpenseType04
2024-01-01 open Expenses:ExpenseType05
2024-01-01 open Expenses:ExpenseType06
2024-01-01 open Expenses:ExpenseType07
2024-01-01 open Expenses:ExpenseType08
2024-01-01 open Expenses:ExpenseType09
2024-01-01 open Expenses:ExpenseType10
2024-01-01 open Expenses:ExpenseType11
2024-01-01 open Expenses:ExpenseType12
2024-01-01 open Expenses:ExpenseType13
2024-01-01 open Expenses:ExpenseType14
2024-01-01 open Expenses:ExpenseType15
2024-01-01 open Expenses:ExpenseType16
2024-01-01 open Expenses:ExpenseType17
2024-01-01 open Expenses:ExpenseType18
2024-01-01 open Expenses:ExpenseType19
2024-01-01 open Expenses:ExpenseType20
2024-01-01 open Expenses:ExpenseType21
2024-01-01 open Expenses:ExpenseType22
2024-01-01 open Expenses:ExpenseType23
2024-01-01 open Expenses:ExpenseType24
2024-01-01 open Expenses:ExpenseType25
2024-01-01 open Expenses:ExpenseType26
2024-01-01 open Expenses:ExpenseType27
2024-01-01 open Expenses:ExpenseType28
2024-01-01 open Expenses:ExpenseType29
2024-01-01 open Expenses:ExpenseType30
";
        let parsed = rustledger_parser::parse(source);
        assert!(
            parsed.errors.is_empty(),
            "fixture must parse cleanly: {:?}",
            parsed.errors,
        );

        let items = complete_account_start(&parsed, None);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

        // The handler also returns standard account-type entries
        // (`Assets:`, `Expenses:`, …) — those are unrelated; the bug
        // is about the *known* account names. Spot-check the two
        // accounts that bracket the legacy cap.
        assert!(
            labels.contains(&"Expenses:ExpenseType19"),
            "ExpenseType19 must be reachable (pre-fix this was the last that worked); \
             labels = {labels:?}"
        );
        assert!(
            labels.contains(&"Expenses:ExpenseType20"),
            "ExpenseType20 must be reachable (pre-fix this was the first that failed); \
             labels = {labels:?}"
        );
        assert!(
            labels.contains(&"Expenses:ExpenseType30"),
            "ExpenseType30 must be reachable (pre-fix all 20+ accounts were dropped); \
             labels = {labels:?}"
        );
    }

    /// Companion regression for #1183: the account-completion cap had
    /// an identical `.take(20)` twin in `complete_payee`. Same shape,
    /// same fix, same hazard for re-introduction — this test pins it
    /// independently so a future contributor who restores the payee
    /// cap can't ride on the account test missing it. Constructing 30
    /// distinct payees requires 30 distinct transactions; the fixture
    /// uses a tight `Buy<NN>` payee with one balanced posting pair.
    #[test]
    fn complete_payee_returns_all_known_payees_above_legacy_cap() {
        use std::fmt::Write as _;

        let mut source = String::from("2024-01-01 open Assets:Cash USD\n");
        for n in 1..=30 {
            // Each transaction names a unique payee so all 30 reach
            // `extract_payees`. Pin every transaction to a real
            // calendar date (2024-02-01) — beancount allows multiple
            // transactions on the same day, and using `{n:02}` for
            // the day would generate Feb 30, which isn't a valid
            // date. Two-posting balanced form (`+1 / -1 USD` on the
            // same account) satisfies the parser's posting-count
            // requirement.
            writeln!(
                source,
                "2024-02-01 * \"Buy{n:02}\" \"\"\n  Assets:Cash  1 USD\n  Assets:Cash  -1 USD",
            )
            .unwrap();
        }

        let parsed = rustledger_parser::parse(&source);
        assert!(
            parsed.errors.is_empty(),
            "fixture must parse cleanly: {:?}",
            parsed.errors,
        );

        let items = complete_payee(&parsed, None);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();

        // Brackets across the legacy cap: pre-fix Buy01..Buy19 would
        // show, Buy20+ would be silently dropped. The new behavior
        // returns all 30.
        assert!(
            labels.contains(&"Buy19"),
            "Buy19 must be reachable (pre-fix last that worked); labels = {labels:?}"
        );
        assert!(
            labels.contains(&"Buy20"),
            "Buy20 must be reachable (pre-fix first that failed); labels = {labels:?}"
        );
        assert!(
            labels.contains(&"Buy30"),
            "Buy30 must be reachable (pre-fix all 20+ payees were dropped); labels = {labels:?}"
        );
    }

    // ---- Tag / link completion (issue #1268) ----

    /// Helper: detect context at the end of `before`, treating it as a
    /// single line with the cursor at the final character (UTF-16).
    fn ctx_at_end(before: &str) -> CompletionContext {
        let char_len = before.chars().map(char::len_utf16).sum::<usize>() as u32;
        detect_context(
            before,
            Position::new(0, char_len),
            crate::handlers::utils::PositionEncoding::Utf16,
        )
    }

    #[test]
    fn test_detect_context_tag_on_transaction_header() {
        // Typing a tag after the narration on a transaction header.
        assert_eq!(
            ctx_at_end("2024-01-15 * \"Central Perk\" #cof"),
            CompletionContext::Tag
        );
        // Bare `#` (just the trigger) is also a tag context.
        assert_eq!(
            ctx_at_end("2024-01-15 * \"Central Perk\" #"),
            CompletionContext::Tag
        );
    }

    #[test]
    fn test_detect_context_link_on_transaction_header() {
        assert_eq!(
            ctx_at_end("2024-01-15 * \"Central Perk\" ^trip"),
            CompletionContext::Link
        );
    }

    #[test]
    fn test_detect_context_tag_on_pushtag() {
        assert_eq!(ctx_at_end("pushtag #tr"), CompletionContext::Tag);
        assert_eq!(ctx_at_end("poptag #tr"), CompletionContext::Tag);
    }

    #[test]
    fn test_detect_context_hash_inside_string_is_not_tag() {
        // A `#` inside an (unterminated) narration is part of the
        // string, not a tag. The odd quote count suppresses the tag
        // branch; the existing header handling then returns AfterDate.
        let ctx = ctx_at_end("2024-01-15 * \"paid #5 invoice");
        assert_ne!(ctx, CompletionContext::Tag);
        assert_ne!(ctx, CompletionContext::Link);
    }

    #[test]
    fn test_detect_context_hash_in_comment_is_not_tag() {
        // A `#` after a `;` comment marker is not a tag.
        let ctx = ctx_at_end("2024-01-15 * \"Lunch\" ; see #123");
        assert_ne!(ctx, CompletionContext::Tag);
        assert_ne!(ctx, CompletionContext::Link);
    }

    #[test]
    fn test_detect_context_after_completed_tag_is_not_tag() {
        // Trailing whitespace means the tag is finished; we should not
        // still be offering tag completions.
        assert_eq!(
            ctx_at_end("2024-01-15 * \"Central Perk\" #coffee "),
            CompletionContext::AfterDate
        );
    }

    #[test]
    fn complete_tag_returns_known_tags_without_sigil_in_insert() {
        let source = "\
2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Expenses:Stuff USD

2024-01-15 * \"Central Perk\" #coffee #morning
  Assets:Bank:Checking  -5 USD
  Expenses:Stuff
";
        let parsed = rustledger_parser::parse(source);
        assert!(
            parsed.errors.is_empty(),
            "fixture must parse: {:?}",
            parsed.errors
        );

        let items = complete_tag(&parsed, None);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        assert!(labels.contains(&"#coffee"), "labels = {labels:?}");
        assert!(labels.contains(&"#morning"), "labels = {labels:?}");

        // The `#` is a trigger character the user already typed, so the
        // inserted/filtered text must NOT repeat it (else `##coffee`).
        let coffee = items.iter().find(|i| i.label == "#coffee").unwrap();
        assert_eq!(coffee.insert_text.as_deref(), Some("coffee"));
        assert_eq!(coffee.filter_text.as_deref(), Some("coffee"));
    }

    #[test]
    fn test_detect_context_tag_after_semicolon_inside_string() {
        // The `;` lives inside the narration, so it is NOT a comment
        // marker and must not suppress tag completion (was a bug with
        // the naive `contains(';')` guard).
        assert_eq!(
            ctx_at_end("2024-01-15 * \"a;b\" #tr"),
            CompletionContext::Tag
        );
    }

    #[test]
    fn test_detect_context_escaped_quote_keeps_string_open() {
        // Literal line: 2024-01-15 * "a\"b #tag
        // The `\"` is an escaped quote, so the string is still open at
        // the `#`; this is inside a string, not a tag. A naive
        // quote-parity count (two `"` chars => even => "outside") would
        // wrongly treat it as code; the escape-aware scan does not.
        let ctx = ctx_at_end("2024-01-15 * \"a\\\"b #tag");
        assert_ne!(ctx, CompletionContext::Tag);
        assert_ne!(ctx, CompletionContext::Link);
    }

    #[test]
    fn test_in_code_position() {
        assert!(in_code_position("2024-01-15 * \"x\" #")); // after closed string
        assert!(in_code_position("pushtag #")); // plain directive
        assert!(!in_code_position("2024-01-15 * \"x\" ; ")); // in comment
        assert!(!in_code_position("2024-01-15 * \"open")); // in string
        assert!(in_code_position("2024-01-15 * \"a;b\" ")); // ; was in string
        assert!(!in_code_position("2024-01-15 * \"a\\\"b")); // escaped quote, still open
    }

    #[test]
    fn complete_link_returns_known_links() {
        let source = "\
2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Expenses:Stuff USD

2024-01-15 * \"Flight\" ^trip-2024
  Assets:Bank:Checking  -5 USD
  Expenses:Stuff
";
        let parsed = rustledger_parser::parse(source);
        assert!(
            parsed.errors.is_empty(),
            "fixture must parse: {:?}",
            parsed.errors
        );

        let items = complete_link(&parsed, None);
        let coffee = items.iter().find(|i| i.label == "^trip-2024");
        assert!(
            coffee.is_some(),
            "labels = {:?}",
            items.iter().map(|i| &i.label).collect::<Vec<_>>()
        );
        assert_eq!(coffee.unwrap().insert_text.as_deref(), Some("trip-2024"));
    }
}
