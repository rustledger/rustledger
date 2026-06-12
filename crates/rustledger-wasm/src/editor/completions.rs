//! Completion support for the editor.

#[cfg(test)]
use rustledger_parser::ParseResult;

use crate::types::{CompletionKind, EditorCompletion, EditorCompletionResult};

use super::helpers::{ACCOUNT_TYPES, DIRECTIVES, get_line, is_date_like};
use super::line_index::EditorCache;

/// Completion context detected from cursor position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletionContext {
    /// At the start of a line (expecting date or directive).
    LineStart,
    /// After a date (expecting directive keyword or flag).
    AfterDate,
    /// Expecting an account name.
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
    /// Unknown context.
    Unknown,
}

impl std::fmt::Display for CompletionContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LineStart => write!(f, "line_start"),
            Self::AfterDate => write!(f, "after_date"),
            Self::ExpectingAccount => write!(f, "expecting_account"),
            Self::AccountSegment { prefix } => write!(f, "account_segment:{prefix}"),
            Self::ExpectingCurrency => write!(f, "expecting_currency"),
            Self::InsideString => write!(f, "inside_string"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Get completions at the given position (using cached data).
pub fn get_completions_cached(
    source: &str,
    line: u32,
    character: u32,
    cache: &EditorCache,
) -> EditorCompletionResult {
    let context = detect_context(source, line, character);
    let completions = match &context {
        CompletionContext::LineStart => complete_line_start(),
        CompletionContext::AfterDate => complete_after_date(),
        CompletionContext::ExpectingAccount => complete_account_start_cached(&cache.accounts),
        CompletionContext::AccountSegment { prefix } => {
            complete_account_segment_cached(prefix, &cache.accounts)
        }
        CompletionContext::ExpectingCurrency => complete_currency_cached(&cache.currencies),
        CompletionContext::InsideString => complete_payee_cached(&cache.payees),
        CompletionContext::Unknown => Vec::new(),
    };

    EditorCompletionResult {
        completions,
        context: context.to_string(),
    }
}

/// Get completions at the given position (non-cached, used by tests).
#[cfg(test)]
pub fn get_completions(
    source: &str,
    line: u32,
    character: u32,
    parse_result: &ParseResult,
) -> EditorCompletionResult {
    let cache = EditorCache::new(source, parse_result);
    get_completions_cached(source, line, character, &cache)
}

/// Detect the completion context from cursor position.
pub fn detect_context(source: &str, line: u32, character: u32) -> CompletionContext {
    let line_text = get_line(source, line as usize);
    // `character` is a character offset, not a byte offset. Slicing
    // `line_text` by it directly panics when a multi-byte character
    // (e.g. a Korean Hangul syllable) sits before the cursor, because
    // the byte index lands mid-character — in the WASM build that
    // surfaces as an `unreachable` trap and kills completion (#1289).
    // Map the character offset to a char-boundary byte offset; clamp
    // past end-of-line to the line length.
    let col = character as usize;
    let byte_col = line_text
        .char_indices()
        .nth(col)
        .map_or(line_text.len(), |(b, _)| b);
    let before_cursor = &line_text[..byte_col];

    let trimmed = before_cursor.trim_start();

    // Check if we're at the start of a posting (indented line)
    if before_cursor.starts_with("  ") || before_cursor.starts_with('\t') {
        if trimmed.is_empty() {
            return CompletionContext::ExpectingAccount;
        }

        let posting_content = trimmed;

        // Check if there's already an account (contains colon and space after)
        if posting_content.contains(':') && posting_content.contains(' ') {
            let parts: Vec<&str> = posting_content.split_whitespace().collect();
            if parts.len() >= 2
                && let Some(last) = parts.last()
                && (last.parse::<f64>().is_ok() || last.ends_with('.'))
            {
                return CompletionContext::ExpectingCurrency;
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

        return CompletionContext::ExpectingAccount;
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
        for (directive, _) in DIRECTIVES {
            if let Some(rest) = after_date.strip_prefix(directive) {
                let after_directive = rest.trim_start();
                if after_directive.is_empty() || !after_directive.contains(' ') {
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

        return CompletionContext::AfterDate;
    }

    // Check if inside a quoted string
    let quote_count = before_cursor.chars().filter(|&c| c == '"').count();
    if quote_count % 2 == 1 {
        return CompletionContext::InsideString;
    }

    CompletionContext::Unknown
}

/// Complete at line start (date template).
pub fn complete_line_start() -> Vec<EditorCompletion> {
    let today = jiff::Zoned::now().date().to_string();
    vec![EditorCompletion {
        label: today.clone(),
        kind: CompletionKind::Date,
        detail: Some("Today's date".to_string()),
        insert_text: Some(format!("{today} ")),
    }]
}

/// Complete after a date (directive keywords).
pub fn complete_after_date() -> Vec<EditorCompletion> {
    DIRECTIVES
        .iter()
        .map(|(name, description)| EditorCompletion {
            label: (*name).to_string(),
            kind: CompletionKind::Keyword,
            detail: Some((*description).to_string()),
            insert_text: Some(format!("{name} ")),
        })
        .collect()
}

/// Complete account name start (account types) - cached version.
pub fn complete_account_start_cached(accounts: &[String]) -> Vec<EditorCompletion> {
    let mut items: Vec<EditorCompletion> = ACCOUNT_TYPES
        .iter()
        .map(|&t| EditorCompletion {
            label: format!("{t}:"),
            kind: CompletionKind::AccountSegment,
            detail: Some(format!("{t} account type")),
            insert_text: None,
        })
        .collect();

    // Also offer known accounts from the file
    for account in accounts.iter().take(20) {
        items.push(EditorCompletion {
            label: account.clone(),
            kind: CompletionKind::Account,
            detail: Some("Known account".to_string()),
            insert_text: None,
        });
    }

    items
}

/// Complete account segment after colon - cached version.
pub fn complete_account_segment_cached(prefix: &str, accounts: &[String]) -> Vec<EditorCompletion> {
    let matching: Vec<_> = accounts.iter().filter(|a| a.starts_with(prefix)).collect();

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
            let has_more = matching.iter().any(|a| a.starts_with(&format!("{full}:")));
            EditorCompletion {
                label: seg.clone(),
                kind: if has_more {
                    CompletionKind::AccountSegment
                } else {
                    CompletionKind::Account
                },
                detail: Some(if has_more {
                    "Account segment".to_string()
                } else {
                    "Account".to_string()
                }),
                insert_text: Some(if has_more { format!("{seg}:") } else { seg }),
            }
        })
        .collect()
}

/// Complete currency after amount - cached version.
pub fn complete_currency_cached(currencies: &[String]) -> Vec<EditorCompletion> {
    currencies
        .iter()
        .map(|c| EditorCompletion {
            label: c.clone(),
            kind: CompletionKind::Currency,
            detail: Some("Currency".to_string()),
            insert_text: None,
        })
        .collect()
}

/// Complete payee/narration inside string - cached version.
pub fn complete_payee_cached(payees: &[String]) -> Vec<EditorCompletion> {
    payees
        .iter()
        .take(20)
        .map(|p| EditorCompletion {
            label: p.clone(),
            kind: CompletionKind::Payee,
            detail: Some("Known payee".to_string()),
            insert_text: None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_detect_context_line_start() {
        let source = "\n";
        let ctx = detect_context(source, 0, 0);
        assert_eq!(ctx, CompletionContext::LineStart);
    }

    #[test]
    fn test_detect_context_after_date() {
        let source = "2024-01-15 ";
        let ctx = detect_context(source, 0, 11);
        assert_eq!(ctx, CompletionContext::AfterDate);
    }

    #[test]
    fn test_detect_context_expecting_account() {
        let source = "  ";
        let ctx = detect_context(source, 0, 2);
        assert_eq!(ctx, CompletionContext::ExpectingAccount);
    }

    #[test]
    fn test_detect_context_account_segment() {
        let source = "  Assets:";
        let ctx = detect_context(source, 0, 9);
        assert_eq!(
            ctx,
            CompletionContext::AccountSegment {
                prefix: "Assets:".to_string()
            }
        );
    }

    /// Regression for #1289: a partial non-ASCII (Korean) segment after
    /// a colon must not panic. `character` is a character offset; the
    /// "롯" is the 20th char (chars 0..18 = "  Liabilities:Card:", char
    /// 19 = "롯"), so the cursor after it is offset 20. Before the fix
    /// this sliced `line_text` at byte 20 — mid-"롯" — and panicked
    /// (an `unreachable` trap in WASM).
    #[test]
    fn test_detect_context_korean_partial_segment_no_panic() {
        let source = "  Liabilities:Card:롯";
        let ctx = detect_context(source, 0, 20);
        assert_eq!(
            ctx,
            CompletionContext::AccountSegment {
                prefix: "Liabilities:Card:".to_string()
            }
        );

        // Cursor at the colon (offset 19, before "롯") is the other
        // boundary case and must also be safe.
        let ctx_before = detect_context(source, 0, 19);
        assert_eq!(
            ctx_before,
            CompletionContext::AccountSegment {
                prefix: "Liabilities:Card:".to_string()
            }
        );
    }

    /// Regression for #1289 (sibling): a non-indented line beginning
    /// with a multi-byte character must not panic in the date-prefix
    /// check (`trimmed[..10]`).
    #[test]
    fn test_detect_context_multibyte_line_start_no_panic() {
        // 10+ bytes, byte 10 lands mid-character.
        let source = "롯롯롯롯 hello";
        let _ctx = detect_context(source, 0, 4);
    }

    #[test]
    fn test_get_completions_line_start() {
        let source = "";
        let result = parse(source);
        let completions = get_completions(source, 0, 0, &result);
        assert!(!completions.completions.is_empty());
        assert_eq!(completions.context, "line_start");
    }

    #[test]
    fn test_detect_context_inside_string() {
        // Test with odd number of quotes before cursor (inside string)
        let source = "text \"inside";
        let ctx = detect_context(source, 0, 10);
        assert_eq!(ctx, CompletionContext::InsideString);
    }

    #[test]
    fn test_detect_context_expecting_currency() {
        let source = "  Assets:Bank  100.00 ";
        let ctx = detect_context(source, 0, 22);
        assert_eq!(ctx, CompletionContext::ExpectingCurrency);
    }

    #[test]
    fn test_detect_context_unknown() {
        let source = "some random text";
        let ctx = detect_context(source, 0, 8);
        assert_eq!(ctx, CompletionContext::Unknown);
    }

    #[test]
    fn test_detect_context_after_directive_keyword() {
        let source = "2024-01-15 open ";
        let ctx = detect_context(source, 0, 16);
        assert_eq!(ctx, CompletionContext::ExpectingAccount);
    }

    #[test]
    fn test_completion_context_display() {
        assert_eq!(format!("{}", CompletionContext::LineStart), "line_start");
        assert_eq!(format!("{}", CompletionContext::AfterDate), "after_date");
        assert_eq!(
            format!("{}", CompletionContext::ExpectingAccount),
            "expecting_account"
        );
        assert_eq!(
            format!(
                "{}",
                CompletionContext::AccountSegment {
                    prefix: "Assets:".to_string()
                }
            ),
            "account_segment:Assets:"
        );
        assert_eq!(
            format!("{}", CompletionContext::ExpectingCurrency),
            "expecting_currency"
        );
        assert_eq!(
            format!("{}", CompletionContext::InsideString),
            "inside_string"
        );
        assert_eq!(format!("{}", CompletionContext::Unknown), "unknown");
    }

    #[test]
    fn test_complete_after_date_returns_all_directives() {
        let completions = complete_after_date();
        assert!(!completions.is_empty());

        let labels: Vec<_> = completions.iter().map(|c| c.label.as_str()).collect();
        assert!(labels.contains(&"open"));
        assert!(labels.contains(&"close"));
        assert!(labels.contains(&"balance"));
        assert!(labels.contains(&"*"));
        assert!(labels.contains(&"!"));
    }

    #[test]
    fn test_complete_account_segment_filters_by_prefix() {
        let accounts = vec![
            "Assets:Bank:Checking".to_string(),
            "Assets:Bank:Savings".to_string(),
            "Assets:Crypto".to_string(),
            "Expenses:Food".to_string(),
        ];

        let completions = complete_account_segment_cached("Assets:Bank:", &accounts);
        assert_eq!(completions.len(), 2);
        let labels: Vec<_> = completions.iter().map(|c| c.label.as_str()).collect();
        assert!(labels.contains(&"Checking"));
        assert!(labels.contains(&"Savings"));
    }
}
