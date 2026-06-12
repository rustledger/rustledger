//! Completion support for the editor.
//!
//! Detection and candidate logic live in the editor-agnostic
//! `rustledger-completion` crate (issue #1319). This module is a thin
//! adapter: it maps the WASM character offset to a byte offset and
//! classifies the context via the shared crate, then maps the neutral
//! [`rustledger_completion::CompletionCandidate`] results into
//! [`EditorCompletion`] items (preserving the existing WASM item shapes
//! and gaining tag/link completion).

#[cfg(test)]
use rustledger_parser::ParseResult;

use rustledger_completion::{
    CompletionCandidate, CompletionKind as SharedKind, PositionEncoding, classify_context,
    offset_to_byte,
};

use crate::types::{CompletionKind, EditorCompletion, EditorCompletionResult};

use super::helpers::get_line;
use super::line_index::EditorCache;

/// Completion context detected from cursor position.
///
/// This mirrors [`rustledger_completion::CompletionContext`] (the shared
/// superset) but is a local type so it can carry the editor's `Display`
/// representation used in [`EditorCompletionResult::context`].
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
    /// Typing a tag (after `#`).
    Tag,
    /// Typing a link (after `^`).
    Link,
    /// Unknown context.
    Unknown,
}

impl From<rustledger_completion::CompletionContext> for CompletionContext {
    fn from(ctx: rustledger_completion::CompletionContext) -> Self {
        use rustledger_completion::CompletionContext as S;
        match ctx {
            S::LineStart => Self::LineStart,
            S::AfterDate => Self::AfterDate,
            S::ExpectingAccount => Self::ExpectingAccount,
            S::AccountSegment { prefix } => Self::AccountSegment { prefix },
            S::ExpectingCurrency => Self::ExpectingCurrency,
            S::InsideString => Self::InsideString,
            S::Tag => Self::Tag,
            S::Link => Self::Link,
            S::Unknown => Self::Unknown,
        }
    }
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
            Self::Tag => write!(f, "tag"),
            Self::Link => write!(f, "link"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Map a shared [`SharedKind`] to the WASM [`CompletionKind`],
/// reproducing the kinds the previous hand-written builders emitted.
fn editor_kind(kind: SharedKind) -> CompletionKind {
    match kind {
        SharedKind::Date => CompletionKind::Date,
        SharedKind::Directive => CompletionKind::Keyword,
        // Account types and folder segments were both `AccountSegment`.
        SharedKind::AccountType | SharedKind::AccountSegmentFolder => {
            CompletionKind::AccountSegment
        }
        SharedKind::Account => CompletionKind::Account,
        SharedKind::Currency => CompletionKind::Currency,
        SharedKind::Payee => CompletionKind::Payee,
        SharedKind::Tag => CompletionKind::Tag,
        SharedKind::Link => CompletionKind::Link,
    }
}

/// Map a neutral [`CompletionCandidate`] into an [`EditorCompletion`],
/// reproducing the existing WASM item shapes for the prior kinds.
fn to_completion(candidate: CompletionCandidate) -> EditorCompletion {
    let CompletionCandidate {
        label,
        insert_text,
        kind,
        detail,
    } = candidate;

    // The previous WASM builders left `insert_text` as `None` for the
    // account-type / known-account / currency / payee items (the label
    // is inserted verbatim). The shared candidate sets
    // `insert_text == label` for those, so suppress it to match.
    let insert_text = match kind {
        SharedKind::AccountType
        | SharedKind::Account
        | SharedKind::Currency
        | SharedKind::Payee => None,
        SharedKind::Date
        | SharedKind::Directive
        | SharedKind::AccountSegmentFolder
        | SharedKind::Tag
        | SharedKind::Link => Some(insert_text),
    };

    EditorCompletion {
        label,
        kind: editor_kind(kind),
        detail,
        insert_text,
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
    let candidates = match &context {
        CompletionContext::LineStart => {
            let today = jiff::Zoned::now().date().to_string();
            rustledger_completion::line_start_candidates(&today)
        }
        CompletionContext::AfterDate => rustledger_completion::after_date_candidates(),
        CompletionContext::ExpectingAccount => {
            rustledger_completion::account_start_candidates(&cache.accounts)
        }
        CompletionContext::AccountSegment { prefix } => {
            rustledger_completion::account_segment_candidates(prefix, &cache.accounts)
        }
        CompletionContext::ExpectingCurrency => {
            rustledger_completion::currency_candidates(&cache.currencies)
        }
        CompletionContext::InsideString => rustledger_completion::payee_candidates(&cache.payees),
        CompletionContext::Tag => rustledger_completion::tag_candidates(&cache.tags),
        CompletionContext::Link => rustledger_completion::link_candidates(&cache.links),
        CompletionContext::Unknown => Vec::new(),
    };

    let completions = candidates.into_iter().map(to_completion).collect();

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
///
/// `character` is a character offset (not a byte offset); the shared
/// `offset_to_byte` maps it to a char-boundary byte offset (preserving
/// the #1289 fix), then `classify_context` classifies the text before
/// the cursor.
pub fn detect_context(source: &str, line: u32, character: u32) -> CompletionContext {
    let line_text = get_line(source, line as usize);
    let byte_col = offset_to_byte(line_text, character as usize, PositionEncoding::Char);
    classify_context(&line_text[..byte_col]).into()
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
        let completions = rustledger_completion::after_date_candidates();
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

        let completions =
            rustledger_completion::account_segment_candidates("Assets:Bank:", &accounts);
        assert_eq!(completions.len(), 2);
        let labels: Vec<_> = completions.iter().map(|c| c.label.as_str()).collect();
        assert!(labels.contains(&"Checking"));
        assert!(labels.contains(&"Savings"));
    }

    /// WASM now offers tag completion (issue #1319): typing `#` on a
    /// transaction header yields the known tags, with the sigil kept in
    /// the label but dropped from the inserted text.
    #[test]
    fn test_tag_completion_offered() {
        let source = "\
2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Expenses:Stuff USD

2024-01-15 * \"Central Perk\" #coffee #morning
  Assets:Bank:Checking  -5 USD
  Expenses:Stuff
";
        let result = parse(source);
        // Cursor right after a fresh `#` on a new transaction header.
        let header = "2024-02-01 * \"x\" #";
        let mut doc = String::from(source);
        doc.push_str(header);
        let line = doc.lines().count() as u32 - 1;
        let character = header.chars().count() as u32;
        let completions = get_completions(&doc, line, character, &result);

        assert_eq!(completions.context, "tag");
        let labels: Vec<_> = completions
            .completions
            .iter()
            .map(|c| c.label.as_str())
            .collect();
        assert!(labels.contains(&"#coffee"), "labels = {labels:?}");
        assert!(labels.contains(&"#morning"), "labels = {labels:?}");

        let coffee = completions
            .completions
            .iter()
            .find(|c| c.label == "#coffee")
            .unwrap();
        assert_eq!(coffee.kind, CompletionKind::Tag);
        assert_eq!(coffee.insert_text.as_deref(), Some("coffee"));
    }

    /// WASM now offers link completion (issue #1319).
    #[test]
    fn test_link_completion_offered() {
        let source = "\
2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Expenses:Stuff USD

2024-01-15 * \"Flight\" ^trip-2024
  Assets:Bank:Checking  -5 USD
  Expenses:Stuff
";
        let result = parse(source);
        let header = "2024-02-01 * \"x\" ^";
        let mut doc = String::from(source);
        doc.push_str(header);
        let line = doc.lines().count() as u32 - 1;
        let character = header.chars().count() as u32;
        let completions = get_completions(&doc, line, character, &result);

        assert_eq!(completions.context, "link");
        let trip = completions
            .completions
            .iter()
            .find(|c| c.label == "^trip-2024")
            .expect("trip-2024 link should be offered");
        assert_eq!(trip.kind, CompletionKind::Link);
        assert_eq!(trip.insert_text.as_deref(), Some("trip-2024"));
    }
}
