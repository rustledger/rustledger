//! Semantic tokens handler for enhanced syntax highlighting.
//!
//! Uses lexer tokens as the baseline for highlighting, ensuring correct
//! positions and unbreakable highlighting even when parse errors occur.
//! Optionally enriches with directive-level semantics (definition/deprecated
//! modifiers) when parsing succeeds.
//!
//! Supports full document, range-based, and delta tokenization.

use lsp_types::{
    Range, SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokens,
    SemanticTokensDelta, SemanticTokensDeltaParams, SemanticTokensEdit,
    SemanticTokensFullDeltaResult, SemanticTokensFullOptions, SemanticTokensLegend,
    SemanticTokensOptions, SemanticTokensParams, SemanticTokensRangeParams,
    SemanticTokensRangeResult, SemanticTokensResult, SemanticTokensServerCapabilities,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use rustledger_parser::logos_lexer::{Token, tokenize};
use std::sync::atomic::{AtomicU64, Ordering};

use super::utils::{LineIndex, PositionEncoding};

/// Token types we support.
pub const TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::KEYWORD,   // 0: directive keywords (open, close, etc.)
    SemanticTokenType::NUMBER,    // 1: amounts
    SemanticTokenType::STRING,    // 2: payees, narrations
    SemanticTokenType::VARIABLE,  // 3: accounts
    SemanticTokenType::TYPE,      // 4: currencies
    SemanticTokenType::COMMENT,   // 5: comments
    SemanticTokenType::OPERATOR,  // 6: flags (*, !)
    SemanticTokenType::MACRO,     // 7: dates
    SemanticTokenType::DECORATOR, // 8: tags and links
];

/// Token modifiers we support.
pub const TOKEN_MODIFIERS: &[SemanticTokenModifier] = &[
    SemanticTokenModifier::DEFINITION, // 0: where something is defined
    SemanticTokenModifier::DEPRECATED, // 1: closed accounts
    SemanticTokenModifier::READONLY,   // 2: balance assertions
];

/// Get the semantic tokens legend for capability registration.
pub fn get_legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: TOKEN_TYPES.to_vec(),
        token_modifiers: TOKEN_MODIFIERS.to_vec(),
    }
}

/// Counter for generating unique result IDs.
static RESULT_ID_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Generate a new unique result ID.
fn generate_result_id() -> String {
    RESULT_ID_COUNTER.fetch_add(1, Ordering::SeqCst).to_string()
}

/// Get the semantic tokens server capabilities.
pub fn get_capabilities() -> SemanticTokensServerCapabilities {
    SemanticTokensServerCapabilities::SemanticTokensOptions(SemanticTokensOptions {
        legend: get_legend(),
        full: Some(SemanticTokensFullOptions::Delta { delta: Some(true) }),
        range: Some(true),
        work_done_progress_options: Default::default(),
    })
}

/// Token type indices.
mod token_type {
    pub const KEYWORD: u32 = 0;
    pub const NUMBER: u32 = 1;
    pub const STRING: u32 = 2;
    pub const VARIABLE: u32 = 3; // accounts
    pub const TYPE: u32 = 4; // currencies
    pub const COMMENT: u32 = 5;
    pub const OPERATOR: u32 = 6; // flags
    pub const MACRO: u32 = 7; // dates
    pub const DECORATOR: u32 = 8; // tags, links
}

/// Token modifier bits.
mod token_modifier {
    pub const DEFINITION: u32 = 1 << 0;
    pub const DEPRECATED: u32 = 1 << 1;
}

/// A raw token before delta encoding.
struct RawToken {
    line: u32,
    start: u32,
    length: u32,
    token_type: u32,
    modifiers: u32,
    /// Byte offset in source (used for modifier overlay matching).
    byte_offset: usize,
}

/// Map a lexer token to a semantic token type, if applicable.
fn lexer_token_type(token: &Token) -> Option<u32> {
    match token {
        Token::Date(_) => Some(token_type::MACRO),
        Token::Number(_) => Some(token_type::NUMBER),
        Token::String(_) => Some(token_type::STRING),
        Token::Account(_) => Some(token_type::VARIABLE),
        Token::Currency(_) => Some(token_type::TYPE),
        Token::Tag(_) => Some(token_type::DECORATOR),
        Token::Link(_) => Some(token_type::DECORATOR),
        Token::Comment(_) => Some(token_type::COMMENT),

        // Keywords
        Token::Txn
        | Token::Balance
        | Token::Open
        | Token::Close
        | Token::Commodity
        | Token::Pad
        | Token::Event
        | Token::Query
        | Token::Note
        | Token::Document
        | Token::Price
        | Token::Custom
        | Token::Option_
        | Token::Include
        | Token::Plugin
        | Token::Pushtag
        | Token::Poptag
        | Token::Pushmeta
        | Token::Popmeta => Some(token_type::KEYWORD),

        // Boolean/null literals
        Token::True | Token::False | Token::Null => Some(token_type::KEYWORD),

        // Flags
        Token::Star | Token::Pending | Token::Flag(_) => Some(token_type::OPERATOR),

        // Punctuation and structural tokens — no highlighting
        _ => None,
    }
}

/// Length of `s` in the negotiated LSP position encoding.
///
/// Under [`PositionEncoding::Utf8`] this is the byte length;
/// under [`PositionEncoding::Utf16`] it is the UTF-16 code-unit count
/// (so non-BMP scalars contribute 2). Used to emit semantic-token
/// column offsets and lengths in the wire encoding the client
/// negotiated.
fn encoded_len(s: &str, encoding: PositionEncoding) -> u32 {
    match encoding {
        PositionEncoding::Utf8 => s.len() as u32,
        PositionEncoding::Utf16 => s.chars().map(|c| c.len_utf16() as u32).sum::<u32>(),
    }
}

/// Collect raw tokens from the lexer output for a source string.
fn collect_lexer_tokens(source: &str, encoding: PositionEncoding) -> Vec<RawToken> {
    let lexer_tokens = tokenize(source);
    let mut raw_tokens = Vec::with_capacity(lexer_tokens.len());

    // Build line start offsets for O(1) byte-to-line/col conversion.
    let line_starts: Vec<usize> = std::iter::once(0)
        .chain(source.match_indices('\n').map(|(i, _)| i + 1))
        .collect();

    for (token, span) in &lexer_tokens {
        if let Some(tt) = lexer_token_type(token) {
            // Binary search for the line containing this byte offset.
            let line_idx = line_starts.partition_point(|&start| start <= span.start) - 1;
            let line = line_idx as u32;
            // Convert byte offset within line to the negotiated wire
            // encoding (UTF-16 by default; UTF-8 byte offsets if the
            // client negotiated UTF-8 at initialization).
            let line_start = line_starts[line_idx];
            let col = encoded_len(&source[line_start..span.start], encoding);
            let length = encoded_len(&source[span.start..span.end], encoding);
            raw_tokens.push(RawToken {
                line,
                start: col,
                length,
                token_type: tt,
                modifiers: 0,
                byte_offset: span.start,
            });
        }
    }

    raw_tokens
}

/// Collect raw tokens from the lexer, restricted to a line range.
///
/// Runs the full lexer (Logos doesn't support partial input) but only builds
/// `RawToken`s for tokens within the requested range, skipping the UTF-16
/// column computation for out-of-range tokens.
fn collect_lexer_tokens_in_range(
    source: &str,
    range: &Range,
    encoding: PositionEncoding,
) -> Vec<RawToken> {
    let lexer_tokens = tokenize(source);

    let line_starts: Vec<usize> = std::iter::once(0)
        .chain(source.match_indices('\n').map(|(i, _)| i + 1))
        .collect();

    // Convert range lines to byte offsets for fast filtering.
    let range_start_byte = line_starts
        .get(range.start.line as usize)
        .copied()
        .unwrap_or(0);
    let range_end_byte = line_starts
        .get(range.end.line as usize + 1)
        .copied()
        .unwrap_or(source.len());

    let mut raw_tokens = Vec::new();

    for (token, span) in &lexer_tokens {
        // Skip tokens entirely before or after the range.
        if span.end <= range_start_byte || span.start >= range_end_byte {
            continue;
        }

        if let Some(tt) = lexer_token_type(token) {
            let line_idx = line_starts.partition_point(|&start| start <= span.start) - 1;
            let line = line_idx as u32;
            let line_start = line_starts[line_idx];
            let col = encoded_len(&source[line_start..span.start], encoding);
            let length = encoded_len(&source[span.start..span.end], encoding);

            let raw = RawToken {
                line,
                start: col,
                length,
                token_type: tt,
                modifiers: 0,
                byte_offset: span.start,
            };

            if is_token_in_range(&raw, range) {
                raw_tokens.push(raw);
            }
        }
    }

    raw_tokens
}

/// Apply directive-level semantic modifiers to raw tokens.
///
/// Walks parsed directives and sets modifiers on matching tokens:
/// - `open` directive accounts get DEFINITION modifier
/// - `close` directive accounts get DEPRECATED modifier
fn apply_directive_modifiers(
    raw_tokens: &mut [RawToken],
    source: &str,
    line_index: &LineIndex,
    parse_result: &ParseResult,
) {
    for spanned in &parse_result.directives {
        let (dir_line, _) = line_index.offset_to_position(spanned.span.start);

        match &spanned.value {
            Directive::Open(open) => {
                // Find the account token on this line and mark as DEFINITION
                let account_str = open.account.as_str();
                for tok in raw_tokens.iter_mut() {
                    if tok.line == dir_line
                        && tok.token_type == token_type::VARIABLE
                        && source_slice_matches(source, tok, account_str)
                    {
                        tok.modifiers |= token_modifier::DEFINITION;
                        break;
                    }
                }
            }
            Directive::Close(close) => {
                // Find the account token on this line and mark as DEPRECATED
                let account_str = close.account.as_str();
                for tok in raw_tokens.iter_mut() {
                    if tok.line == dir_line
                        && tok.token_type == token_type::VARIABLE
                        && source_slice_matches(source, tok, account_str)
                    {
                        tok.modifiers |= token_modifier::DEPRECATED;
                        break;
                    }
                }
            }
            Directive::Commodity(comm) => {
                // Mark the currency on this line as DEFINITION
                let currency_str = comm.currency.as_str();
                for tok in raw_tokens.iter_mut() {
                    if tok.line == dir_line
                        && tok.token_type == token_type::TYPE
                        && source_slice_matches(source, tok, currency_str)
                    {
                        tok.modifiers |= token_modifier::DEFINITION;
                        break;
                    }
                }
            }
            _ => {}
        }
    }
}

/// Check if a raw token's source text matches a given string.
fn source_slice_matches(source: &str, token: &RawToken, expected: &str) -> bool {
    source[token.byte_offset..].starts_with(expected)
}

/// Convert raw tokens to delta-encoded semantic tokens.
fn encode_tokens(raw_tokens: &[RawToken]) -> Vec<SemanticToken> {
    let mut tokens = Vec::with_capacity(raw_tokens.len());
    let mut prev_line = 0u32;
    let mut prev_start = 0u32;

    for raw in raw_tokens {
        let delta_line = raw.line - prev_line;
        let delta_start = if delta_line == 0 {
            raw.start - prev_start
        } else {
            raw.start
        };

        tokens.push(SemanticToken {
            delta_line,
            delta_start,
            length: raw.length,
            token_type: raw.token_type,
            token_modifiers_bitset: raw.modifiers,
        });

        prev_line = raw.line;
        prev_start = raw.start;
    }

    tokens
}

/// Handle a semantic tokens request.
pub fn handle_semantic_tokens(
    _params: &SemanticTokensParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<SemanticTokensResult> {
    let mut raw_tokens = collect_lexer_tokens(source, encoding);
    let line_index = LineIndex::new(source, encoding);
    apply_directive_modifiers(&mut raw_tokens, source, &line_index, parse_result);

    // Tokens are already in source order from the lexer
    let tokens = encode_tokens(&raw_tokens);

    if tokens.is_empty() {
        None
    } else {
        Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: Some(generate_result_id()),
            data: tokens,
        }))
    }
}

/// Handle a semantic tokens delta request.
pub fn handle_semantic_tokens_delta(
    params: &SemanticTokensDeltaParams,
    source: &str,
    parse_result: &ParseResult,
    previous_tokens: Option<&[SemanticToken]>,
    encoding: PositionEncoding,
) -> Option<SemanticTokensFullDeltaResult> {
    let mut raw_tokens = collect_lexer_tokens(source, encoding);
    let line_index = LineIndex::new(source, encoding);
    apply_directive_modifiers(&mut raw_tokens, source, &line_index, parse_result);
    let current_tokens = encode_tokens(&raw_tokens);

    // If tokens unchanged, return empty delta
    if let Some(prev) = previous_tokens
        && tokens_equal(prev, &current_tokens)
    {
        return Some(SemanticTokensFullDeltaResult::TokensDelta(
            SemanticTokensDelta {
                result_id: Some(generate_result_id()),
                edits: vec![],
            },
        ));
    }

    let _ = params;

    if current_tokens.is_empty() && previous_tokens.is_none_or(|t| t.is_empty()) {
        return None;
    }

    let prev_len = previous_tokens.map(|t| t.len()).unwrap_or(0);

    Some(SemanticTokensFullDeltaResult::TokensDelta(
        SemanticTokensDelta {
            result_id: Some(generate_result_id()),
            edits: vec![SemanticTokensEdit {
                start: 0,
                delete_count: prev_len as u32,
                data: Some(current_tokens),
            }],
        },
    ))
}

/// Check if two token arrays are equal.
fn tokens_equal(a: &[SemanticToken], b: &[SemanticToken]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b.iter()).all(|(x, y)| {
        x.delta_line == y.delta_line
            && x.delta_start == y.delta_start
            && x.length == y.length
            && x.token_type == y.token_type
            && x.token_modifiers_bitset == y.token_modifiers_bitset
    })
}

/// Handle a semantic tokens range request.
///
/// Only builds `RawToken`s for lexer tokens whose byte offset falls within
/// the requested line range, avoiding UTF-16 column computation for tokens
/// outside the visible area.
pub fn handle_semantic_tokens_range(
    params: &SemanticTokensRangeParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<SemanticTokensRangeResult> {
    let range = params.range;

    let mut raw_tokens = collect_lexer_tokens_in_range(source, &range, encoding);
    let line_index = LineIndex::new(source, encoding);
    apply_directive_modifiers(&mut raw_tokens, source, &line_index, parse_result);

    let tokens = encode_tokens(&raw_tokens);

    if tokens.is_empty() {
        None
    } else {
        Some(SemanticTokensRangeResult::Tokens(SemanticTokens {
            result_id: None,
            data: tokens,
        }))
    }
}

/// Check if a token is within the requested range.
fn is_token_in_range(token: &RawToken, range: &Range) -> bool {
    if token.line < range.start.line || token.line > range.end.line {
        return false;
    }
    if token.line == range.start.line && token.start < range.start.character {
        return false;
    }
    if token.line == range.end.line && token.start + token.length > range.end.character {
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_semantic_tokens_basic() {
        let source = "2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);
        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            // Should have tokens for: date, keyword(open), account, currency
            assert!(tokens.data.len() >= 4);
        }
    }

    #[test]
    fn test_semantic_tokens_with_parse_error() {
        // Even with a parse error, lexer tokens should still provide highlighting
        let source = "2024-01-01 open Assets:Bank USD\n2024-01-15 INVALID_DIRECTIVE\n2024-01-20 close Assets:OldAccount\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            // Should still have tokens from all three lines (dates at minimum)
            let date_tokens: Vec<_> = tokens
                .data
                .iter()
                .filter(|t| t.token_type == token_type::MACRO)
                .collect();
            assert!(
                date_tokens.len() >= 3,
                "Should have date tokens from all 3 lines, got {}",
                date_tokens.len()
            );
        }
    }

    #[test]
    fn test_semantic_tokens_comments() {
        let source = "; This is a comment\n2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            // Should have a comment token
            assert!(
                tokens
                    .data
                    .iter()
                    .any(|t| t.token_type == token_type::COMMENT),
                "Should have comment token"
            );
        }
    }

    #[test]
    fn test_semantic_tokens_tags_links() {
        let source =
            "2024-01-15 * \"Coffee\" #tag1 ^link1\n  Expenses:Food  5.00 USD\n  Assets:Bank\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            // Should have decorator tokens for tag and link
            let decorator_count = tokens
                .data
                .iter()
                .filter(|t| t.token_type == token_type::DECORATOR)
                .count();
            assert!(
                decorator_count >= 2,
                "Should have at least 2 decorator tokens (tag + link), got {decorator_count}"
            );
        }
    }

    #[test]
    fn test_open_has_definition_modifier() {
        let source = "2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            // Find the account token and check it has DEFINITION modifier
            let account_token = tokens
                .data
                .iter()
                .find(|t| t.token_type == token_type::VARIABLE);
            assert!(account_token.is_some(), "Should have account token");
            assert_eq!(
                account_token.unwrap().token_modifiers_bitset & token_modifier::DEFINITION,
                token_modifier::DEFINITION,
                "Account in open directive should have DEFINITION modifier"
            );
        }
    }

    #[test]
    fn test_close_has_deprecated_modifier() {
        let source = "2024-01-01 close Assets:OldAccount\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            let account_token = tokens
                .data
                .iter()
                .find(|t| t.token_type == token_type::VARIABLE);
            assert!(account_token.is_some());
            assert_eq!(
                account_token.unwrap().token_modifiers_bitset & token_modifier::DEPRECATED,
                token_modifier::DEPRECATED,
                "Account in close directive should have DEPRECATED modifier"
            );
        }
    }

    #[test]
    fn test_semantic_tokens_range() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-20 close Assets:OldAccount
"#;
        let result = parse(source);

        let params = SemanticTokensRangeParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: Range {
                start: lsp_types::Position::new(1, 0),
                end: lsp_types::Position::new(3, 100),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response =
            handle_semantic_tokens_range(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensRangeResult::Tokens(tokens)) = response {
            assert!(!tokens.data.is_empty());
        }
    }

    #[test]
    fn test_semantic_tokens_delta_no_change() {
        let source = "2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let initial = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        let initial_tokens = match initial {
            Some(SemanticTokensResult::Tokens(t)) => t.data,
            _ => panic!("Expected tokens"),
        };

        let delta_params = SemanticTokensDeltaParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            previous_result_id: "0".to_string(),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let delta = handle_semantic_tokens_delta(
            &delta_params,
            source,
            &result,
            Some(&initial_tokens),
            PositionEncoding::Utf16,
        );
        assert!(delta.is_some());

        if let Some(SemanticTokensFullDeltaResult::TokensDelta(d)) = delta {
            assert!(d.edits.is_empty());
        } else {
            panic!("Expected delta result");
        }
    }

    #[test]
    fn test_is_token_in_range() {
        let token = RawToken {
            line: 5,
            start: 10,
            length: 5,
            token_type: 0,
            modifiers: 0,
            byte_offset: 0,
        };

        let range = Range {
            start: lsp_types::Position::new(0, 0),
            end: lsp_types::Position::new(10, 100),
        };
        assert!(is_token_in_range(&token, &range));

        let range = Range {
            start: lsp_types::Position::new(6, 0),
            end: lsp_types::Position::new(10, 100),
        };
        assert!(!is_token_in_range(&token, &range));
    }

    #[test]
    fn test_tokens_equal() {
        let tokens1 = vec![SemanticToken {
            delta_line: 0,
            delta_start: 0,
            length: 10,
            token_type: 0,
            token_modifiers_bitset: 0,
        }];
        let tokens2 = tokens1.clone();
        let tokens3 = vec![SemanticToken {
            delta_line: 0,
            delta_start: 0,
            length: 11,
            token_type: 0,
            token_modifiers_bitset: 0,
        }];

        assert!(tokens_equal(&tokens1, &tokens2));
        assert!(!tokens_equal(&tokens1, &tokens3));
        assert!(!tokens_equal(&tokens1, &[]));
    }

    #[test]
    fn test_semantic_tokens_multibyte_positions() {
        // CJK narration — token positions must use UTF-16 code units, not bytes.
        let source = "2024-01-15 * \"午餐\"\n  Expenses:Food  10 USD\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some(), "should produce tokens for CJK source");

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            let account_tokens: Vec<_> = tokens
                .data
                .iter()
                .filter(|t| t.token_type == token_type::VARIABLE)
                .collect();
            assert!(
                !account_tokens.is_empty(),
                "should have account tokens even with CJK narration"
            );
        }
    }

    #[test]
    fn test_semantic_tokens_emoji_utf16_positions() {
        // Non-BMP emoji: 😀 is 4 bytes UTF-8 but 2 UTF-16 code units.
        // Verify token positions are in UTF-16 code units, not bytes.
        let source = "; 😀 comment\n2024-01-15 * \"😀\" #tag\n";
        let result = parse(source);

        let params = SemanticTokensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_semantic_tokens(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(SemanticTokensResult::Tokens(tokens)) = response {
            // Reconstruct absolute positions from delta encoding
            let mut absolute = Vec::new();
            let mut line = 0u32;
            let mut start = 0u32;
            for t in &tokens.data {
                line += t.delta_line;
                start = if t.delta_line == 0 {
                    start + t.delta_start
                } else {
                    t.delta_start
                };
                absolute.push((line, start, t.length, t.token_type));
            }

            // Comment on line 0: "; 😀 comment" = 12 UTF-16 code units
            let comment = absolute
                .iter()
                .find(|t| t.0 == 0 && t.3 == token_type::COMMENT);
            assert!(comment.is_some(), "should have comment token");
            assert_eq!(
                comment.unwrap().2,
                "; 😀 comment".encode_utf16().count() as u32,
                "comment length should be in UTF-16 code units"
            );

            // Tag on line 1: starts after "2024-01-15 * \"😀\" "
            let tag = absolute
                .iter()
                .find(|t| t.0 == 1 && t.3 == token_type::DECORATOR);
            assert!(tag.is_some(), "should have tag token");
            assert_eq!(
                tag.unwrap().1,
                "2024-01-15 * \"😀\" ".encode_utf16().count() as u32,
                "tag start should be in UTF-16 code units"
            );
        }
    }
}
