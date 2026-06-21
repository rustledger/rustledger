//! Go-to-definition handler.
//!
//! Provides navigation to symbol definitions:
//! - Account → Open directive
//! - Currency → Commodity directive

use lsp_types::{GotoDefinitionParams, GotoDefinitionResponse, Location, Position, Range, Uri};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use crate::ledger_state::LedgerState;

use super::utils::{
    LineIndex, PositionEncoding, get_word_at_source_position, is_account_type, is_currency_like,
};

/// Handle a go-to-definition request.
pub fn handle_goto_definition(
    params: &GotoDefinitionParams,
    source: &str,
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
    uri: &Uri,
    encoding: PositionEncoding,
) -> Option<GotoDefinitionResponse> {
    let position = params.text_document_position_params.position;

    // Get the word at the cursor position
    let word = get_word_at_source_position(source, position, encoding)?;

    tracing::debug!("Go-to-definition for word: {:?}", word);

    // Build the line index once and share across both lookups.
    // Each `byte_offset_to_position` call is O(n) (linear scan from
    // byte 0); `LineIndex::offset_to_position` is O(log lines)
    // after a one-shot O(n) build.
    let line_index = LineIndex::new(source, encoding);

    let is_account = word.contains(':') || is_account_type(&word);

    // Check if it's an account name (current file first).
    if is_account
        && let Some(location) = find_account_definition(&word, parse_result, &line_index, uri)
    {
        return Some(GotoDefinitionResponse::Scalar(location));
    }

    // Cross-file fallback: the account may be opened in an `include`d file,
    // which the single-file `parse_result` above doesn't see.
    if is_account
        && let Some(state) = ledger_state
        && let Some((path, line)) = state.find_account_definition(&word)
        && let Some(location) = cross_file_location(&path, line)
    {
        return Some(GotoDefinitionResponse::Scalar(location));
    }

    // Check if it's a currency. Use the AST-validating
    // `is_currency_like` (not `_simple`) so words that look like
    // currencies but don't actually appear as `Currency` tokens
    // anywhere in the document short-circuit here instead of falling
    // through to `find_currency_definition` and then returning None.
    if is_currency_like(&word, parse_result)
        && let Some(location) = find_currency_definition(&word, parse_result, &line_index, uri)
    {
        return Some(GotoDefinitionResponse::Scalar(location));
    }

    None
}

/// Build a `Location` for a cross-file definition from the ledger's
/// `find_account_definition` result.
///
/// The stored line is **1-based** (`rustledger_loader`'s
/// `SourceFile::line_col` returns `line + 1`), while LSP positions are
/// **0-based**, hence `line - 1`. A zero-width range at column 0 makes the
/// editor jump to the start of the `open` line.
fn cross_file_location(path: &std::path::Path, line_1based: u32) -> Option<Location> {
    let uri: Uri = format!("file://{}", path.display()).parse().ok()?;
    let line = line_1based.saturating_sub(1);
    Some(Location {
        uri,
        range: Range {
            start: Position::new(line, 0),
            end: Position::new(line, 0),
        },
    })
}

/// Find the definition of an account (the Open directive).
///
/// Returns the whole Open directive's span. Most LSP clients
/// position the cursor at the range start, so the practical UX is
/// "jump to the start of `Open`". Narrowing to just the account-
/// name token would require per-field spans on `Open`, which
/// don't exist today.
fn find_account_definition(
    account: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    uri: &Uri,
) -> Option<Location> {
    for spanned_directive in &parse_result.directives {
        if let Directive::Open(open) = &spanned_directive.value {
            let open_account = open.account.as_ref();
            // Match exact account or `Open:account:Sub`-style prefix.
            // Pre-fix this branch did
            // `account.starts_with(&format!("{}:", open_account))`,
            // which allocated a new `String` per iteration. Using
            // `strip_prefix` + a `b':'` check keeps it allocation-
            // free.
            let prefix_match = account
                .strip_prefix(open_account)
                .is_some_and(|rest| rest.starts_with(':'));
            if account == open_account || prefix_match {
                let (start_line, start_col) =
                    line_index.offset_to_position(spanned_directive.span.start);
                let (end_line, end_col) = line_index.offset_to_position(spanned_directive.span.end);

                return Some(Location {
                    uri: uri.clone(),
                    range: Range {
                        start: Position::new(start_line, start_col),
                        end: Position::new(end_line, end_col),
                    },
                });
            }
        }
    }
    None
}

/// Find the definition of a currency (the declared `Currency` token
/// inside its `Commodity` directive).
///
/// Returns a Range covering exactly the declared currency token, not
/// the whole Commodity directive. With per-token precision the
/// editor highlights just `USD` when the user invokes "go to
/// definition" instead of a multi-line range (which is what we
/// returned previously, because Commodity directives can have an
/// indented metadata block).
///
/// The declared token is identified as the *first* `Currency` token
/// within the Commodity directive's span. The parser is strictly
/// forward-advancing and consumes the declared currency before the
/// indented metadata block, so the first-within-span occurrence is
/// unambiguously the declaration — same identification rule used by
/// `commodity_declaration_spans` for the references / document-
/// highlight handlers (see utils.rs).
fn find_currency_definition(
    currency: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    uri: &Uri,
) -> Option<Location> {
    let commodity_directive = parse_result.directives.iter().find(|d| {
        matches!(
            &d.value,
            Directive::Commodity(c) if c.currency.as_ref() == currency
        )
    })?;

    let declaration_token = parse_result.currency_occurrences.iter().find(|o| {
        o.span.start >= commodity_directive.span.start && o.span.end <= commodity_directive.span.end
    })?;

    let (start_line, start_col) = line_index.offset_to_position(declaration_token.span.start);
    let (end_line, end_col) = line_index.offset_to_position(declaration_token.span.end);

    Some(Location {
        uri: uri.clone(),
        range: Range {
            start: Position::new(start_line, start_col),
            end: Position::new(end_line, end_col),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    /// Regression test: go-to-definition on a currency must return
    /// a Range that covers exactly the declared currency token, not
    /// the whole Commodity directive.
    ///
    /// The previous implementation returned the directive's whole
    /// span, which for a Commodity with indented metadata spans
    /// multiple lines and renders awkwardly in editors that
    /// highlight the target range (e.g., a flash-highlight of the
    /// whole multi-line block instead of just the `USD` token).
    #[test]
    fn test_goto_definition_currency_returns_token_span() {
        let source = "\
2024-01-01 commodity USD
  name: \"United States Dollar\"
2024-01-15 * \"Coffee\"
  Assets:Bank  -5.00 USD
";
        let parse_result = parse(source);
        assert!(
            parse_result.errors.is_empty(),
            "parse errors: {:?}",
            parse_result.errors
        );
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        // Cursor on `USD` in `-5.00 USD` (line 3, col 21 — the `U`).
        let params = GotoDefinitionParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(3, 21),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let resp = handle_goto_definition(
            &params,
            source,
            &parse_result,
            None,
            &uri,
            PositionEncoding::Utf16,
        )
        .expect("definition returns Some");
        let loc = match resp {
            GotoDefinitionResponse::Scalar(l) => l,
            other => panic!("expected Scalar location; got {other:?}"),
        };

        // The declared `USD` token sits on line 0 at columns
        // 21..24 (after `2024-01-01 commodity `).
        // Pre-fix: range was the whole Commodity directive
        // (lines 0..2 — multi-line because of the metadata block).
        assert_eq!(loc.range.start, Position::new(0, 21));
        assert_eq!(loc.range.end, Position::new(0, 24));
    }

    /// `is_currency_like_simple` accepts anything matching
    /// `[A-Z0-9]{2,5}` — so `USDX` would pass the format check
    /// even if no commodity for it exists. The function must
    /// return None when the currency isn't declared, not panic or
    /// return a bogus location.
    #[test]
    fn test_goto_definition_currency_with_no_commodity_returns_none() {
        let source = "2024-01-15 * \"Coffee\"\n  Assets:Bank  -5.00 USD\n";
        let parse_result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        // Cursor on `USD`. There's no `commodity USD` directive.
        let params = GotoDefinitionParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(1, 21),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        assert!(
            handle_goto_definition(
                &params,
                source,
                &parse_result,
                None,
                &uri,
                PositionEncoding::Utf16
            )
            .is_none()
        );
    }

    #[test]
    fn cross_file_location_builds_uri_and_converts_line() {
        // `find_account_definition` returns a 1-based line (SourceFile::line_col);
        // the LSP Location must be 0-based, and the path becomes a file:// URI.
        let loc = cross_file_location(std::path::Path::new("/ledger/accounts.beancount"), 5)
            .expect("location");
        assert_eq!(loc.uri.as_str(), "file:///ledger/accounts.beancount");
        assert_eq!(loc.range.start, Position::new(4, 0)); // 5 (1-based) -> 4 (0-based)
        assert_eq!(loc.range.end, Position::new(4, 0));
        // Line 1 (1-based) clamps to 0, not underflow.
        let first = cross_file_location(std::path::Path::new("/a.beancount"), 1).unwrap();
        assert_eq!(first.range.start, Position::new(0, 0));
    }
}
