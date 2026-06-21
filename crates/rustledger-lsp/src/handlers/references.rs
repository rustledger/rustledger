//! Find references handler for locating all usages.
//!
//! Provides references for:
//! - Account names (all usages across directives)
//! - Currency names (all usages across directives)
//! - Payees (all transactions with same payee)

use super::utils::{
    LineIndex, PositionEncoding, account_declaration_spans, commodity_declaration_spans,
    get_word_at_position, is_account_like, is_currency_like,
};
use lsp_types::{Location, Position, Range, ReferenceParams, Uri};
use rustledger_core::Directive;
use rustledger_parser::{ParseResult, parse};

/// Which kind of symbol references are being collected.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RefKind {
    Account,
    Currency,
    Payee,
}

/// Handle a find references request.
pub fn handle_references(
    params: &ReferenceParams,
    source: &str,
    parse_result: &ParseResult,
    // Other ledger files reachable via `include` (everything except the current
    // buffer), as `(uri, source)` with live content for open buffers. Gathered
    // by the caller under the state lock so parsing here holds no locks. So
    // "find references" spans the whole ledger, not just the open file.
    other_files: &[(Uri, String)],
    uri: &Uri,
    encoding: PositionEncoding,
) -> Option<Vec<Location>> {
    let position = params.text_document_position.position;
    let include_declaration = params.context.include_declaration;

    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, _, _) = get_word_at_position(line, position.character as usize, encoding)?;

    // Classify the symbol kind from the cursor's file (account / currency /
    // payee), then collect that kind's occurrences across every ledger file.
    let kind = if is_account_like(&word) {
        RefKind::Account
    } else if is_currency_like(&word, parse_result) {
        RefKind::Currency
    } else if is_in_quotes(line, position.character as usize) {
        RefKind::Payee
    } else {
        return None;
    };

    // Collect references from a single file into its own vec (each collector
    // sorts/dedups within the file). Returns the file's locations.
    let collect_file = |src: &str, pr: &ParseResult, file_uri: &Uri| -> Vec<Location> {
        let line_index = LineIndex::new(src, encoding);
        let mut out = Vec::new();
        match kind {
            RefKind::Account => {
                collect_account_references(
                    pr,
                    &line_index,
                    &word,
                    file_uri,
                    include_declaration,
                    &mut out,
                );
            }
            RefKind::Currency => {
                collect_currency_references(
                    pr,
                    &line_index,
                    &word,
                    file_uri,
                    include_declaration,
                    &mut out,
                );
            }
            RefKind::Payee => {
                collect_payee_references(src, pr, &line_index, &word, file_uri, &mut out);
            }
        }
        out
    };

    let mut locations = collect_file(source, parse_result, uri);
    for (f_uri, f_source) in other_files {
        if f_uri == uri {
            continue; // current file already collected from its live source
        }
        let f_parse = parse(f_source);
        locations.extend(collect_file(f_source, &f_parse, f_uri));
    }

    // Final cross-file dedup keyed by (uri, range) — the per-file collectors
    // only dedup by range, so two files with a same-positioned occurrence must
    // not collapse into one.
    locations.sort_by(|a, b| {
        a.uri
            .as_str()
            .cmp(b.uri.as_str())
            .then(a.range.start.line.cmp(&b.range.start.line))
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    locations.dedup_by(|a, b| a.uri == b.uri && a.range == b.range);

    if locations.is_empty() {
        None
    } else {
        Some(locations)
    }
}

/// Collect all references to an account.
///
/// Walks the parser's `account_occurrences` index (every `ACCOUNT`
/// token with exact source spans) and emits one `Location` per
/// occurrence matching `account`. The previous shape walked the
/// typed directives and ran a substring search inside each
/// directive's source bytes, which produced false positives in
/// payee strings, comments, and STRING-typed metadata values
/// containing the account name as a substring (e.g.
/// `2024-01-15 * "Assets:Bank transfer"` with a real
/// `Assets:Bank` posting in the same transaction).
///
/// To honor `include_declaration`, we look up declared-account
/// tokens (the `Open` and `Close` directive headers — both are
/// lifecycle-boundary "declarations" in the LSP sense) via
/// [`account_declaration_spans`] - same shape as the
/// currency-references path's use of `commodity_declaration_spans`.
fn collect_account_references(
    parse_result: &ParseResult,
    line_index: &LineIndex,
    account: &str,
    uri: &Uri,
    include_declaration: bool,
    locations: &mut Vec<Location>,
) {
    let declaration_spans = account_declaration_spans(parse_result);

    for occurrence in &parse_result.account_occurrences {
        if occurrence.value != account {
            continue;
        }
        let is_declaration = declaration_spans.contains(&occurrence.span);
        if is_declaration && !include_declaration {
            continue;
        }
        let (start_line, start_col) = line_index.offset_to_position(occurrence.span.start);
        let (end_line, end_col) = line_index.offset_to_position(occurrence.span.end);
        locations.push(Location {
            uri: uri.clone(),
            range: Range {
                start: Position::new(start_line, start_col),
                end: Position::new(end_line, end_col),
            },
        });
    }

    // Defensive dedup, same shape as the currency path - see
    // `collect_currency_references` for why this guard is here.
    locations.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    locations.dedup_by(|a, b| a.range == b.range);
}

/// Collect all references to a currency.
///
/// Walks the parser's `currency_occurrences` index (every `Currency`
/// token with exact source spans) and emits one `Location` per
/// occurrence matching `currency`. The previous implementation
/// string-searched the source within each directive, which produced
/// false positives in payee strings, comments, and account-name
/// segments containing the currency code.
///
/// To honor `include_declaration`, we look up the *declared*
/// currency token in each `Commodity` directive via
/// `commodity_declaration_spans` — which returns the first
/// `Currency` token within each Commodity's source span. A
/// containment check ("occurrence span ⊆ Commodity directive
/// span") is NOT sufficient here, because Commodity directives can
/// have metadata whose values tokenize as `Currency` (e.g.
/// `alias: EUR`); a containment check would misclassify those as
/// declarations.
fn collect_currency_references(
    parse_result: &ParseResult,
    line_index: &LineIndex,
    currency: &str,
    uri: &Uri,
    include_declaration: bool,
    locations: &mut Vec<Location>,
) {
    let declaration_spans = commodity_declaration_spans(parse_result);

    for occurrence in &parse_result.currency_occurrences {
        if occurrence.value != currency {
            continue;
        }
        let is_declaration = declaration_spans.contains(&occurrence.span);
        if is_declaration && !include_declaration {
            continue;
        }
        let (start_line, start_col) = line_index.offset_to_position(occurrence.span.start);
        let (end_line, end_col) = line_index.offset_to_position(occurrence.span.end);
        locations.push(Location {
            uri: uri.clone(),
            range: Range {
                start: Position::new(start_line, start_col),
                end: Position::new(end_line, end_col),
            },
        });
    }

    // Deduplicate by range — see `collect_currency_rename_edits` for
    // why this guard is here.
    locations.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    locations.dedup_by(|a, b| a.range == b.range);
}

/// Collect all references to a payee.
fn collect_payee_references(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    payee: &str,
    uri: &Uri,
    locations: &mut Vec<Location>,
) {
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value
            && let Some(ref txn_payee) = txn.payee
            && txn_payee.as_ref() == payee
        {
            let (line, _) = line_index.offset_to_position(spanned.span.start);
            let line_text = source.lines().nth(line as usize).unwrap_or("");

            // Find the payee in quotes
            if let Some(quote_byte) = line_text.find(&format!("\"{}\"", payee))
                && let Some(start) = line_index.byte_in_line_to_position(line, quote_byte + 1)
                && let Some(end) =
                    line_index.byte_in_line_to_position(line, quote_byte + 1 + payee.len())
            {
                locations.push(Location {
                    uri: uri.clone(),
                    range: Range { start, end },
                });
            }
        }
    }
}

/// Check if position is inside quotes.
fn is_in_quotes(line: &str, col: usize) -> bool {
    let chars: Vec<char> = line.chars().collect();
    let mut in_quotes = false;

    for (i, c) in chars.iter().enumerate() {
        if i >= col {
            break;
        }
        if *c == '"' {
            in_quotes = !in_quotes;
        }
    }

    in_quotes
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_find_account_references() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 16), // On "Assets:Bank"
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };

        let refs = handle_references(&params, source, &result, &[], &uri, PositionEncoding::Utf16);
        assert!(refs.is_some());

        let refs = refs.unwrap();
        // Should find: open, posting, balance = 3 references
        assert_eq!(refs.len(), 3);
    }

    #[test]
    fn test_find_currency_references() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food  5.00 USD
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 28), // On "USD"
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };

        let refs = handle_references(&params, source, &result, &[], &uri, PositionEncoding::Utf16);
        assert!(refs.is_some());

        let refs = refs.unwrap();
        // Should find USD in: open, posting 1, posting 2 = 3 references
        assert_eq!(refs.len(), 3);
    }

    /// Regression test for currency-reference false positives. See
    /// `rename.rs::test_rename_currency_no_false_positives` for the
    /// fuller rationale. Same source shape; the AST-driven
    /// references walker should report exactly the legitimate
    /// `Currency`-token occurrences.
    #[test]
    fn test_find_currency_references_no_false_positives() {
        let source = r#"2024-01-01 open Assets:USD-Reserve
2024-01-01 commodity USD
2024-01-15 * "USD-to-EUR transfer"
  Assets:USD-Reserve  -100 USD
  Assets:Bank          100 USD
"#;
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        // Position cursor on the `USD` of `commodity USD`.
        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(1, 21),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };

        let refs = handle_references(&params, source, &result, &[], &uri, PositionEncoding::Utf16)
            .expect("references returns Some");

        // Expected: 3 references — `commodity USD`, `-100 USD`,
        // `100 USD`. Bespoke string-search would have reported the
        // payee string and the account-name substrings too.
        assert_eq!(
            refs.len(),
            3,
            "expected 3 currency references, got {}: {refs:#?}",
            refs.len()
        );

        // With `include_declaration: false`, the commodity-directive
        // occurrence should drop out.
        let params_no_decl = ReferenceParams {
            context: lsp_types::ReferenceContext {
                include_declaration: false,
            },
            ..params
        };
        let refs_no_decl = handle_references(
            &params_no_decl,
            source,
            &result,
            &[],
            &uri,
            PositionEncoding::Utf16,
        )
        .expect("references returns Some");
        assert_eq!(
            refs_no_decl.len(),
            2,
            "expected 2 non-declaration references, got {}: {refs_no_decl:#?}",
            refs_no_decl.len()
        );
    }

    /// Regression test for account-reference false positives -
    /// phase 5.5 of the CST migration (#1262). Same shape as
    /// `test_find_currency_references_no_false_positives` and
    /// `rename::test_rename_account_no_false_positives`.
    #[test]
    fn test_find_account_references_no_false_positives() {
        // Source carefully constructed to embed the literal string
        // `Assets:Bank` in payee, STRING-typed metadata, and
        // comment positions inside the same directives that
        // legitimately reference the account. The CST-backed walk
        // emits NO edits for these because the lexer classified
        // them as STRING / META_VALUE / COMMENT, not ACCOUNT.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Assets:Bank transfer note"
  Assets:Bank  -5.00 USD
    memo: "moved Assets:Bank balance"
  Expenses:Food
; rebalanced Assets:Bank yesterday
"#;
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 16), // on `Assets:Bank` of the open
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };
        let refs = handle_references(&params, source, &result, &[], &uri, PositionEncoding::Utf16)
            .expect("references returns Some");
        // Expected: 2 references - the open's ACCOUNT token and
        // the posting's ACCOUNT token. The substring-search shape
        // would have produced 5 (the 2 valid + payee string +
        // STRING-typed metadata + trailing comment).
        assert_eq!(
            refs.len(),
            2,
            "expected 2 account references, got {}: {refs:#?}",
            refs.len()
        );
        // Pin the exact source lines so a future bug that emits
        // two zero-width ranges (or two ranges both at the Open
        // position) still fails — count-only assertions used to
        // miss that class.
        let lines: Vec<u32> = refs.iter().map(|r| r.range.start.line).collect();
        assert_eq!(
            lines,
            vec![0, 2],
            "expected references on lines 0 (open) and 2 (posting), got {lines:?}"
        );
        // Each range must be non-zero-width and span the full
        // 11-char `Assets:Bank`.
        for r in &refs {
            assert_eq!(
                r.range.end.character - r.range.start.character,
                "Assets:Bank".len() as u32,
                "reference range is wrong width: {r:?}"
            );
        }

        // include_declaration: false drops the open occurrence.
        let params_no_decl = ReferenceParams {
            context: lsp_types::ReferenceContext {
                include_declaration: false,
            },
            ..params
        };
        let refs_no_decl = handle_references(
            &params_no_decl,
            source,
            &result,
            &[],
            &uri,
            PositionEncoding::Utf16,
        )
        .expect("references returns Some");
        assert_eq!(
            refs_no_decl.len(),
            1,
            "expected 1 non-declaration account reference, got {}: {refs_no_decl:#?}",
            refs_no_decl.len()
        );
        assert_eq!(
            refs_no_decl[0].range.start.line, 2,
            "the surviving reference must be the posting on line 2"
        );
    }

    /// Regression test for the metadata-currency misclassification
    /// bug (Copilot #3270929987).
    ///
    /// Commodity directives can carry indented metadata whose values
    /// tokenize as `Currency` (e.g., `parent: USD`). A naive
    /// "occurrence span ⊆ Commodity directive span" check would
    /// classify those metadata-value currency tokens as
    /// declarations. With `include_declaration = false`, the
    /// metadata reference would then be incorrectly filtered out of
    /// the results — a silent false negative.
    ///
    /// The fix is to identify the *first* currency token within
    /// each Commodity span as the declaration (the parser is
    /// forward-advancing and the declared currency is parsed
    /// before the metadata block), via
    /// `commodity_declaration_spans`.
    #[test]
    fn test_currency_in_commodity_metadata_is_not_a_declaration() {
        // `commodity USD\n  parent: USD` — the second USD is a
        // metadata reference, not a declaration. Renaming with
        // `include_declaration = false` must surface it.
        let source = r#"2024-01-01 commodity USD
  parent: USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
"#;
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 21), // on `USD` of `commodity USD`
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: false,
            },
        };

        let refs = handle_references(&params, source, &result, &[], &uri, PositionEncoding::Utf16)
            .expect("references returns Some");

        // Expected: 2 non-declaration references — the metadata
        // `parent: USD` and the posting `-5.00 USD`. The
        // declaration on line 0 is filtered out. A buggy
        // containment-only check would have returned 1 (only the
        // posting) because both line-0-USD and line-1-USD would
        // be considered declarations.
        assert_eq!(
            refs.len(),
            2,
            "expected 2 references (metadata + posting); got {}: {refs:#?}",
            refs.len()
        );
    }

    /// Regression test for the read-only sibling of #1142.
    ///
    /// Pre-fix, the reference range for the second posting landed on
    /// the metadata line between postings. With per-posting span
    /// lookup, every reference points at its actual posting line.
    #[test]
    fn test_find_account_references_with_interleaved_metadata_1142() {
        let source = "\
2024-01-01 open Assets:Bank USD
2024-01-15 * \"Test\"
  Assets:Bank  -5.00 USD
    effective_date: 2024-01-20
  Expenses:Food  5.00 USD
    effective_date: 2024-01-21
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 16), // on "Assets:Bank" in open
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };

        let refs = handle_references(&params, source, &result, &[], &uri, PositionEncoding::Utf16)
            .expect("at least the Open definition + 1 posting reference");

        let metadata_lines = [3u32, 5u32];
        for r in &refs {
            assert!(
                !metadata_lines.contains(&r.range.start.line),
                "reference range landed on a metadata line: {r:?}"
            );
        }
        // The Assets:Bank posting is on line 2 (the second posting,
        // Expenses:Food, is on line 4 and isn't a reference to
        // Assets:Bank, so we only verify the positive lines we expect).
        let lines: Vec<u32> = refs.iter().map(|r| r.range.start.line).collect();
        assert!(
            lines.contains(&2),
            "Assets:Bank posting on line 2 should appear in refs; got {lines:?}"
        );
    }
}
