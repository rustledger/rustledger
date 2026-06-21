//! Document symbols handler for outline view.
//!
//! Provides a hierarchical view of all directives in a Beancount file:
//! - Transactions with their postings
//! - Account directives (open, close)
//! - Balance assertions
//! - Other directives

use lsp_types::{
    DocumentSymbol, DocumentSymbolParams, DocumentSymbolResponse, Position, Range, SymbolKind,
};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;

use super::utils::{LineIndex, PositionEncoding, trim_span_end};

/// Handle a document symbols request.
pub fn handle_document_symbols(
    _params: &DocumentSymbolParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<DocumentSymbolResponse> {
    // Build line index once for O(log n) lookups
    let line_index = LineIndex::new(source, encoding);

    let symbols: Vec<DocumentSymbol> = parse_result
        .directives
        .iter()
        .filter_map(|spanned| {
            directive_to_symbol(
                &spanned.value,
                source,
                spanned.span.start,
                // Trim trailing whitespace so a symbol's range ends at its own
                // content, not at the next directive (which made sibling symbol
                // ranges overlap and broke editor breadcrumb/enclosing logic).
                trim_span_end(source, spanned.span.end),
                &line_index,
            )
        })
        .collect();

    if symbols.is_empty() {
        None
    } else {
        Some(DocumentSymbolResponse::Nested(symbols))
    }
}

/// Convert a directive to a document symbol.
#[allow(deprecated)] // DocumentSymbol::deprecated field is deprecated but required
fn directive_to_symbol(
    directive: &Directive,
    source: &str,
    start_offset: usize,
    end_offset: usize,
    line_index: &LineIndex,
) -> Option<DocumentSymbol> {
    let (start_line, start_col) = line_index.offset_to_position(start_offset);
    let (end_line, end_col) = line_index.offset_to_position(end_offset);

    let range = Range {
        start: Position::new(start_line, start_col),
        end: Position::new(end_line, end_col),
    };

    let selection_range = range;

    match directive {
        Directive::Transaction(txn) => {
            let name = if let Some(ref payee) = txn.payee {
                format!("{} {}", txn.date, payee)
            } else if !txn.narration.is_empty() {
                format!("{} {}", txn.date, txn.narration)
            } else {
                format!("{} Transaction", txn.date)
            };

            let detail = if txn.narration.is_empty() {
                None
            } else {
                Some(txn.narration.to_string())
            };

            // Create child symbols for postings. Look up each posting's
            // line from its own source span instead of the prior
            // `start_line + 1 + i` arithmetic (see #1142): with
            // interleaved metadata, that pointed at metadata lines and
            // produced wrong symbol ranges in the outline view.
            let children: Vec<DocumentSymbol> = txn
                .postings
                .iter()
                .filter(|spanned_posting| spanned_posting.file_id != SYNTHESIZED_FILE_ID)
                .map(|spanned_posting| {
                    let posting = &**spanned_posting;
                    let posting_name = posting.account.to_string();
                    let posting_detail = posting.units.as_ref().map(|u| {
                        if let (Some(num), Some(curr)) = (u.number(), u.currency()) {
                            format!("{} {}", num, curr)
                        } else if let Some(num) = u.number() {
                            num.to_string()
                        } else {
                            String::new()
                        }
                    });

                    // Derive the range from the posting's own span (trimmed of
                    // trailing whitespace) instead of a hardcoded `col 2..50`,
                    // which overshot past end-of-line on short postings,
                    // truncated long ones, and started mid-account on
                    // non-2-space indentation.
                    let (posting_start_line, posting_start_col) =
                        line_index.offset_to_position(spanned_posting.span.start);
                    let (posting_end_line, posting_end_col) = line_index
                        .offset_to_position(trim_span_end(source, spanned_posting.span.end));
                    let posting_range = Range {
                        start: Position::new(posting_start_line, posting_start_col),
                        end: Position::new(posting_end_line, posting_end_col),
                    };

                    DocumentSymbol {
                        name: posting_name,
                        detail: posting_detail,
                        kind: SymbolKind::PROPERTY,
                        tags: None,
                        deprecated: None,
                        range: posting_range,
                        selection_range: posting_range,
                        children: None,
                    }
                })
                .collect();

            Some(DocumentSymbol {
                name,
                detail,
                kind: SymbolKind::EVENT,
                tags: None,
                deprecated: None,
                range,
                selection_range,
                children: if children.is_empty() {
                    None
                } else {
                    Some(children)
                },
            })
        }

        Directive::Open(open) => Some(DocumentSymbol {
            name: format!("open {}", open.account),
            detail: if open.currencies.is_empty() {
                None
            } else {
                Some(
                    open.currencies
                        .iter()
                        .map(|c| c.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                )
            },
            kind: SymbolKind::CLASS,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Close(close) => Some(DocumentSymbol {
            name: format!("close {}", close.account),
            detail: None,
            kind: SymbolKind::CLASS,
            tags: None,
            deprecated: Some(true), // Mark as deprecated since it's closing
            range,
            selection_range,
            children: None,
        }),

        Directive::Balance(bal) => Some(DocumentSymbol {
            name: format!("balance {}", bal.account),
            detail: Some(format!("{} {}", bal.amount.number, bal.amount.currency)),
            kind: SymbolKind::NUMBER,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Pad(pad) => Some(DocumentSymbol {
            name: format!("pad {}", pad.account),
            detail: Some(format!("from {}", pad.source_account)),
            kind: SymbolKind::OPERATOR,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Commodity(comm) => Some(DocumentSymbol {
            name: format!("commodity {}", comm.currency),
            detail: None,
            kind: SymbolKind::CONSTANT,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Event(event) => Some(DocumentSymbol {
            name: format!("event \"{}\"", event.event_type),
            detail: Some(event.value.to_string()),
            kind: SymbolKind::EVENT,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Note(note) => Some(DocumentSymbol {
            name: format!("note {}", note.account),
            detail: Some(note.comment.to_string()),
            kind: SymbolKind::STRING,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Document(doc) => Some(DocumentSymbol {
            name: format!("document {}", doc.account),
            detail: Some(doc.path.to_string()),
            kind: SymbolKind::FILE,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Price(price) => Some(DocumentSymbol {
            name: format!("price {}", price.currency),
            detail: Some(format!("{} {}", price.amount.number, price.amount.currency)),
            kind: SymbolKind::NUMBER,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Query(query) => Some(DocumentSymbol {
            name: format!("query \"{}\"", query.name),
            detail: None,
            kind: SymbolKind::FUNCTION,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),

        Directive::Custom(custom) => Some(DocumentSymbol {
            name: format!("custom \"{}\"", custom.custom_type),
            detail: None,
            kind: SymbolKind::OBJECT,
            tags: None,
            deprecated: None,
            range,
            selection_range,
            children: None,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_document_symbols_basic() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee Shop" "Morning coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let params = DocumentSymbolParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let response = handle_document_symbols(&params, source, &result, PositionEncoding::Utf16);
        assert!(response.is_some());

        if let Some(DocumentSymbolResponse::Nested(symbols)) = response {
            assert_eq!(symbols.len(), 2); // open + transaction
        }
    }

    #[test]
    fn test_document_symbol_ranges_do_not_overlap() {
        // Two transactions separated by blank lines. Each symbol's range must
        // end at its own content, not extend into the next directive — else
        // sibling ranges overlap and break editor breadcrumb/enclosing logic.
        let source = "2024-01-15 * \"T1\"\n  Assets:Bank  -5 USD\n  Expenses:Food  5 USD\n\n\n2024-01-20 * \"T2\"\n  Assets:Bank  -3 USD\n  Expenses:Food  3 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "no parse errors");
        let params = DocumentSymbolParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let Some(DocumentSymbolResponse::Nested(symbols)) =
            handle_document_symbols(&params, source, &result, PositionEncoding::Utf16)
        else {
            panic!("expected nested symbols");
        };
        assert_eq!(symbols.len(), 2);
        // T1's range must end before T2's range starts (line 5 is T2's header).
        assert!(
            symbols[0].range.end.line < symbols[1].range.start.line,
            "T1 symbol range {:?} overlaps T2 {:?}",
            symbols[0].range,
            symbols[1].range
        );
        assert_eq!(symbols[0].range.end.line, 2, "T1 ends at its last posting");
    }

    #[test]
    fn test_posting_child_ranges_match_their_spans() {
        // Posting child symbols must use their own source span, not a hardcoded
        // `col 2..50` window that overshoots end-of-line / starts mid-account.
        let source = "2024-01-15 * \"T\"\n  Assets:Bank  -5 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "no parse errors");
        let params = DocumentSymbolParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let Some(DocumentSymbolResponse::Nested(symbols)) =
            handle_document_symbols(&params, source, &result, PositionEncoding::Utf16)
        else {
            panic!("expected nested symbols");
        };
        let txn = &symbols[0];
        let posting = &txn.children.as_ref().expect("postings as children")[0];
        // `  Assets:Bank  -5 USD` on line 1: the posting span runs from the
        // start of the line (col 0 — the indent, so the range still fully
        // covers the account) to col 21 (just after `USD`) — never the
        // hardcoded col 50 that overshot end-of-line.
        assert_eq!(posting.range.start, Position::new(1, 0));
        assert_eq!(
            posting.range.end,
            Position::new(1, 21),
            "posting range must end at its content, not the hardcoded col 50"
        );
    }
}
