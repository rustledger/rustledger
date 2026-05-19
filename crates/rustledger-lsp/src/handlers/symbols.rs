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

use super::utils::LineIndex;

/// Handle a document symbols request.
pub fn handle_document_symbols(
    _params: &DocumentSymbolParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<DocumentSymbolResponse> {
    // Build line index once for O(log n) lookups
    let line_index = LineIndex::new(source);

    let symbols: Vec<DocumentSymbol> = parse_result
        .directives
        .iter()
        .filter_map(|spanned| {
            directive_to_symbol(
                &spanned.value,
                spanned.span.start,
                spanned.span.end,
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

                    let (posting_line, _) =
                        line_index.offset_to_position(spanned_posting.span.start);
                    let posting_range = Range {
                        start: Position::new(posting_line, 2),
                        end: Position::new(posting_line, 50),
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

        let response = handle_document_symbols(&params, source, &result);
        assert!(response.is_some());

        if let Some(DocumentSymbolResponse::Nested(symbols)) = response {
            assert_eq!(symbols.len(), 2); // open + transaction
        }
    }
}
