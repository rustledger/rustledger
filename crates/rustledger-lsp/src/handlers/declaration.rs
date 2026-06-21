//! Go to declaration handler.
//!
//! In Beancount, "declaration" and "definition" are the same concept:
//! - For accounts: the `open` directive
//! - For currencies: the `commodity` directive
//!
//! This module simply re-exports the definition handler.

pub use super::definition::handle_goto_definition as handle_goto_declaration;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handlers::utils::PositionEncoding;
    use lsp_types::{
        GotoDefinitionParams, Position, TextDocumentIdentifier, TextDocumentPositionParams,
    };
    use rustledger_parser::parse;

    #[test]
    fn test_goto_declaration_is_goto_definition() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        let params = GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(2, 5), // On "Assets:Bank" in posting
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let result = handle_goto_declaration(
            &params,
            source,
            &result,
            None,
            &uri,
            PositionEncoding::Utf16,
        );
        assert!(result.is_some());
    }
}
