//! Signature help handler for directive syntax assistance.
//!
//! Provides syntax hints when typing beancount directives:
//! - After date: shows available directive types
//! - After directive keyword: shows expected parameters

use lsp_types::{
    Documentation, MarkupContent, MarkupKind, ParameterInformation, ParameterLabel, SignatureHelp,
    SignatureHelpParams, SignatureInformation,
};

use super::utils::PositionEncoding;

/// Trigger characters for signature help.
pub const TRIGGER_CHARACTERS: &[&str] = &[" ", "*", "!"];

/// Handle a signature help request.
pub fn handle_signature_help(
    params: &SignatureHelpParams,
    source: &str,
    encoding: PositionEncoding,
) -> Option<SignatureHelp> {
    let position = params.text_document_position_params.position;
    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Map `position.character` (in the negotiated encoding) to a
    // byte offset into `line`. Walks chars once; `len_utf8` /
    // `len_utf16` per char dispatch is the only encoding-sensitive
    // step.
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
            break;
        }
        acc += u;
        byte_col += ch.len_utf8();
    }
    let text_before = &line[..byte_col];

    // Detect what kind of signature help to show
    detect_signature_context(text_before)
}

/// Detect the signature context based on text before cursor.
fn detect_signature_context(text: &str) -> Option<SignatureHelp> {
    let trimmed = text.trim_start();

    // Check if we're after a date (YYYY-MM-DD pattern)
    if let Some(after_date) = extract_after_date(trimmed) {
        return signature_after_date(after_date);
    }

    // Check for specific directive patterns
    if trimmed.starts_with("option") {
        return signature_for_option(trimmed);
    }

    if trimmed.starts_with("include") {
        return signature_for_include(trimmed);
    }

    if trimmed.starts_with("plugin") {
        return signature_for_plugin(trimmed);
    }

    None
}

/// Extract text after a date pattern.
fn extract_after_date(text: &str) -> Option<&str> {
    // Match YYYY-MM-DD pattern
    if text.len() >= 10 {
        let potential_date = &text[..10];
        if potential_date.chars().enumerate().all(|(i, c)| match i {
            0..=3 | 5..=6 | 8..=9 => c.is_ascii_digit(),
            4 | 7 => c == '-',
            _ => false,
        }) {
            return Some(text[10..].trim_start());
        }
    }
    None
}

/// Signature help after a date - show available directives.
fn signature_after_date(after_date: &str) -> Option<SignatureHelp> {
    let after_date = after_date.trim_start();

    // Determine which signature to show based on what follows
    if after_date.is_empty() {
        // Just typed date + space, show all options
        return Some(SignatureHelp {
            signatures: vec![
                transaction_signature(),
                open_signature(),
                close_signature(),
                balance_signature(),
                pad_signature(),
                note_signature(),
                document_signature(),
                event_signature(),
                price_signature(),
                commodity_signature(),
            ],
            active_signature: Some(0),
            active_parameter: Some(0),
        });
    }

    // Transaction flag
    if after_date == "*" || after_date == "!" {
        return Some(SignatureHelp {
            signatures: vec![transaction_signature()],
            active_signature: Some(0),
            active_parameter: Some(1), // payee parameter
        });
    }

    // After flag + space
    if after_date.starts_with("* ") || after_date.starts_with("! ") {
        let rest = &after_date[2..];
        let param = if rest.is_empty() {
            1 // payee
        } else if rest.contains('"') && rest.matches('"').count() >= 2 {
            2 // narration
        } else {
            1 // still on payee
        };
        return Some(SignatureHelp {
            signatures: vec![transaction_signature()],
            active_signature: Some(0),
            active_parameter: Some(param),
        });
    }

    // "txn" keyword
    if after_date.starts_with("txn") {
        return Some(SignatureHelp {
            signatures: vec![transaction_signature()],
            active_signature: Some(0),
            active_parameter: Some(1),
        });
    }

    // "open" directive
    if let Some(rest) = after_date.strip_prefix("open") {
        let rest = rest.trim_start();
        let param = if rest.is_empty() {
            0 // account
        } else if rest.contains(' ') {
            1 // currencies
        } else {
            0
        };
        return Some(SignatureHelp {
            signatures: vec![open_signature()],
            active_signature: Some(0),
            active_parameter: Some(param),
        });
    }

    // "close" directive
    if after_date.starts_with("close") {
        return Some(SignatureHelp {
            signatures: vec![close_signature()],
            active_signature: Some(0),
            active_parameter: Some(0),
        });
    }

    // "balance" directive
    if let Some(rest) = after_date.strip_prefix("balance") {
        let rest = rest.trim_start();
        let param = if rest.is_empty() {
            0 // account
        } else if rest.contains(' ') {
            1 // amount
        } else {
            0
        };
        return Some(SignatureHelp {
            signatures: vec![balance_signature()],
            active_signature: Some(0),
            active_parameter: Some(param),
        });
    }

    // "pad" directive
    if let Some(rest) = after_date.strip_prefix("pad") {
        let rest = rest.trim_start();
        let spaces = rest.matches(' ').count();
        let param = spaces.min(1);
        return Some(SignatureHelp {
            signatures: vec![pad_signature()],
            active_signature: Some(0),
            active_parameter: Some(param as u32),
        });
    }

    // "note" directive
    if let Some(rest) = after_date.strip_prefix("note") {
        let rest = rest.trim_start();
        let param = if rest.is_empty() || !rest.contains(' ') {
            0 // account
        } else {
            1 // note text
        };
        return Some(SignatureHelp {
            signatures: vec![note_signature()],
            active_signature: Some(0),
            active_parameter: Some(param),
        });
    }

    // "document" directive
    if let Some(rest) = after_date.strip_prefix("document") {
        let rest = rest.trim_start();
        let param = if rest.is_empty() || !rest.contains(' ') {
            0 // account
        } else {
            1 // path
        };
        return Some(SignatureHelp {
            signatures: vec![document_signature()],
            active_signature: Some(0),
            active_parameter: Some(param),
        });
    }

    // "event" directive
    if let Some(rest) = after_date.strip_prefix("event") {
        let rest = rest.trim_start();
        let param = if rest.is_empty() || !rest.contains('"') {
            0 // type
        } else {
            1 // description
        };
        return Some(SignatureHelp {
            signatures: vec![event_signature()],
            active_signature: Some(0),
            active_parameter: Some(param),
        });
    }

    // "price" directive
    if let Some(rest) = after_date.strip_prefix("price") {
        let rest = rest.trim_start();
        // The active parameter is the number of COMPLETE tokens: a trailing
        // space means the previous token is finished and the cursor has advanced
        // to the next parameter. Counting tokens alone left `price AAPL ` on
        // param 0 (commodity) instead of advancing to 1 (amount).
        let tokens = rest.split_whitespace().count();
        let complete = if rest.is_empty() || rest.ends_with(char::is_whitespace) {
            tokens
        } else {
            tokens.saturating_sub(1)
        };
        let param = complete.min(2);
        return Some(SignatureHelp {
            signatures: vec![price_signature()],
            active_signature: Some(0),
            active_parameter: Some(param as u32),
        });
    }

    // "commodity" directive
    if after_date.starts_with("commodity") {
        return Some(SignatureHelp {
            signatures: vec![commodity_signature()],
            active_signature: Some(0),
            active_parameter: Some(0),
        });
    }

    None
}

/// Signature help for option directive.
fn signature_for_option(text: &str) -> Option<SignatureHelp> {
    let rest = &text[6..].trim_start(); // after "option"
    let param = if rest.is_empty() || !rest.contains('"') {
        0 // name
    } else {
        1 // value
    };

    Some(SignatureHelp {
        signatures: vec![SignatureInformation {
            label: "option \"name\" \"value\"".to_string(),
            documentation: Some(Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "Set a beancount option.\n\nCommon options:\n- `title`: Ledger title\n- `operating_currency`: Main currency\n- `booking_method`: FIFO, LIFO, etc.".to_string(),
            })),
            parameters: Some(vec![
                ParameterInformation {
                    label: ParameterLabel::Simple("\"name\"".to_string()),
                    documentation: Some(Documentation::String("Option name".to_string())),
                },
                ParameterInformation {
                    label: ParameterLabel::Simple("\"value\"".to_string()),
                    documentation: Some(Documentation::String("Option value".to_string())),
                },
            ]),
            active_parameter: None,
        }],
        active_signature: Some(0),
        active_parameter: Some(param),
    })
}

/// Signature help for include directive.
fn signature_for_include(_text: &str) -> Option<SignatureHelp> {
    Some(SignatureHelp {
        signatures: vec![SignatureInformation {
            label: "include \"path\"".to_string(),
            documentation: Some(Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "Include another beancount file.\n\nPaths are relative to the current file."
                    .to_string(),
            })),
            parameters: Some(vec![ParameterInformation {
                label: ParameterLabel::Simple("\"path\"".to_string()),
                documentation: Some(Documentation::String("Path to beancount file".to_string())),
            }]),
            active_parameter: None,
        }],
        active_signature: Some(0),
        active_parameter: Some(0),
    })
}

/// Signature help for plugin directive.
fn signature_for_plugin(text: &str) -> Option<SignatureHelp> {
    let rest = &text[6..].trim_start(); // after "plugin"
    let param = if rest.is_empty() || !rest.contains('"') {
        0 // name
    } else if rest.matches('"').count() >= 2 {
        1 // config
    } else {
        0
    };

    Some(SignatureHelp {
        signatures: vec![SignatureInformation {
            label: "plugin \"name\" [\"config\"]".to_string(),
            documentation: Some(Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "Load a beancount plugin.\n\nBuilt-in plugins include:\n- `auto_accounts`\n- `check_commodity`\n- `coherent_cost`".to_string(),
            })),
            parameters: Some(vec![
                ParameterInformation {
                    label: ParameterLabel::Simple("\"name\"".to_string()),
                    documentation: Some(Documentation::String("Plugin module name".to_string())),
                },
                ParameterInformation {
                    label: ParameterLabel::Simple("\"config\"".to_string()),
                    documentation: Some(Documentation::String("Optional plugin configuration".to_string())),
                },
            ]),
            active_parameter: None,
        }],
        active_signature: Some(0),
        active_parameter: Some(param),
    })
}

fn transaction_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD [*|!] [\"payee\"] \"narration\"".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Create a transaction.\n\n- `*` = completed\n- `!` = pending\n\nFollowed by posting lines.".to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("[*|!]".to_string()),
                documentation: Some(Documentation::String("Transaction flag (* = completed, ! = pending)".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("\"payee\"".to_string()),
                documentation: Some(Documentation::String("Optional payee name".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("\"narration\"".to_string()),
                documentation: Some(Documentation::String("Transaction description".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn open_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD open Account [Currency,...]".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Open a new account.\n\nAccount format: `Type:Subtype:Name`\n\nTypes: Assets, Liabilities, Equity, Income, Expenses".to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("Account".to_string()),
                documentation: Some(Documentation::String("Account name (e.g., Assets:Bank:Checking)".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("[Currency,...]".to_string()),
                documentation: Some(Documentation::String("Optional allowed currencies".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn close_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD close Account".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Close an account.\n\nPrevents further postings after this date.".to_string(),
        })),
        parameters: Some(vec![ParameterInformation {
            label: ParameterLabel::Simple("Account".to_string()),
            documentation: Some(Documentation::String("Account to close".to_string())),
        }]),
        active_parameter: None,
    }
}

fn balance_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD balance Account Amount Currency".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Assert an account balance.\n\nVerifies the account has the specified balance at the start of this date.".to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("Account".to_string()),
                documentation: Some(Documentation::String("Account to check".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("Amount Currency".to_string()),
                documentation: Some(Documentation::String("Expected balance (e.g., 1000.00 USD)".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn pad_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD pad Account PadAccount".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Automatically pad an account.\n\nInserts a transaction to bring the account to the expected balance (used with balance assertions).".to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("Account".to_string()),
                documentation: Some(Documentation::String("Account to pad".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("PadAccount".to_string()),
                documentation: Some(Documentation::String("Source account for padding (e.g., Equity:Opening-Balances)".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn note_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD note Account \"text\"".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Add a note to an account.\n\nUseful for recording important events or changes."
                .to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("Account".to_string()),
                documentation: Some(Documentation::String("Account to annotate".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("\"text\"".to_string()),
                documentation: Some(Documentation::String("Note content".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn document_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD document Account \"path\"".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value:
                "Link a document to an account.\n\nUsed for attaching receipts, statements, etc."
                    .to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("Account".to_string()),
                documentation: Some(Documentation::String("Associated account".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("\"path\"".to_string()),
                documentation: Some(Documentation::String("Path to document file".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn event_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD event \"type\" \"description\"".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Record an event.\n\nUsed for tracking life events, location changes, etc."
                .to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("\"type\"".to_string()),
                documentation: Some(Documentation::String(
                    "Event type (e.g., \"location\", \"employer\")".to_string(),
                )),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("\"description\"".to_string()),
                documentation: Some(Documentation::String("Event description".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn price_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD price Currency Amount QuoteCurrency".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Record a price for a commodity.\n\nUsed for tracking market prices of stocks, currencies, etc.".to_string(),
        })),
        parameters: Some(vec![
            ParameterInformation {
                label: ParameterLabel::Simple("Currency".to_string()),
                documentation: Some(Documentation::String("Base currency (e.g., AAPL, EUR)".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("Amount".to_string()),
                documentation: Some(Documentation::String("Price value".to_string())),
            },
            ParameterInformation {
                label: ParameterLabel::Simple("QuoteCurrency".to_string()),
                documentation: Some(Documentation::String("Quote currency (e.g., USD)".to_string())),
            },
        ]),
        active_parameter: None,
    }
}

fn commodity_signature() -> SignatureInformation {
    SignatureInformation {
        label: "YYYY-MM-DD commodity Currency".to_string(),
        documentation: Some(Documentation::MarkupContent(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "Declare a commodity.\n\nOptionally followed by metadata lines.".to_string(),
        })),
        parameters: Some(vec![ParameterInformation {
            label: ParameterLabel::Simple("Currency".to_string()),
            documentation: Some(Documentation::String(
                "Commodity symbol (e.g., USD, AAPL)".to_string(),
            )),
        }]),
        active_parameter: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_after_date_shows_directives() {
        let source = "2024-01-15 ";
        let params = SignatureHelpParams {
            context: None,
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier {
                    uri: "file:///test.beancount".parse().unwrap(),
                },
                position: lsp_types::Position::new(0, 11),
            },
            work_done_progress_params: Default::default(),
        };

        let help = handle_signature_help(&params, source, PositionEncoding::Utf16);
        assert!(help.is_some());

        let help = help.unwrap();
        assert!(!help.signatures.is_empty());
        assert!(help.signatures.len() >= 5); // Multiple directive options
    }

    #[test]
    fn test_transaction_flag() {
        let source = "2024-01-15 * ";
        let params = SignatureHelpParams {
            context: None,
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier {
                    uri: "file:///test.beancount".parse().unwrap(),
                },
                position: lsp_types::Position::new(0, 13),
            },
            work_done_progress_params: Default::default(),
        };

        let help = handle_signature_help(&params, source, PositionEncoding::Utf16);
        assert!(help.is_some());

        let help = help.unwrap();
        assert_eq!(help.signatures.len(), 1);
        assert!(help.signatures[0].label.contains("payee"));
    }

    #[test]
    fn test_open_directive() {
        let source = "2024-01-15 open ";
        let params = SignatureHelpParams {
            context: None,
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier {
                    uri: "file:///test.beancount".parse().unwrap(),
                },
                position: lsp_types::Position::new(0, 16),
            },
            work_done_progress_params: Default::default(),
        };

        let help = handle_signature_help(&params, source, PositionEncoding::Utf16);
        assert!(help.is_some());

        let help = help.unwrap();
        assert_eq!(help.signatures.len(), 1);
        assert!(help.signatures[0].label.contains("open"));
        assert_eq!(help.active_parameter, Some(0)); // Account parameter
    }

    #[test]
    fn test_price_directive_active_parameter_advances() {
        // After `price AAPL ` (commodity + trailing space) the active parameter
        // must advance to the amount (1), not stay on the commodity (0).
        let cases = [
            ("2024-01-15 price ", 17, 0u32),       // typing the commodity
            ("2024-01-15 price AAPL ", 22, 1),     // commodity done → amount
            ("2024-01-15 price AAPL 150 ", 26, 2), // amount done → currency
        ];
        for (source, col, expected) in cases {
            let params = SignatureHelpParams {
                context: None,
                text_document_position_params: lsp_types::TextDocumentPositionParams {
                    text_document: lsp_types::TextDocumentIdentifier {
                        uri: "file:///test.beancount".parse().unwrap(),
                    },
                    position: lsp_types::Position::new(0, col),
                },
                work_done_progress_params: Default::default(),
            };
            let help = handle_signature_help(&params, source, PositionEncoding::Utf16)
                .unwrap_or_else(|| panic!("signature help for {source:?}"));
            assert!(help.signatures[0].label.contains("price"));
            assert_eq!(
                help.active_parameter,
                Some(expected),
                "wrong active parameter for {source:?}"
            );
        }
    }

    #[test]
    fn test_option_directive() {
        let source = "option ";
        let params = SignatureHelpParams {
            context: None,
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier {
                    uri: "file:///test.beancount".parse().unwrap(),
                },
                position: lsp_types::Position::new(0, 7),
            },
            work_done_progress_params: Default::default(),
        };

        let help = handle_signature_help(&params, source, PositionEncoding::Utf16);
        assert!(help.is_some());

        let help = help.unwrap();
        assert!(help.signatures[0].label.contains("option"));
    }
}
