//! Document color handler for visual amount feedback.
//!
//! Provides color information for:
//! - Negative amounts: red
//! - Positive amounts: green
//! - Zero amounts: gray

use lsp_types::{
    Color, ColorInformation, ColorPresentation, ColorPresentationParams, DocumentColorParams,
    Position, Range,
};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;

use super::utils::{LineIndex, PositionEncoding};

/// Red color for negative amounts.
const COLOR_NEGATIVE: Color = Color {
    red: 0.9,
    green: 0.2,
    blue: 0.2,
    alpha: 1.0,
};

/// Green color for positive amounts.
const COLOR_POSITIVE: Color = Color {
    red: 0.2,
    green: 0.8,
    blue: 0.3,
    alpha: 1.0,
};

/// Gray color for zero amounts.
const COLOR_ZERO: Color = Color {
    red: 0.5,
    green: 0.5,
    blue: 0.5,
    alpha: 1.0,
};

/// Handle a document color request.
pub fn handle_document_color(
    _params: &DocumentColorParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<ColorInformation>> {
    let mut colors = Vec::new();
    let line_index = LineIndex::new(source, encoding);
    let lines: Vec<&str> = source.lines().collect();

    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                // Per-posting span lookup (see #1142): the prior
                // `start_line + 1 + i` arithmetic broke whenever a
                // transaction had interleaved posting-level metadata.
                for spanned_posting in &txn.postings {
                    if spanned_posting.file_id == SYNTHESIZED_FILE_ID {
                        continue;
                    }
                    let posting = &**spanned_posting;
                    if let Some(units) = &posting.units
                        && let Some(number) = units.number()
                    {
                        let (posting_line, _) =
                            line_index.offset_to_position(spanned_posting.span.start);
                        let line_text = lines.get(posting_line as usize).copied().unwrap_or("");

                        // Find the amount in the line
                        let amount_str = number.to_string();
                        if let Some(range) =
                            find_amount_range(line_text, &amount_str, posting_line, &line_index)
                        {
                            let color = if number.is_sign_negative() {
                                COLOR_NEGATIVE
                            } else if number.is_zero() {
                                COLOR_ZERO
                            } else {
                                COLOR_POSITIVE
                            };

                            colors.push(ColorInformation { range, color });
                        }
                    }
                }
            }
            Directive::Balance(bal) => {
                let (line, _) = line_index.offset_to_position(spanned.span.start);
                let line_text = source.lines().nth(line as usize).unwrap_or("");

                let amount_str = bal.amount.number.to_string();
                if let Some(range) = find_amount_range(line_text, &amount_str, line, &line_index) {
                    let color = if bal.amount.number.is_sign_negative() {
                        COLOR_NEGATIVE
                    } else if bal.amount.number.is_zero() {
                        COLOR_ZERO
                    } else {
                        COLOR_POSITIVE
                    };

                    colors.push(ColorInformation { range, color });
                }
            }
            Directive::Price(price) => {
                let (line, _) = line_index.offset_to_position(spanned.span.start);
                let line_text = source.lines().nth(line as usize).unwrap_or("");

                let amount_str = price.amount.number.to_string();
                if let Some(range) = find_amount_range(line_text, &amount_str, line, &line_index) {
                    colors.push(ColorInformation {
                        range,
                        color: COLOR_POSITIVE, // Prices are always "positive" in context
                    });
                }
            }
            _ => {}
        }
    }

    if colors.is_empty() {
        None
    } else {
        Some(colors)
    }
}

/// Handle a color presentation request.
/// This is called when the user wants to change a color (not really applicable for amounts).
pub fn handle_color_presentation(params: &ColorPresentationParams) -> Vec<ColorPresentation> {
    // We don't support changing colors - amounts are data, not colors
    // Just return the current representation
    let label = if params.color.red > 0.5 && params.color.green < 0.5 {
        "Negative amount"
    } else if params.color.green > 0.5 {
        "Positive amount"
    } else {
        "Zero amount"
    };

    vec![ColorPresentation {
        label: label.to_string(),
        text_edit: None,
        additional_text_edits: None,
    }]
}

/// Find the range of an amount in a line.
///
/// `line_index` is consulted to convert the byte offsets returned by
/// `line.find()` into LSP columns in the negotiated encoding —
/// otherwise the emitted Range carries raw byte offsets that misalign
/// under UTF-16 negotiation on lines containing non-ASCII content.
fn find_amount_range(
    line: &str,
    amount_str: &str,
    line_num: u32,
    line_index: &LineIndex<'_>,
) -> Option<Range> {
    // Look for the amount pattern (may have negative sign)
    let search_patterns = [
        amount_str.to_string(),
        format!("-{}", amount_str.trim_start_matches('-')),
    ];

    // Resolve the byte offset of the addressed line's start in the
    // full source so we can translate `pos` (byte offset within
    // `line`) into source-frame byte offsets for the LineIndex
    // conversion.
    let line_start_byte = line_index
        .position_to_offset(line_num, 0)
        .unwrap_or_default();

    for pattern in &search_patterns {
        if let Some(pos) = line.find(pattern) {
            // Verify it's a standalone number (not part of a larger
            // string). `pos` is a BYTE offset returned by
            // `line.find`, so the boundary check must index by byte
            // too. Pre-round-19 used `line.chars().nth(pos - 1)`
            // which is a CHAR index — for any line containing non-
            // ASCII content (account names with Cyrillic, narrations
            // with emoji), the char index landed past the intended
            // location and the check produced wrong results. The
            // ASCII-only classification we want here (alnum / digit)
            // is well-defined on the raw byte at `pos - 1` /
            // `after_pos`, so byte indexing is both correct and
            // simpler.
            let bytes = line.as_bytes();
            let before_ok = pos == 0 || !bytes[pos - 1].is_ascii_alphanumeric();
            let after_pos = pos + pattern.len();
            let after_ok = after_pos >= bytes.len() || !bytes[after_pos].is_ascii_digit();

            if before_ok && after_ok {
                let (sl, sc) = line_index.offset_to_position(line_start_byte + pos);
                let (el, ec) = line_index.offset_to_position(line_start_byte + after_pos);
                return Some(Range {
                    start: Position::new(sl, sc),
                    end: Position::new(el, ec),
                });
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_document_color_positive_negative() {
        let source = r#"2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food  5.00 USD
"#;
        let result = parse(source);
        let params = DocumentColorParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let colors = handle_document_color(&params, source, &result, PositionEncoding::Utf16);
        assert!(colors.is_some());

        let colors = colors.unwrap();
        assert_eq!(colors.len(), 2);

        // First posting is negative (red)
        assert!(colors[0].color.red > 0.5);
        assert!(colors[0].color.green < 0.5);

        // Second posting is positive (green)
        assert!(colors[1].color.green > 0.5);
        assert!(colors[1].color.red < 0.5);
    }

    #[test]
    fn test_document_color_balance() {
        let source = r#"2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = DocumentColorParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let colors = handle_document_color(&params, source, &result, PositionEncoding::Utf16);
        assert!(colors.is_some());

        let colors = colors.unwrap();
        assert_eq!(colors.len(), 1);
        // Positive balance (green)
        assert!(colors[0].color.green > 0.5);
    }
}
