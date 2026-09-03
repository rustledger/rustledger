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

    let bytes = line.as_bytes();
    for pattern in &search_patterns {
        // Scan EVERY occurrence, not just the first. The number string can
        // appear inside the account name (`100` in `Assets:US-100:Bank`, `5`
        // in `Assets:Account5`) before the real amount; the old code looked at
        // only `line.find`'s first hit, so it either colored the in-account
        // digits or — when that hit failed the boundary check — gave up
        // without trying the real amount.
        let mut search_from = 0;
        while let Some(rel) = line[search_from..].find(pattern) {
            let pos = search_from + rel;
            let after_pos = pos + pattern.len();

            // An amount is a whitespace-separated token, so the char before it
            // must be whitespace (or line start). Requiring whitespace — rather
            // than merely "not alphanumeric" — rejects digits embedded in an
            // account name, where the preceding char is `-` or `:` (not alnum
            // but not whitespace either). Byte indexing is correct here: the
            // classification is ASCII-only, and `pos`/`after_pos` are byte
            // offsets from `find`.
            let before_ok = pos == 0 || bytes[pos - 1].is_ascii_whitespace();
            let after_ok = after_pos >= bytes.len() || !bytes[after_pos].is_ascii_digit();

            if before_ok && after_ok {
                let (sl, sc) = line_index.offset_to_position(line_start_byte + pos);
                let (el, ec) = line_index.offset_to_position(line_start_byte + after_pos);
                return Some(Range {
                    start: Position::new(sl, sc),
                    end: Position::new(el, ec),
                });
            }
            // Advance past this (rejected) match and keep looking.
            search_from = pos + 1;
        }
    }

    // Nothing matched literally. The line may spell the number with THOUSANDS
    // SEPARATORS -- `-1,999.00` where `amount_str` is always `-1999.00`,
    // because it comes from `Decimal::to_string()` and that never groups.
    //
    // This is not a rare spelling: `option "render_commas" "TRUE"` makes it
    // the canonical form, and `rledger format` writes it. So the provider was
    // declining to color exactly the text the formatter produces, coloring
    // only the amounts too small to carry a separator -- which in an aligned
    // block makes the column ragged, since an editor draws each color as a
    // swatch occupying a character cell (#2230).
    //
    // Compare whitespace-delimited tokens with separators removed, and return
    // the range over the WHOLE token as written so the swatch lands in the
    // same place for both spellings. Tokenising on whitespace keeps the
    // account-name guard above: `Assets:US-100:Bank` is one token and does not
    // compare equal to a bare number.
    for pattern in &search_patterns {
        for (pos, token) in whitespace_tokens(line) {
            if !token.contains(',') {
                continue;
            }
            let ungrouped: String = token.chars().filter(|c| *c != ',').collect();
            if ungrouped == *pattern {
                let after_pos = pos + token.len();
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

/// Whitespace-delimited tokens of `line`, each with its byte offset.
///
/// `str::split_whitespace` discards positions, and the color range needs
/// them. ASCII-only classification, matching the boundary check above.
fn whitespace_tokens(line: &str) -> impl Iterator<Item = (usize, &str)> {
    line.char_indices()
        .filter(|(i, c)| {
            !c.is_ascii_whitespace() && (*i == 0 || line.as_bytes()[i - 1].is_ascii_whitespace())
        })
        .map(move |(start, _)| {
            let end = line[start..]
                .find(char::is_whitespace)
                .map_or(line.len(), |off| start + off);
            (start, &line[start..end])
        })
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

    /// The reporter's ledger from #2230: `render_commas` is on, so `format`
    /// writes `-1,999.00` -- and the color provider skipped exactly those,
    /// coloring only the amounts small enough to have no separator.
    ///
    /// VS Code renders each color as an inline swatch occupying a character
    /// cell, so coloring some amounts on a line-aligned block and not others
    /// makes the column ragged. The provider was declining to color text the
    /// formatter itself produces.
    #[test]
    fn test_document_color_covers_amounts_with_thousands_separators() {
        let source = "2026-01-05 * \"P\" \"grouped and plain on purpose\"\n  \
                      Assets:Cash    -1,999.00 USD\n  \
                      Expenses:Fees   1,999.00 USD\n\
                      \n2026-01-06 * \"P\" \"plain only\"\n  \
                      Assets:Cash       -14.62 USD\n  \
                      Expenses:Fees      14.62 USD\n";
        let result = parse(source);
        let params = DocumentColorParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let colors = handle_document_color(&params, source, &result, PositionEncoding::Utf16)
            .expect("colors");
        assert_eq!(
            colors.len(),
            4,
            "every posting amount gets a color, grouped or not; got {colors:?}",
        );

        // The grouped amounts are on lines 1 and 2, and their ranges must
        // cover the WHOLE token including the separator -- a range that
        // stopped at the comma would put the swatch mid-number.
        let grouped: Vec<&ColorInformation> = colors
            .iter()
            .filter(|c| c.range.start.line == 1 || c.range.start.line == 2)
            .collect();
        assert_eq!(grouped.len(), 2, "both grouped amounts are colored");
        for c in &grouped {
            let width = c.range.end.character - c.range.start.character;
            assert_eq!(
                width,
                "-1,999.00".len() as u32 - u32::from(c.range.start.line == 2),
                "the range spans the full token, separators included: {:?}",
                c.range,
            );
        }

        // Sign still drives the color: first of each pair negative, second
        // positive. Without this the test would pass on a provider that
        // colored everything one color.
        assert!(colors[0].color.red > 0.5 && colors[0].color.green < 0.5);
        assert!(colors[1].color.green > 0.5 && colors[1].color.red < 0.5);
    }

    /// `balance` and `price` amounts go through the same `find_amount_range`,
    /// so they get separators too. Asserted separately because they are
    /// different arms of the directive match, and a fix applied to the posting
    /// arm alone would leave these two behind.
    #[test]
    fn test_document_color_covers_grouped_balance_and_price() {
        let source = "2026-01-01 open Assets:Cash USD\n\
                      2026-02-01 balance Assets:Cash  1,234.00 USD\n\
                      2026-02-02 price HOOL  2,500.00 USD\n";
        let result = parse(source);
        let params = DocumentColorParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let colors = handle_document_color(&params, source, &result, PositionEncoding::Utf16)
            .expect("colors");
        let lines: Vec<u32> = colors.iter().map(|c| c.range.start.line).collect();
        assert!(
            lines.contains(&1) && lines.contains(&2),
            "the grouped balance and price amounts must both be colored; got {colors:?}",
        );
        for c in &colors {
            let width = c.range.end.character - c.range.start.character;
            assert_eq!(
                width,
                "1,234.00".len() as u32,
                "the range spans the full grouped token: {:?}",
                c.range,
            );
        }
    }

    #[test]
    fn test_document_color_ignores_digits_in_account_name() {
        // `100` also appears inside the account `Assets:US-100:Bank`. The color
        // must land on the real amount (col 22), not the in-account digits.
        let source =
            "2024-01-15 * \"Test\"\n  Assets:US-100:Bank  100 USD\n  Equity:Opening  -100 USD\n";
        let result = parse(source);
        let params = DocumentColorParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let colors =
            handle_document_color(&params, source, &result, PositionEncoding::Utf16).unwrap();
        let first = colors
            .iter()
            .find(|c| c.range.start.line == 1)
            .expect("line 1 colored");
        assert_eq!(
            first.range.start.character, 22,
            "must color the amount, not the `100` inside the account name"
        );
    }

    #[test]
    fn test_document_color_amount_value_also_in_account() {
        // The amount `5` also occurs inside `Assets:Account5`. The real amount
        // must still be colored (the old code found the in-account `5` first,
        // failed the boundary check, and dropped the color entirely).
        let source = "2024-01-15 * \"Test\"\n  Assets:Account5  5 USD\n  Expenses:Food  -5 USD\n";
        let result = parse(source);
        let params = DocumentColorParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let colors =
            handle_document_color(&params, source, &result, PositionEncoding::Utf16).unwrap();
        assert_eq!(colors.len(), 2, "both amounts must be colored");
        let first = colors
            .iter()
            .find(|c| c.range.start.line == 1)
            .expect("line 1 colored");
        assert_eq!(
            first.range.start.character, 19,
            "color the real amount `5`, not the one in `Account5`"
        );
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
