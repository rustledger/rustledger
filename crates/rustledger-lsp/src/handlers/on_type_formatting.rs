//! On-type formatting handler for auto-formatting as you type.
//!
//! Triggers on specific characters to:
//! - Auto-align amounts when entering numbers
//! - Clean up whitespace after newlines

use lsp_types::{DocumentOnTypeFormattingParams, Position, Range, TextEdit};

use super::utils::PositionEncoding;

/// First trigger character for on-type formatting.
pub const FIRST_TRIGGER_CHARACTER: &str = "\n";
/// Additional trigger characters for on-type formatting.
pub const MORE_TRIGGER_CHARACTERS: &[&str] = &[" "];

/// Convert a column in the negotiated encoding to a byte offset into `line`.
/// Returns `line.len()` when `col` overshoots the line.
fn col_to_byte(line: &str, col: usize, encoding: PositionEncoding) -> usize {
    let mut acc = 0usize;
    let mut byte = 0usize;
    for ch in line.chars() {
        if acc >= col {
            return byte;
        }
        let u = match encoding {
            PositionEncoding::Utf8 => ch.len_utf8(),
            PositionEncoding::Utf16 => ch.len_utf16(),
        };
        if acc + u > col {
            // col lands inside a multi-unit char — bail to current byte.
            return byte;
        }
        acc += u;
        byte += ch.len_utf8();
    }
    byte
}

/// Encoded length of an ASCII-or-multibyte string in the negotiated encoding.
fn encoded_len(s: &str, encoding: PositionEncoding) -> u32 {
    match encoding {
        PositionEncoding::Utf8 => s.len() as u32,
        PositionEncoding::Utf16 => s.encode_utf16().count() as u32,
    }
}

/// Handle an on-type formatting request.
pub fn handle_on_type_formatting(
    params: &DocumentOnTypeFormattingParams,
    source: &str,
    encoding: PositionEncoding,
) -> Option<Vec<TextEdit>> {
    let position = params.text_document_position.position;
    let ch = &params.ch;

    match ch.as_str() {
        "\n" => handle_newline_formatting(source, position, encoding),
        " " => handle_space_formatting(source, position, encoding),
        _ => None,
    }
}

/// Handle formatting after a newline.
/// If the previous line was a transaction header, indent the new posting line.
fn handle_newline_formatting(
    source: &str,
    position: Position,
    encoding: PositionEncoding,
) -> Option<Vec<TextEdit>> {
    let lines: Vec<&str> = source.lines().collect();
    let prev_line_idx = position.line.saturating_sub(1) as usize;

    if prev_line_idx >= lines.len() {
        return None;
    }

    let prev_line = lines[prev_line_idx];

    // Check if previous line is a transaction header (starts with date and has *)
    if is_transaction_header(prev_line) {
        // The current line should be indented for a posting
        let current_line_idx = position.line as usize;
        let current_line = lines.get(current_line_idx).unwrap_or(&"");

        // If current line is empty or has less than 2 spaces, add proper indentation
        let leading_spaces = current_line.len() - current_line.trim_start().len();
        if leading_spaces < 2 {
            let indent = "  "; // Standard Beancount indent
            let leading_in_encoding = encoded_len(&current_line[..leading_spaces], encoding);
            return Some(vec![TextEdit {
                range: Range {
                    start: Position::new(position.line, 0),
                    end: Position::new(position.line, leading_in_encoding),
                },
                new_text: indent.to_string(),
            }]);
        }
    }

    // Check if previous line is a posting and current line should also be indented
    if is_posting_line(prev_line) {
        let current_line_idx = position.line as usize;
        let current_line = lines.get(current_line_idx).unwrap_or(&"");

        let leading_spaces = current_line.len() - current_line.trim_start().len();
        if leading_spaces < 2 && current_line.trim().is_empty() {
            // Keep same indentation as previous posting
            let prev_indent = prev_line.len() - prev_line.trim_start().len();
            let indent = " ".repeat(prev_indent);
            let leading_in_encoding = encoded_len(&current_line[..leading_spaces], encoding);
            return Some(vec![TextEdit {
                range: Range {
                    start: Position::new(position.line, 0),
                    end: Position::new(position.line, leading_in_encoding),
                },
                new_text: indent,
            }]);
        }
    }

    None
}

/// Handle formatting after a space.
/// Used to help align amounts in postings.
fn handle_space_formatting(
    source: &str,
    position: Position,
    encoding: PositionEncoding,
) -> Option<Vec<TextEdit>> {
    let lines: Vec<&str> = source.lines().collect();
    let line_idx = position.line as usize;
    let line = lines.get(line_idx)?;

    // Check if we're in a posting line
    if !is_posting_line(line) {
        return None;
    }

    // Check if we just typed a space after an account name
    let byte_col = col_to_byte(line, position.character as usize, encoding);
    if byte_col < 2 {
        return None;
    }

    let before_cursor = &line[..byte_col];

    // Look for pattern: "  Account:Name "
    // If the user just typed a space after an account, we can help align
    if before_cursor.trim_start().contains(':') && before_cursor.ends_with(' ') {
        // Check if there's already proper spacing (at least 2 spaces before amount)
        let trimmed = before_cursor.trim_end();
        let trailing_spaces = before_cursor.len() - trimmed.len();

        // If there's exactly 1 space and this looks like it's before an amount,
        // add another space for the typical 2-space gap
        if trailing_spaces == 1 {
            // Check if what follows looks like it could be an amount
            let after_cursor = &line[byte_col..];
            if after_cursor
                .trim_start()
                .starts_with(|c: char| c == '-' || c.is_ascii_digit())
            {
                return Some(vec![TextEdit {
                    range: Range {
                        start: position,
                        end: position,
                    },
                    new_text: " ".to_string(), // Add one more space
                }]);
            }
        }
    }

    None
}

/// Check if a line is a transaction header.
fn is_transaction_header(line: &str) -> bool {
    let trimmed = line.trim();

    // Must start with a date-like pattern
    if trimmed.len() < 10 {
        return false;
    }

    let first_char = trimmed.chars().next().unwrap_or(' ');
    if !first_char.is_ascii_digit() {
        return false;
    }

    // Look for transaction flag (* or !)
    trimmed.contains(" * ") || trimmed.contains(" ! ")
}

/// Check if a line is a posting line.
fn is_posting_line(line: &str) -> bool {
    let trimmed = line.trim();

    // Posting lines are indented and start with an account type
    line.starts_with("  ")
        && (trimmed.starts_with("Assets")
            || trimmed.starts_with("Liabilities")
            || trimmed.starts_with("Equity")
            || trimmed.starts_with("Income")
            || trimmed.starts_with("Expenses"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_transaction_header() {
        assert!(is_transaction_header("2024-01-15 * \"Coffee Shop\""));
        assert!(is_transaction_header("2024-01-15 ! \"Pending\""));
        assert!(!is_transaction_header("  Assets:Bank"));
        assert!(!is_transaction_header("2024-01-01 open Assets:Bank"));
    }

    #[test]
    fn test_is_posting_line() {
        assert!(is_posting_line("  Assets:Bank  -5.00 USD"));
        assert!(is_posting_line("  Expenses:Food"));
        assert!(!is_posting_line("2024-01-15 * \"Coffee\""));
        assert!(!is_posting_line("Assets:Bank")); // Not indented
    }

    #[test]
    fn test_newline_after_transaction() {
        let source = "2024-01-15 * \"Coffee\"\n";
        let params = DocumentOnTypeFormattingParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier {
                    uri: "file:///test.beancount".parse().unwrap(),
                },
                position: Position::new(1, 0),
            },
            ch: "\n".to_string(),
            options: lsp_types::FormattingOptions {
                tab_size: 2,
                insert_spaces: true,
                properties: Default::default(),
                trim_trailing_whitespace: None,
                insert_final_newline: None,
                trim_final_newlines: None,
            },
        };

        let result = handle_on_type_formatting(&params, source, PositionEncoding::Utf16);
        assert!(result.is_some());

        let edits = result.unwrap();
        assert_eq!(edits.len(), 1);
        assert_eq!(edits[0].new_text, "  "); // Two-space indent
    }
}
