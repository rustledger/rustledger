//! Document links handler for clickable paths.
//!
//! Provides clickable links for:
//! - `include` directive paths
//! - `document` directive paths
//!
//! Supports resolve for lazy-loading targets and verifying file existence.

use lsp_types::{DocumentLink, DocumentLinkParams, Range, Uri};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::path::Path;

use super::utils::{LineIndex, PositionEncoding};

/// Handle a document links request.
pub fn handle_document_links(
    params: &DocumentLinkParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<DocumentLink>> {
    let mut links = Vec::new();
    let base_uri = &params.text_document.uri;

    // Get the base directory from the document URI
    let base_dir = get_base_directory(base_uri);
    let line_index = LineIndex::new(source, encoding);

    for spanned in &parse_result.directives {
        if let Directive::Document(doc) = &spanned.value {
            // Create link for document path
            let path_str = doc.path.to_string();
            if let Some(link) =
                create_document_link(&line_index, spanned.span.start, &path_str, &base_dir)
            {
                links.push(link);
            }
        }
    }

    // Also look for include directives in comments/options
    // (includes are typically parsed as options, not directives)
    for (line_num, line) in source.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("include")
            && let Some(link) = parse_include_line(line, line_num as u32, &line_index, &base_dir)
        {
            links.push(link);
        }
    }

    if links.is_empty() { None } else { Some(links) }
}

/// Handle a document link resolve request.
/// Resolves the target URI and verifies the file exists.
pub fn handle_document_link_resolve(link: DocumentLink) -> DocumentLink {
    let mut resolved = link.clone();

    if let Some(data) = &link.data {
        let path = data.get("path").and_then(|v| v.as_str()).unwrap_or("");
        let base_dir = data
            .get("base_dir")
            .and_then(|v| v.as_str())
            .map(String::from);
        let kind = data.get("kind").and_then(|v| v.as_str()).unwrap_or("file");

        // Resolve the path
        let resolved_path = resolve_full_path(path, &base_dir);

        // Check if file exists
        let exists = resolved_path
            .as_ref()
            .map(|p| Path::new(p).exists())
            .unwrap_or(false);

        // Set target URI
        if let Some(ref full_path) = resolved_path
            && let Ok(uri) = format!("file://{}", full_path).parse::<Uri>()
        {
            resolved.target = Some(uri);
        }

        // Set tooltip based on existence
        let tooltip = if exists {
            match kind {
                "include" => format!("Open included file: {}", path),
                "document" => format!("Open document: {}", path),
                _ => format!("Open {}", path),
            }
        } else {
            format!("⚠ File not found: {}", path)
        };
        resolved.tooltip = Some(tooltip);
    }

    resolved
}

/// Resolve a path to its full filesystem path.
fn resolve_full_path(path: &str, base_dir: &Option<String>) -> Option<String> {
    if Path::new(path).is_absolute() {
        Some(path.to_string())
    } else if let Some(base) = base_dir {
        let base_path = Path::new(base);
        Some(base_path.join(path).to_string_lossy().to_string())
    } else {
        None
    }
}

/// Get the base directory from a file URI.
fn get_base_directory(uri: &Uri) -> Option<String> {
    let uri_str = uri.as_str();
    if let Some(path_str) = uri_str.strip_prefix("file://") {
        let path = Path::new(path_str);
        path.parent().map(|p| p.to_string_lossy().to_string())
    } else {
        None
    }
}

/// Create a document link for a path found in source.
/// The target is deferred to the resolve phase for lazy verification.
fn create_document_link(
    line_index: &LineIndex<'_>,
    directive_start: usize,
    path: &str,
    base_dir: &Option<String>,
) -> Option<DocumentLink> {
    let (start_line, _) = line_index.offset_to_position(directive_start);

    // Find the path in the directive line
    let line = line_index.line_text(start_line)?;

    // Find the quoted path
    let quote_start = line.find('"')?;
    let after_quote = &line[quote_start + 1..];
    let quote_end = after_quote.find('"')?;

    let path_in_line = &after_quote[..quote_end];
    if path_in_line != path {
        return None;
    }

    // Convert the path's byte offsets to encoding-aware `Position`s. Emitting
    // `quote_start`/`path.len()` directly (raw byte offsets) misplaces the link
    // under UTF-16 whenever the line contains multibyte characters (a Unicode
    // account name or an accented path).
    let quote_byte = quote_start + 1;
    let start = line_index.byte_in_line_to_position(start_line, quote_byte)?;
    let end = line_index.byte_in_line_to_position(start_line, quote_byte + path.len())?;

    // Store data for resolve - defer target resolution
    let data = serde_json::json!({
        "path": path,
        "base_dir": base_dir,
        "kind": "document",
    });

    Some(DocumentLink {
        range: Range { start, end },
        target: None,  // Resolved lazily
        tooltip: None, // Resolved lazily
        data: Some(data),
    })
}

/// Parse an include line and create a document link.
/// The target is deferred to the resolve phase for lazy verification.
fn parse_include_line(
    line: &str,
    line_num: u32,
    line_index: &LineIndex<'_>,
    base_dir: &Option<String>,
) -> Option<DocumentLink> {
    // Match patterns like: include "path/to/file.beancount"
    let trimmed = line.trim();
    if !trimmed.starts_with("include") {
        return None;
    }

    // Find the quoted path
    let quote_start = line.find('"')?;
    let after_quote = &line[quote_start + 1..];
    let quote_end = after_quote.find('"')?;

    let path = &after_quote[..quote_end];
    // Convert byte offsets to encoding-aware `Position`s (see
    // `create_document_link`): raw byte columns misplace the link under UTF-16.
    let quote_byte = quote_start + 1;
    let start = line_index.byte_in_line_to_position(line_num, quote_byte)?;
    let end = line_index.byte_in_line_to_position(line_num, quote_byte + path.len())?;

    // Store data for resolve - defer target resolution
    let data = serde_json::json!({
        "path": path,
        "base_dir": base_dir,
        "kind": "include",
    });

    Some(DocumentLink {
        range: Range { start, end },
        target: None,  // Resolved lazily
        tooltip: None, // Resolved lazily
        data: Some(data),
    })
}

/// Resolve a relative path to a file URI (used in tests).
#[cfg(test)]
fn resolve_path_to_uri(path: &str, base_dir: &Option<String>) -> Option<Uri> {
    let resolved = resolve_full_path(path, base_dir)?;
    format!("file://{}", resolved).parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::Position;

    #[test]
    fn test_parse_include_line() {
        let line = r#"include "accounts.beancount""#;
        let base_dir = Some("/home/user/ledger".to_string());
        let line_index = LineIndex::new(line, PositionEncoding::Utf16);

        let link = parse_include_line(line, 0, &line_index, &base_dir);
        assert!(link.is_some());

        let link = link.unwrap();
        assert_eq!(link.range.start.character, 9); // After the opening quote
        assert_eq!(link.range.end.character, 27); // "accounts.beancount" is 18 chars

        // Target should be None (resolved lazily)
        assert!(link.target.is_none());
        // Data should contain the path info
        assert!(link.data.is_some());
    }

    #[test]
    fn test_document_link_columns_are_utf16() {
        // A multibyte account name precedes the path, and the path itself
        // contains multibyte chars. Under UTF-16, columns must count code
        // units, not bytes — otherwise the clickable span is misplaced.
        let source = "2024-01-02 document Assets:Café \"réçu.pdf\"\n";
        let result = rustledger_parser::parse(source);
        let params = DocumentLinkParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///x/main.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let links =
            handle_document_links(&params, source, &result, PositionEncoding::Utf16).unwrap();
        let link = &links[0];
        // The opening quote sits at UTF-16 col 32 (`Café` is 4 units, not 5
        // bytes), so the path starts at col 33; `réçu.pdf` is 8 UTF-16 units →
        // end (exclusive) at col 41. Raw byte offsets would give 34/44 — the
        // pre-fix bug.
        assert_eq!(
            link.range.start.character, 33,
            "path start must be a UTF-16 column"
        );
        assert_eq!(
            link.range.end.character, 41,
            "path end must be a UTF-16 column"
        );
    }

    #[test]
    fn test_resolve_path_to_uri() {
        let base_dir = Some("/home/user/ledger".to_string());

        let uri = resolve_path_to_uri("accounts.beancount", &base_dir);
        assert!(uri.is_some());
        assert!(uri.unwrap().as_str().contains("accounts.beancount"));
    }

    #[test]
    fn test_document_link_resolve() {
        // Create a link with data (as returned by handle_document_links)
        let link = DocumentLink {
            range: Range {
                start: Position::new(0, 9),
                end: Position::new(0, 27),
            },
            target: None,
            tooltip: None,
            data: Some(serde_json::json!({
                "path": "accounts.beancount",
                "base_dir": "/home/user/ledger",
                "kind": "include",
            })),
        };

        let resolved = handle_document_link_resolve(link);

        // Should now have a target
        assert!(resolved.target.is_some());
        let target = resolved.target.unwrap();
        assert!(target.as_str().contains("accounts.beancount"));

        // Should have a tooltip (file won't exist, so will show warning)
        assert!(resolved.tooltip.is_some());
        let tooltip = resolved.tooltip.unwrap();
        assert!(tooltip.contains("not found") || tooltip.contains("Open"));
    }

    #[test]
    fn test_resolve_full_path() {
        let base_dir = Some("/home/user/ledger".to_string());

        // Relative path
        let resolved = resolve_full_path("accounts.beancount", &base_dir);
        assert!(resolved.is_some());
        assert_eq!(resolved.unwrap(), "/home/user/ledger/accounts.beancount");

        // Absolute path
        let resolved = resolve_full_path("/absolute/path.beancount", &base_dir);
        assert!(resolved.is_some());
        assert_eq!(resolved.unwrap(), "/absolute/path.beancount");

        // No base dir
        let resolved = resolve_full_path("relative.beancount", &None);
        assert!(resolved.is_none());
    }
}
