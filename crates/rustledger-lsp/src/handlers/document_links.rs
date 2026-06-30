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

        // A glob `include` (e.g. `transactions/*.bean`) is valid — the loader
        // expands it on load — so a literal path-exists check wrongly reports
        // "File not found" for the pattern (issue #1647). Only `include` paths
        // are glob-expanded by the loader; `document` paths are always literal
        // and may legitimately contain `[`/`*`/`?` in real filenames, so never
        // glob-detect those. `is_glob_pattern` is the loader's own detector,
        // shared so the two cannot disagree.
        let is_glob = kind == "include" && rustledger_loader::is_glob_pattern(path);

        // For a glob, enumerate matches once: keep only the FIRST match as an
        // owned String (the clickable target) plus a count — no String-per-match
        // allocation. `pattern_ok` distinguishes a syntactically invalid pattern
        // (the loader reports a distinct error) from one that matches nothing.
        let (glob_first, glob_count, pattern_ok) = if is_glob {
            match resolved_path.as_ref().map(|p| glob::glob(p)) {
                Some(Ok(paths)) => {
                    let mut first = None;
                    let mut count = 0usize;
                    for entry in paths.flatten() {
                        if first.is_none() {
                            first = Some(entry.to_string_lossy().into_owned());
                        }
                        count += 1;
                    }
                    (first, count, true)
                }
                Some(Err(_)) => (None, 0, false),
                None => (None, 0, true),
            }
        } else {
            (None, 0, true)
        };

        let exists = if is_glob {
            glob_count > 0
        } else {
            resolved_path
                .as_ref()
                .map(|p| Path::new(p).exists())
                .unwrap_or(false)
        };

        // Set target URI. For a glob, point at the first matched file so the
        // link is still clickable; otherwise the resolved path itself.
        let target_path = if is_glob {
            glob_first
        } else {
            resolved_path.clone()
        };
        if let Some(ref full_path) = target_path
            && let Ok(uri) = format!("file://{}", full_path).parse::<Uri>()
        {
            resolved.target = Some(uri);
        }

        // Set tooltip based on existence
        let tooltip = if is_glob {
            if !pattern_ok {
                format!("⚠ Invalid include pattern: {}", path)
            } else if exists {
                format!("Open {} included file(s) matching: {}", glob_count, path)
            } else {
                format!("⚠ No files match include pattern: {}", path)
            }
        } else if exists {
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
    fn test_document_link_resolve_glob_include() {
        // #1647: a glob include must not show "File not found" — the loader
        // expands it on load. With matching files present, the resolved link
        // reports the match count and stays clickable.
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("a.bean"), "").unwrap();
        std::fs::write(dir.path().join("b.bean"), "").unwrap();

        let link = DocumentLink {
            range: Range {
                start: Position::new(0, 9),
                end: Position::new(0, 20),
            },
            target: None,
            tooltip: None,
            data: Some(serde_json::json!({
                "path": "*.bean",
                "base_dir": dir.path().to_string_lossy(),
                "kind": "include",
            })),
        };

        let resolved = handle_document_link_resolve(link);
        let tooltip = resolved.tooltip.unwrap();
        assert!(
            !tooltip.contains("not found"),
            "glob include wrongly reported missing: {tooltip}"
        );
        assert!(tooltip.contains("matching"), "tooltip: {tooltip}");
        assert!(
            resolved.target.is_some(),
            "glob link should still be clickable"
        );
    }

    #[test]
    fn test_document_link_resolve_glob_no_match() {
        // A glob that matches nothing is the one case that *should* warn.
        let dir = tempfile::tempdir().unwrap();
        let link = DocumentLink {
            range: Range {
                start: Position::new(0, 9),
                end: Position::new(0, 20),
            },
            target: None,
            tooltip: None,
            data: Some(serde_json::json!({
                "path": "*.bean",
                "base_dir": dir.path().to_string_lossy(),
                "kind": "include",
            })),
        };
        let resolved = handle_document_link_resolve(link);
        let tooltip = resolved.tooltip.unwrap();
        assert!(tooltip.contains("No files match"), "tooltip: {tooltip}");
    }

    #[test]
    fn test_document_link_resolve_document_with_glob_char_is_literal() {
        // #1651 review: a `document` whose real filename contains a glob
        // metacharacter (legal on Linux/macOS) must be treated literally, never
        // glob-expanded — otherwise an existing document link falsely 404s.
        let dir = tempfile::tempdir().unwrap();
        let fname = "Statement[2024-01].pdf";
        std::fs::write(dir.path().join(fname), "").unwrap();

        let link = DocumentLink {
            range: Range {
                start: Position::new(0, 9),
                end: Position::new(0, 30),
            },
            target: None,
            tooltip: None,
            data: Some(serde_json::json!({
                "path": fname,
                "base_dir": dir.path().to_string_lossy(),
                "kind": "document",
            })),
        };
        let resolved = handle_document_link_resolve(link);
        let tooltip = resolved.tooltip.unwrap();
        // The key assertion: a literal document is NOT glob-detected, so it
        // resolves as an existing document rather than "no files match". (The
        // bracketed path won't round-trip through a `file://` URI — a separate,
        // pre-existing encoding limitation — so we don't assert on `target`.)
        assert!(
            tooltip.contains("Open document"),
            "document with [] in name must resolve literally: {tooltip}"
        );
    }

    #[test]
    fn test_document_link_resolve_invalid_glob_pattern() {
        // An unbalanced `[` is syntactically invalid — reported as such, not as a
        // misleading "no files match".
        let dir = tempfile::tempdir().unwrap();
        let link = DocumentLink {
            range: Range {
                start: Position::new(0, 9),
                end: Position::new(0, 20),
            },
            target: None,
            tooltip: None,
            data: Some(serde_json::json!({
                "path": "foo[.bean",
                "base_dir": dir.path().to_string_lossy(),
                "kind": "include",
            })),
        };
        let resolved = handle_document_link_resolve(link);
        let tooltip = resolved.tooltip.unwrap();
        assert!(
            tooltip.contains("Invalid include pattern"),
            "tooltip: {tooltip}"
        );
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
