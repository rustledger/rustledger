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
use std::path::{Path, PathBuf};

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

    // The document's own URI is what the resolve phase gets. NOT a path
    // string: `data` is JSON, a JSON string must be valid UTF-8, and a Unix
    // path is arbitrary bytes — so any path put here is `to_string_lossy`'d and
    // a directory whose name is not valid UTF-8 arrives as U+FFFD, naming
    // something that does not exist (#1877). A URI is ASCII by construction and
    // `proto::uri_to_path` inverts it exactly, so the bytes survive the trip.
    let line_index = LineIndex::new(source, encoding);

    for spanned in &parse_result.directives {
        if let Directive::Document(doc) = &spanned.value {
            // Create link for document path
            let path_str = doc.path.to_string();
            if let Some(link) =
                create_document_link(&line_index, spanned.span.start, &path_str, base_uri)
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
            && let Some(link) = parse_include_line(line, line_num as u32, &line_index, base_uri)
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
        // The ledger's own URI -> its directory, losslessly. `uri_to_path`
        // percent-decodes to real bytes, so a non-UTF-8 directory name survives
        // (#1877); the old payload carried a `to_string_lossy` path string and
        // turned those bytes into U+FFFD.
        let base_dir: Option<PathBuf> = data
            .get("base_uri")
            .and_then(|v| v.as_str())
            .and_then(|s| s.parse::<Uri>().ok())
            .and_then(|u| crate::uri_to_path(&u).ok())
            .and_then(|p| p.parent().map(Path::to_path_buf));
        let kind = data.get("kind").and_then(|v| v.as_str()).unwrap_or("file");

        // Resolve the path
        let resolved_path = resolve_full_path(path, base_dir.as_deref());

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
            // `glob` takes a `&str` pattern, so a PATTERN under a non-UTF-8
            // directory is still lossy — a limitation of that crate, not of the
            // payload. The matches it returns are `PathBuf` and are kept as
            // such, and the far commoner literal-path branch below is fully
            // lossless now, which is what #1877 was about.
            match resolved_path
                .as_ref()
                .map(|p| glob::glob(&p.to_string_lossy()))
            {
                Some(Ok(paths)) => {
                    let mut first: Option<PathBuf> = None;
                    let mut count = 0usize;
                    for entry in paths.flatten() {
                        if first.is_none() {
                            first = Some(entry);
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
        if let Some(ref full_path) = target_path {
            // Resolve through the OS before converting. `full_path` is a
            // `Path::join` of the ledger's base and a possibly-relative
            // include, so it can carry `..` — and POSIX applies `..` AFTER
            // symlink resolution, which no lexical pass can reproduce. With
            // `/base/view -> /base/real/ledger`, `/base/view/../attachments/x`
            // EXISTS (the kernel lands on `/base/real/attachments/x`) while any
            // textual normalization yields `/base/attachments/x`, which does
            // not. `path_to_uri` deliberately does not normalize for exactly
            // this reason, so the resolution belongs here, where we already
            // know whether the file is there.
            //
            // This also makes the target agree with the tooltip (which asks
            // `exists()`) and with the loader (which canonicalizes its source
            // map), so a link names the file `rledger check` actually reads.
            // When the file does NOT exist there is nothing to resolve and the
            // un-normalized path is the honest answer; the tooltip says
            // "File not found" in that case anyway.
            let resolved_target =
                std::fs::canonicalize(full_path).unwrap_or_else(|_| full_path.clone());
            match crate::path_to_uri(&resolved_target) {
                Ok(uri) => resolved.target = Some(uri),
                // Every sibling site warns; this one silently produced a link
                // with no target, which an editor renders as unclickable text
                // with no way to find out why.
                Err(e) => tracing::warn!(
                    "document link: no file URI for {}: {e}",
                    full_path.display()
                ),
            }
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
///
/// `Path::join`, matching `rustledger_loader`'s own `base_dir.join(include_path)`
/// exactly — including that a backslash is NOT a separator on Unix.
///
/// A previous `file_uri` helper mapped `\` to `/` unconditionally while
/// building the URI, so a Windows-authored `document "statements\jan.pdf"`
/// opened on Linux got a link pointing at `statements/jan.pdf`. That looks
/// friendlier and is wrong: the loader joins the literal string, so
/// `rledger check` looks for a file NAMED `statements\jan.pdf` and reports it
/// missing. The link went somewhere the ledger does not. The same code checked
/// `exists()` on the un-normalized path, so the tooltip already said "File not
/// found" while the target claimed otherwise — one helper disagreeing with both
/// the loader and itself.
///
/// Showing what the loader will actually do is the point of the feature, so a
/// dead link for a genuinely dead include is the correct answer. Fixing it
/// belongs in the loader, for both tools at once, or nowhere.
fn resolve_full_path(path: &str, base_dir: Option<&Path>) -> Option<PathBuf> {
    if Path::new(path).is_absolute() {
        Some(PathBuf::from(path))
    } else {
        base_dir.map(|base| base.join(path))
    }
}

/// Create a document link for a path found in source.
/// The target is deferred to the resolve phase for lazy verification.
fn create_document_link(
    line_index: &LineIndex<'_>,
    directive_start: usize,
    path: &str,
    base_uri: &Uri,
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
        "base_uri": base_uri.as_str(),
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
    base_uri: &Uri,
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
        "base_uri": base_uri.as_str(),
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
fn resolve_path_to_uri(path: &str, base_dir: Option<&Path>) -> Option<Uri> {
    let resolved = resolve_full_path(path, base_dir)?;
    crate::path_to_uri(Path::new(&resolved))
        .map_err(|e| {
            tracing::warn!("document link: no file URI for {}: {e}", resolved.display());
        })
        .ok()
}

#[cfg(test)]
/// A `base_uri` payload value for a DIRECTORY, as `handle_document_links`
/// builds it from the open document's URI.
///
/// The resolve phase takes the URI's PARENT, so a test fixture has to name a
/// file inside the directory it means — passing the directory itself would
/// resolve one level too high. `handle_document_links` passes the ledger's own
/// URI, hence the placeholder filename.
fn dir_uri(dir: &std::path::Path) -> String {
    crate::path_to_uri(&dir.join("main.beancount"))
        .expect("test dir is absolute")
        .as_str()
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::Position;

    #[test]
    fn test_parse_include_line() {
        let line = r#"include "accounts.beancount""#;
        let base_uri = crate::path_to_uri(&crate::test_abs("home/user/ledger")).expect("uri");
        let line_index = LineIndex::new(line, PositionEncoding::Utf16);

        let link = parse_include_line(line, 0, &line_index, &base_uri);
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
        let base = crate::test_abs("home/user/ledger");

        let uri = resolve_path_to_uri("accounts.beancount", Some(base.as_path()));
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
                "base_uri": dir_uri(&crate::test_abs("home/user/ledger")),
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
                "base_uri": dir_uri(dir.path()),
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
                "base_uri": dir_uri(dir.path()),
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
                "base_uri": dir_uri(dir.path()),
                "kind": "document",
            })),
        };
        let resolved = handle_document_link_resolve(link);
        let tooltip = resolved.tooltip.unwrap();
        // The key assertion: a literal document is NOT glob-detected, so it
        // resolves as an existing document rather than "no files match".
        assert!(
            tooltip.contains("Open document"),
            "document with [] in name must resolve literally: {tooltip}"
        );
        // And it is CLICKABLE. This used to say the bracketed path "won't
        // round-trip through a `file://` URI — a separate, pre-existing
        // encoding limitation — so we don't assert on `target`", which is why
        // the limitation survived: the one end-to-end test over the exact
        // reported symptom declined to look at the thing that was broken.
        // `url` leaves `[` and `]` literal and `fluent_uri` refuses them, so
        // `target` was `None` and the link was dead.
        let target = resolved
            .target
            .expect("a bracketed document must be clickable");
        assert!(
            target.as_str().ends_with("Statement%5B2024-01%5D.pdf"),
            "brackets must be percent-encoded: {}",
            target.as_str()
        );
        // Compared in ONE spelling, because three are in play for this file and
        // no two of them are the same string:
        //
        //   raw TempDir     macOS `/var/...`      Windows `...\RUNNER~1\...`
        //   canonicalized   macOS `/private/var/` Windows `\\?\C:\...`
        //   through the URI both prefixes dropped by `url`'s conversion
        //
        // The claim worth asserting is that the target NAMES THE FIXTURE, so
        // both sides are resolved and then compared. Asserting on any single
        // spelling passes on one platform and fails on the others, which is
        // how the raw-path version of this got through review.
        let target_path = crate::uri_to_path(&target).expect("target inverts");
        assert_eq!(
            target_path
                .canonical_for_loader_lookup()
                .expect("the target exists"),
            dir.path()
                .join(fname)
                .canonicalize()
                .expect("the fixture exists")
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
                "base_uri": dir_uri(dir.path()),
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
        let base = crate::test_abs("home/user/ledger");

        // Relative path: joined onto the base, with the platform's separator —
        // `Path::join`, exactly as the loader does it.
        let resolved = resolve_full_path("accounts.beancount", Some(base.as_path()));
        assert_eq!(
            resolved.as_deref(),
            Some(base.join("accounts.beancount").as_path())
        );

        // Absolute path: passed through untouched, base ignored.
        let absolute = crate::test_abs("absolute/path.beancount");
        let resolved = resolve_full_path(&absolute.to_string_lossy(), Some(base.as_path()));
        assert_eq!(resolved.as_deref(), Some(absolute.as_path()));

        // No base dir
        assert_eq!(resolve_full_path("relative.beancount", None), None);
    }
}

#[cfg(test)]
mod uri_resolution_tests {
    use super::*;
    use std::str::FromStr;

    /// A relative document resolves under a directory whose name is NOT valid
    /// UTF-8 (#1877).
    ///
    /// A Unix path is arbitrary bytes. The link payload is JSON, and a JSON
    /// string must be valid UTF-8, so the old `base_dir` path string went
    /// through `to_string_lossy` and every non-UTF-8 byte became U+FFFD — the
    /// payload named a directory that does not exist, and every relative
    /// `include`/`document` under it rendered "⚠ File not found" for a file
    /// that was right there.
    ///
    /// Carrying the ledger's URI instead is lossless: percent-encoding is
    /// ASCII, and `uri_to_path` decodes back to the original bytes.
    ///
    /// `cfg(target_os = "linux")`, not `cfg(unix)`, and not a runtime skip.
    ///
    /// The fixture cannot be CREATED on the other two CI platforms, so the bug
    /// is unreachable there rather than untested:
    ///
    /// - macOS: APFS/HFS+ enforce valid UTF-8 filenames. `create_dir_all`
    ///   fails with `EILSEQ` "Illegal byte sequence" — measured, this test
    ///   failed exactly that way on `macos-latest` before the gate.
    /// - Windows: filenames are UTF-16; the byte sequence has no spelling.
    ///
    /// A runtime "skip if creation fails" would have been the tempting fix and
    /// the wrong one — CLAUDE.md's rule is that an availability-gated test
    /// which silently skips is a test that runs nowhere. A `cfg` states the
    /// platform property instead, and the Linux leg always runs it.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_relative_document_resolves_under_a_non_utf8_directory() {
        use std::os::unix::ffi::OsStrExt;

        // 0xFF is not valid UTF-8 in any position.
        let root = std::env::temp_dir().join(format!("rl-1877-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let dir = root.join(std::ffi::OsStr::from_bytes(b"led\xffger"));
        std::fs::create_dir_all(&dir).expect("create non-UTF-8 dir");
        std::fs::write(dir.join("invoice.pdf"), b"pdf").expect("write doc");

        assert!(
            std::str::from_utf8(dir.as_os_str().as_bytes()).is_err(),
            "the fixture must actually be non-UTF-8, or this proves nothing"
        );

        let link = DocumentLink {
            range: lsp_types::Range {
                start: lsp_types::Position::new(0, 9),
                end: lsp_types::Position::new(0, 30),
            },
            target: None,
            tooltip: None,
            data: Some(serde_json::json!({
                "path": "invoice.pdf",
                "base_uri": dir_uri(&dir),
                "kind": "document",
            })),
        };
        let resolved = handle_document_link_resolve(link);

        let tooltip = resolved.tooltip.clone().unwrap_or_default();
        assert!(
            tooltip.starts_with("Open document"),
            "the file exists, so the tooltip must say so — got {tooltip:?}"
        );
        let target = resolved
            .target
            .expect("an existing document must be clickable");
        let target_path = crate::uri_to_path(&target).expect("target inverts");
        assert_eq!(
            target_path
                .canonical_for_loader_lookup()
                .expect("target exists"),
            dir.join("invoice.pdf")
                .canonicalize()
                .expect("fixture exists"),
            "the target must name the real file, not a U+FFFD-mangled path"
        );

        let _ = std::fs::remove_dir_all(&root);
    }

    /// A `..` that crosses a symlink resolves to the file the OS finds.
    ///
    /// POSIX applies `..` AFTER symlink resolution; a lexical pass does it
    /// before, and the two name different files. `path_to_uri` briefly
    /// normalized lexically so the two converters would be exact inverses,
    /// which made this link's tooltip say "Open document" (it asks `exists()`,
    /// so the OS answered) while its target named a file that does not exist.
    ///
    /// `cfg(unix)`: creating a symlink on Windows needs elevation or developer
    /// mode, so the fixture cannot be built there.
    #[cfg(unix)]
    #[test]
    fn a_dot_dot_across_a_symlink_resolves_the_way_the_os_does() {
        let root = std::env::temp_dir().join(format!("rl-symlink-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(root.join("real/ledger")).expect("mkdir");
        std::fs::create_dir_all(root.join("real/attachments")).expect("mkdir");
        std::fs::write(root.join("real/attachments/jan.pdf"), b"pdf").expect("write");
        let view = root.join("view");
        std::os::unix::fs::symlink(root.join("real/ledger"), &view).expect("symlink");

        let link = DocumentLink {
            range: lsp_types::Range {
                start: lsp_types::Position::new(0, 9),
                end: lsp_types::Position::new(0, 30),
            },
            target: None,
            tooltip: None,
            data: Some(serde_json::json!({
                "path": "../attachments/jan.pdf",
                "base_uri": dir_uri(&view),
                "kind": "document",
            })),
        };
        let resolved = handle_document_link_resolve(link);

        let tooltip = resolved.tooltip.clone().unwrap_or_default();
        assert!(
            tooltip.starts_with("Open document"),
            "the OS finds this file, so the tooltip must say so: {tooltip}"
        );
        let target = resolved
            .target
            .expect("a resolvable document must be clickable");
        let target_path = crate::uri_to_path(&target).expect("target inverts");
        assert!(
            target_path.as_path().exists(),
            "the tooltip says the file exists, so the target must name one that \
             does: {}",
            target.as_str()
        );
        assert_eq!(
            target_path.as_path(),
            root.join("real/attachments/jan.pdf")
                .canonicalize()
                .expect("canon"),
            "and it must be the file the OS resolves to"
        );

        let _ = std::fs::remove_dir_all(&root);
    }

    /// A relative `document` path must resolve under a directory whose URI is
    /// percent-encoded (issue #1866).
    ///
    /// The directory has a SPACE in it deliberately. The report came from
    /// Windows, where `file:///C:/…` leaves both a leading slash and a `%3A`
    /// drive colon, so no relative document path ever resolved. But the cause is
    /// the URI decoding, not the platform: any encoded character breaks it, and
    /// a space reproduces the same failure on Linux and macOS. Testing the
    /// portable trigger means this runs everywhere, rather than on the one OS CI
    /// might not have.
    #[test]

    fn a_relative_document_resolves_under_a_percent_encoded_directory() {
        // Unique per process: a fixed name collides when two `cargo test`
        // processes run at once, or when a previous failed run left the
        // directory behind.
        let dir = std::env::temp_dir().join(format!("rledger lsp 1866 {}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create fixture dir");
        std::fs::write(dir.join("neighbor.txt"), b"invoice").expect("write doc");
        let ledger = dir.join("main.beancount");
        let source = "2020-01-01 open Expenses:Probe\n\
                      2026-07-27 document Expenses:Probe \"neighbor.txt\"\n";
        std::fs::write(&ledger, source).expect("write ledger");

        // The URI an editor actually sends. Built through `url` rather than by
        // hand: an editor percent-encodes the space AND, on Windows, produces
        // the three-slash drive form, which `format!("file://{}", ..)` does not.
        // This is the client's job, not `proto`'s, so it is spelled out here
        // rather than borrowed from `path_to_uri` — a test that builds its
        // input with the code under test asserts only self-consistency.
        let uri_str = url::Url::from_file_path(&ledger)
            .expect("fixture path is absolute")
            .to_string();
        assert!(
            uri_str.contains("%20"),
            "the fixture must exercise encoding"
        );
        let uri = Uri::from_str(&uri_str).expect("uri");

        let parse = rustledger_parser::parse(source);
        let params = DocumentLinkParams {
            text_document: lsp_types::TextDocumentIdentifier { uri },
            work_done_progress_params: lsp_types::WorkDoneProgressParams::default(),
            partial_result_params: lsp_types::PartialResultParams::default(),
        };
        let links = handle_document_links(&params, source, &parse, PositionEncoding::Utf16)
            .expect("a document link");
        assert_eq!(links.len(), 1, "{links:?}");

        let resolved = handle_document_link_resolve(links.into_iter().next().unwrap());
        let tooltip = resolved.tooltip.unwrap_or_default();
        assert!(
            tooltip.starts_with("Open document:"),
            "the file exists, so the link must be openable, got {tooltip:?}"
        );
        // ...and the target must be a URI the editor can actually open, which
        // means the space is encoded rather than embedded raw.
        let target = resolved.target.expect("a target").as_str().to_string();
        assert!(target.contains("%20"), "target not encoded: {target}");
        assert!(!target.contains(' '), "raw space in a URI: {target}");

        let _ = std::fs::remove_dir_all(&dir);
    }
}
