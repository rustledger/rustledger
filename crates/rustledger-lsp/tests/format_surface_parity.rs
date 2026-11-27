//! The LSP's formatting requests agree with `rledger format`, and never
//! change what a file means.
//!
//! * **Clean files.** `textDocument/formatting` produces exactly the CLI's
//!   output (`try_format_source`, the entry `rledger format` calls), with
//!   CRLF re-injected on a CRLF document (the LSP's documented difference:
//!   it keeps a Windows file's line endings). `textDocument/rangeFormatting`
//!   over the whole document produces the same. Over any part of it, it
//!   keeps the file's meaning and moves toward the same canonical form:
//!   formatting its result whole gives the CLI's output.
//! * **Broken files.** The CLI refuses them. `textDocument/formatting` falls
//!   back to surface cleanup (trailing blanks, leading tabs), and range
//!   formatting to formatting the selected directives. Neither may change a
//!   parse error, a value or a comment.
//!
//! Formatter-specific on purpose: the general LSP-vs-CLI surface-parity test
//! lives elsewhere.

use std::fs;
use std::path::{Path, PathBuf};

use lsp_types::{
    DocumentFormattingParams, DocumentRangeFormattingParams, Position, Range, TextEdit,
};
use proptest::prelude::*;
use rustledger_lsp::handlers::formatting::handle_formatting;
use rustledger_lsp::handlers::range_formatting::handle_range_formatting;
use rustledger_lsp::handlers::utils::{LineIndex, PositionEncoding};
use rustledger_parser::format::{GroupingStyle, lf_to_crlf_outside_strings, try_format_source};
use rustledger_parser::parse;

#[path = "../../rustledger-parser/fuzz/fuzz_targets/common/format_roundtrip.rs"]
#[allow(dead_code)]
mod format_roundtrip;

#[path = "../../rustledger-parser/tests/format_roundtrip_common/ledger_gen.rs"]
mod ledger_gen;

const ENCODINGS: [PositionEncoding; 2] = [PositionEncoding::Utf16, PositionEncoding::Utf8];

fn uri() -> lsp_types::TextDocumentIdentifier {
    lsp_types::TextDocumentIdentifier {
        uri: "file:///ledger.beancount".parse().expect("uri"),
    }
}

/// `source` with `edits` applied, as a client applies them: all positions
/// refer to the original text.
fn apply(source: &str, edits: &[TextEdit], encoding: PositionEncoding) -> String {
    let index = LineIndex::new(source, encoding);
    let mut spans: Vec<(usize, usize, &str)> = edits
        .iter()
        .map(|e| {
            let start = index
                .position_to_offset(e.range.start.line, e.range.start.character)
                .expect("edit start in bounds");
            let end = index
                .position_to_offset(e.range.end.line, e.range.end.character)
                .expect("edit end in bounds");
            assert!(start <= end, "inverted edit {e:?}");
            (start, end, e.new_text.as_str())
        })
        .collect();
    spans.sort_by_key(|&(s, e, _)| (s, e));
    for w in spans.windows(2) {
        assert!(w[0].1 <= w[1].0, "overlapping edits {w:?}");
    }
    let mut out = source.to_string();
    for (start, end, text) in spans.into_iter().rev() {
        out.replace_range(start..end, text);
    }
    out
}

fn lsp_format(source: &str, encoding: PositionEncoding) -> String {
    let parsed = parse(source);
    let params = DocumentFormattingParams {
        text_document: uri(),
        options: Default::default(),
        work_done_progress_params: Default::default(),
    };
    match handle_formatting(&params, source, &parsed, encoding, GroupingStyle::default()) {
        Some(edits) => apply(source, &edits, encoding),
        None => source.to_string(),
    }
}

fn lsp_range_format(source: &str, range: Range, encoding: PositionEncoding) -> String {
    let parsed = parse(source);
    let params = DocumentRangeFormattingParams {
        text_document: uri(),
        range,
        options: Default::default(),
        work_done_progress_params: Default::default(),
    };
    match handle_range_formatting(&params, source, &parsed, encoding, GroupingStyle::default()) {
        Some(edits) => apply(source, &edits, encoding),
        None => source.to_string(),
    }
}

/// What the LSP must produce for a clean `source`: the CLI's output, with
/// CRLF line endings when the document has them.
fn expected(source: &str) -> String {
    let cli = try_format_source(source).expect("clean source");
    if source.contains("\r\n") {
        lf_to_crlf_outside_strings(&cli)
    } else {
        cli
    }
}

/// The range from the start of line `first` to the start of line `last + 1`
/// (or the end of the document).
fn line_range(source: &str, first: usize, last: usize, encoding: PositionEncoding) -> Range {
    let index = LineIndex::new(source, encoding);
    let line_count = source.split('\n').count();
    let end = if last + 1 < line_count {
        Position::new((last + 1) as u32, 0)
    } else {
        let (l, c) = index.offset_to_position(source.len());
        Position::new(l, c)
    };
    Range {
        start: Position::new(first as u32, 0),
        end,
    }
}

/// Every LSP formatting surface agrees with the CLI on the clean `source`.
fn check_clean(source: &str) -> Result<(), String> {
    let want = expected(source);
    for encoding in ENCODINGS {
        let whole = lsp_format(source, encoding);
        if whole != want {
            return Err(format!(
                "[{encoding:?}] textDocument/formatting disagrees with the CLI\n--- input ---\n{source:?}\n--- lsp ---\n{whole:?}\n--- cli ---\n{want:?}"
            ));
        }
        let lines = source.split('\n').count();
        let all = line_range(source, 0, lines - 1, encoding);
        let ranged = lsp_range_format(source, all, encoding);
        if ranged != want {
            return Err(format!(
                "[{encoding:?}] whole-document rangeFormatting disagrees with the CLI\n--- input ---\n{source:?}\n--- lsp ---\n{ranged:?}\n--- cli ---\n{want:?}"
            ));
        }
        // Every single line, and every pair of adjacent lines.
        for first in 0..lines {
            for last in first..(first + 2).min(lines) {
                let range = line_range(source, first, last, encoding);
                let out = lsp_range_format(source, range, encoding);
                // Range formatting may round out to whole directives (its
                // fallback does), so text outside the selected lines can
                // change; what it means cannot.
                same_meaning(
                    &format!("[{encoding:?}] rangeFormatting of lines {first}..={last}"),
                    source,
                    &out,
                )?;
                if parse(&out).errors.is_empty() {
                    if expected(&out) != want {
                        return Err(format!(
                            "[{encoding:?}] rangeFormatting of lines {first}..={last} moved away from the canonical form\n--- input ---\n{source:?}\n--- output ---\n{out:?}\n--- formatted whole ---\n{:?}\n--- cli ---\n{want:?}",
                            expected(&out)
                        ));
                    }
                } else {
                    return Err(format!(
                        "[{encoding:?}] rangeFormatting of lines {first}..={last} broke a clean file\n--- input ---\n{source:?}\n--- output ---\n{out:?}"
                    ));
                }
            }
        }
    }
    Ok(())
}

/// The parse of `out` keeps what the parse of `src` means: the same error
/// lines (each kept verbatim, none gained), the same values outside them,
/// and the same comments.
fn same_meaning(what: &str, src: &str, out: &str) -> Result<(), String> {
    let (before, after) = (parse(src), parse(out));
    let report = |detail: String| {
        Err(format!(
            "{what} changed what the file means: {detail}\n--- input ---\n{src:?}\n--- output ---\n{out:?}"
        ))
    };
    if before.errors.is_empty() != after.errors.is_empty() {
        return report(format!(
            "errors {:?} became {:?}",
            before.errors, after.errors
        ));
    }
    // Surface cleanup rewrites a line's indent (tabs to two spaces), which
    // is layout: the line still holds its error, and its text after the
    // indent is unchanged.
    let indent_free = |lines: Vec<String>| -> Vec<String> {
        lines
            .into_iter()
            .map(|l| {
                let body = l.trim_start_matches('"');
                let mut rest = body;
                loop {
                    let next = rest.trim_start_matches(' ').trim_start_matches("\\t");
                    if next.len() == rest.len() {
                        break;
                    }
                    rest = next;
                }
                let indented = rest.len() < body.len();
                format!("{}{rest}", if indented { "<indent>" } else { "" })
            })
            .collect()
    };
    let (e_before, e_after) = (
        indent_free(format_roundtrip::error_lines(src, &before)),
        indent_free(format_roundtrip::error_lines(out, &after)),
    );
    if e_before != e_after {
        return report(format!("error lines {e_before:?} became {e_after:?}"));
    }
    let skip = |s: &str, r: &rustledger_parser::ParseResult| -> Vec<usize> {
        r.errors
            .iter()
            .map(|e| s[..e.span.start.min(s.len())].matches('\n').count())
            .collect()
    };
    // Which node a comment hangs on (`comments` / `trailing_comments`) can
    // follow the indent surface cleanup rewrites on a broken file (an
    // indented comment at the end of the file); the comments themselves are
    // compared, in order, below.
    let drop_attachment = |items: Vec<String>| -> Vec<String> {
        items.into_iter().map(|s| strip_comment_lists(&s)).collect()
    };
    let (m_before, m_after) = (
        drop_attachment(format_roundtrip::meaning(src, &before, &skip(src, &before))),
        drop_attachment(format_roundtrip::meaning(out, &after, &skip(out, &after))),
    );
    if m_before != m_after {
        return report(format!("values {m_before:#?} became {m_after:#?}"));
    }
    let (c_before, c_after) = (
        format_roundtrip::comment_stream(src, &before),
        format_roundtrip::comment_stream(out, &after),
    );
    if c_before != c_after {
        return report(format!("comments {c_before:?} became {c_after:?}"));
    }
    Ok(())
}

/// The LSP's broken-file fallbacks keep what the broken `source` means.
fn check_broken(source: &str) -> Result<(), String> {
    for encoding in ENCODINGS {
        same_meaning(
            "textDocument/formatting (surface cleanup)",
            source,
            &lsp_format(source, encoding),
        )?;
        let lines = source.split('\n').count();
        for first in 0..lines {
            let range = line_range(source, first, first, encoding);
            same_meaning(
                &format!("rangeFormatting of line {first}"),
                source,
                &lsp_range_format(source, range, encoding),
            )?;
        }
    }
    Ok(())
}

fn check(source: &str) -> Result<(), String> {
    if parse(source).errors.is_empty() {
        check_clean(source)
    } else {
        check_broken(source)
    }
}

fn collect(dir: &Path, exts: &[&str], out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect(&p, exts, out);
        } else if p
            .extension()
            .and_then(|x| x.to_str())
            .is_some_and(|x| exts.contains(&x))
        {
            out.push(p);
        }
    }
}

/// The repository's ledgers (clean and broken) and the formatter fixtures.
#[test]
fn test_lsp_formatting_matches_cli_on_repository_ledgers() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    collect(&root.join("tests"), &["beancount", "bean"], &mut files);
    collect(
        &root.join("crates/rustledger-parser/tests/format_compat/cases"),
        &["bean"],
        &mut files,
    );
    files.sort();
    let mut checked = 0;
    let mut failures = Vec::new();
    for f in &files {
        let Ok(src) = fs::read_to_string(f) else {
            continue;
        };
        // The per-line range sweep is quadratic in the line count; the big
        // fixtures are covered by the whole-document checks in the parser's
        // corpus sweep.
        if src.lines().count() > 400 {
            continue;
        }
        checked += 1;
        if let Err(e) = check(&src) {
            failures.push(format!("[{}] {e}", f.display()));
        }
    }
    assert!(checked >= 200, "only {checked} ledgers checked");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// Generated ledgers: clean ones, and the same with a broken line spliced in.
fn cases() -> u32 {
    std::env::var("FORMAT_ROUNDTRIP_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(64)
}

#[test]
fn test_lsp_formatting_matches_cli_on_generated_ledgers() {
    ledger_gen::run_property(cases(), ledger_gen::ledger, |src| {
        prop_assume!(parse(&src).errors.is_empty());
        if let Err(e) = check_clean(&src) {
            prop_assert!(false, "{}", e);
        }
        Ok(())
    });
}

/// A generated ledger, a line index, and a broken line to splice in there.
fn broken_ledger() -> impl Strategy<Value = (String, prop::sample::Index, &'static str)> {
    (
        ledger_gen::ledger(),
        any::<prop::sample::Index>(),
        prop_oneof![
            Just("@@@ junk"),
            Just("2024-01-01 open Assets:A junk"),
            Just("\tstray-indent"),
            Just("  \tbad posting 1 USD USD"),
        ],
    )
}

#[test]
fn test_lsp_formatting_keeps_meaning_on_broken_ledgers() {
    ledger_gen::run_property(cases(), broken_ledger, |(src, at, junk)| {
        // Splice the junk in at a line start.
        let starts: Vec<usize> = std::iter::once(0)
            .chain(src.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        let at = starts[at.index(starts.len())];
        let src = format!("{}{junk}\n{}", &src[..at], &src[at..]);
        prop_assume!(!parse(&src).errors.is_empty());
        if let Err(e) = check_broken(&src) {
            prop_assert!(false, "{}", e);
        }
        Ok(())
    });
}

/// Surface cleanup converts a line's leading tabs and strips its trailing
/// blanks, so on a line that starts or ends inside a multi-line string it
/// rewrote the string's value.
#[test]
fn test_surface_cleanup_keeps_multi_line_strings() {
    for src in [
        "2024-01-01 * \"a\n\tb\"\n  Assets:A  1 USD\n  Assets:B\n@@@ junk\n",
        "2024-01-01 * \"a   \nb\"\n  Assets:A  1 USD\n  Assets:B\n@@@ junk\n",
        "2024-01-01 note Assets:A \"x\n\t\ty  \n  z\"\n@@@ junk\n",
    ] {
        assert!(!parse(src).errors.is_empty(), "{src:?}");
        if let Err(e) = check_broken(src) {
            panic!("{e}");
        }
    }
}

/// Range formatting kept edits by position alone. The line diff expressed
/// the reformatting of a posting (with its metadata and a comment) as an
/// insertion inside the selection and a deletion outside it; keeping only
/// the insertion duplicated the posting. The clipped edits are now kept only
/// when they converge on the canonical form, and otherwise the selected
/// directives are formatted whole.
#[test]
fn test_range_formatting_does_not_duplicate_a_posting() {
    let src = "2000-01-01 * \"\"\n  aA: \"\"  ;; \"quoted\" ; nested\n  ; 生活\n  Assets:Bank:Checking  1/5 VACHR ;ünïcode 生活\n      o0:   \"trailing spaces   \n  leading\"  ;; \"quoted\" ; nested\n ; 生活\n  Expenses:Café:Ünïcode\n      n_b-: 1.50 USD\t;\n      i_WT:\tTRUE ; note\n  Expenses:Café:Ünïcode    53.95 + 29.61 HOOL\t;\n";
    assert!(parse(src).errors.is_empty());
    if let Err(e) = check_clean(src) {
        panic!("{e}");
    }
}

/// `debug` with the contents of every `CommentList(...)` removed.
fn strip_comment_lists(debug: &str) -> String {
    const OPEN: &str = "CommentList(";
    let mut out = String::with_capacity(debug.len());
    let mut rest = debug;
    while let Some(i) = rest.find(OPEN) {
        out.push_str(&rest[..i + OPEN.len()]);
        rest = &rest[i + OPEN.len()..];
        // Skip to the matching `)`, outside string literals.
        let (mut depth, mut in_string, mut escaped) = (1usize, false, false);
        let mut end = rest.len();
        for (j, c) in rest.char_indices() {
            match c {
                _ if escaped => escaped = false,
                '\\' if in_string => escaped = true,
                '"' => in_string = !in_string,
                '(' if !in_string => depth += 1,
                ')' if !in_string => {
                    depth -= 1;
                    if depth == 0 {
                        end = j;
                        break;
                    }
                }
                _ => {}
            }
        }
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}
