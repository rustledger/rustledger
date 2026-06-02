//! Whole-source formatter.
//!
//! [`format_source`] reformats an entire beancount file from its source text
//! plus a [`ParseResult`], preserving comments, blank lines, and original
//! element order while aligning all amount-bearing lines against shared,
//! file-wide column widths in a single pass.
//!
//! This is the canonical entry point for tools that format complete files
//! (the `rledger format` CLI, the LSP, WASM/FFI bindings) so they all emit
//! byte-identical output. Callers that only have a list of directives and no
//! surrounding source should use [`rustledger_core::format::format_directives`].

use crate::{ParseResult, Span, Spanned};
use rustledger_core::format::{
    FormatConfig, FormatLine, escape_string, format_directive_lines, render_lines,
};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};

/// A parsed element that can be formatted, paired with its source span.
enum FormattableItem<'a> {
    Directive(&'a Spanned<Directive>),
    Option(&'a str, &'a str, Span),
    Include(&'a str, Span),
    Plugin(&'a str, Option<&'a str>, Span),
    Comment(&'a Spanned<String>),
}

impl FormattableItem<'_> {
    const fn span(&self) -> Span {
        match self {
            Self::Directive(d) => d.span,
            Self::Option(_, _, span) => *span,
            Self::Include(_, span) => *span,
            Self::Plugin(_, _, span) => *span,
            Self::Comment(c) => c.span,
        }
    }
}

/// Reformat a whole beancount file, preserving non-directive content.
///
/// `source` is the original file text and `parse_result` is the result of
/// [`crate::parse`] over that same text. The returned string is the
/// reformatted file: every directive is re-rendered and all amount-bearing
/// lines are aligned against file-wide column widths, while comments, blank
/// lines, options, includes, and plugins are preserved in their original
/// order.
///
/// The output always ends with a trailing newline (even for an empty file).
///
/// # Contract
///
/// * `parse_result` MUST come from [`crate::parse`] applied to `source`.
///   Spans are byte offsets into `source`; mismatched inputs will produce
///   wrong output. Synthesized directives (`file_id` ==
///   [`SYNTHESIZED_FILE_ID`]) appended by callers post-parse are detected
///   and skipped, but synthesized options/includes/plugins/comments
///   cannot be cleanly distinguished from real ones and will be rendered
///   as if their spans were source-derived — pass parse output only.
/// * Callers should gate this on a clean parse (`parse_result.errors`
///   empty); formatting a file with parse errors would drop the
///   unparsable content. The LSP, CLI, WASM, and FFI consumers all gate.
///
/// To format a directive list without surrounding source, use
/// `rustledger_core::format::format_directives` instead — it composes the
/// same primitives (`format_directive_lines` + `render_lines`) callers
/// can use to mix source-backed directives with synthesized ones at the
/// line level.
#[must_use]
pub fn format_source(source: &str, parse_result: &ParseResult, config: &FormatConfig) -> String {
    // Exhaustive destructure of every ParseResult field by name —
    // mirrors the guard in `shift_spans_up`. Adding a new field to
    // ParseResult breaks this pattern and forces an explicit decision
    // about whether the new field needs to be rendered (and how) or
    // is irrelevant to output (bind to `_` with a one-line comment).
    //
    // Without this exhaustiveness, a future spanned source-bearing
    // field would silently get dropped from formatter output even
    // though shift_spans_up correctly tracks it — exactly the kind of
    // visit-every-field drift the round-10 architecture refactor was
    // meant to eliminate.
    let ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        // `errors`, `warnings`, `currency_occurrences`, `has_leading_bom`
        // are not source-bearing items to be rendered: errors/warnings
        // are diagnostic state the caller already gated on (per
        // contract), currency_occurrences is just an index for LSP
        // tooling, and has_leading_bom is consulted by the BOM-restore
        // tail of this function via parse_result.has_leading_bom.
        errors: _,
        warnings: _,
        currency_occurrences: _,
        has_leading_bom: _,
    } = parse_result;

    // Collect every element into a single list, then sort by source position
    // so the output preserves the original top-to-bottom order regardless of
    // how the parser bucketed elements by kind.
    let mut items: Vec<FormattableItem<'_>> = Vec::new();

    // Skip synthesized directives — they have Span::ZERO and no source
    // backing, so they would sort to the top of the file regardless of the
    // caller's intended position. Non-directive items (options/includes/
    // plugins/comments) carry no file_id, so we can't symmetrically filter
    // them — the contract above warns callers that those are assumed to
    // come from `parse` and so always have real source spans.
    for directive in directives {
        if directive.file_id == SYNTHESIZED_FILE_ID {
            continue;
        }
        items.push(FormattableItem::Directive(directive));
    }
    for (key, value, span) in options {
        items.push(FormattableItem::Option(key, value, *span));
    }
    for (path, span) in includes {
        items.push(FormattableItem::Include(path, *span));
    }
    for (name, cfg, span) in plugins {
        items.push(FormattableItem::Plugin(name, cfg.as_deref(), *span));
    }
    for comment in comments {
        items.push(FormattableItem::Comment(comment));
    }

    items.sort_by_key(|item| item.span().start);

    // Phase 1: render every item to a flat list of FormatLines, preserving
    // blank lines as empty entries. Phase 2 (render_lines) then aligns all
    // amount-bearing lines against file-wide column widths in one pass.
    let mut lines: Vec<FormatLine> = Vec::new();
    let mut prev_end: usize = 0;

    for item in &items {
        let item_start = item.span().start;

        // Preserve blank lines between items by counting newlines in the
        // gap. One newline terminates the previous item's last line; any
        // extras are blank lines. At the start of file (prev_end == 0)
        // every leading newline is a blank line.
        if item_start > prev_end {
            let between = &source[prev_end..item_start];
            let newline_count = between.chars().filter(|&c| c == '\n').count();
            let blank_lines = if prev_end == 0 {
                newline_count
            } else {
                newline_count.saturating_sub(1)
            };
            for _ in 0..blank_lines {
                lines.push(FormatLine::Plain(String::new()));
            }
        }

        match item {
            FormattableItem::Directive(d) => {
                lines.extend(format_directive_lines(&d.value, config));

                // Preserve trailing blank lines inside the directive span.
                // Walk backwards counting '\n' (treating '\r' as part of a
                // CRLF pair) so "\r\n\r\n" yields 2. The directive's own
                // last line already terminates with one newline at render
                // time, so only the extras become blank lines.
                let original_text = &source[d.span.start..d.span.end];
                let mut trailing_newlines = 0usize;
                for c in original_text.chars().rev() {
                    match c {
                        '\n' => trailing_newlines += 1,
                        '\r' => {}
                        _ => break,
                    }
                }
                for _ in 1..trailing_newlines {
                    lines.push(FormatLine::Plain(String::new()));
                }
            }
            FormattableItem::Option(key, value, _) => {
                lines.push(FormatLine::Plain(format!(
                    "option \"{}\" \"{}\"",
                    escape_string(key),
                    escape_string(value)
                )));
            }
            FormattableItem::Include(path, _) => {
                lines.push(FormatLine::Plain(format!(
                    "include \"{}\"",
                    escape_string(path)
                )));
            }
            FormattableItem::Plugin(name, cfg, _) => {
                lines.push(FormatLine::Plain(if let Some(cfg) = cfg {
                    format!(
                        "plugin \"{}\" \"{}\"",
                        escape_string(name),
                        escape_string(cfg)
                    )
                } else {
                    format!("plugin \"{}\"", escape_string(name))
                }));
            }
            FormattableItem::Comment(c) => {
                // The lexer's `;[^\n\r]*` regex excludes the terminator, so
                // the comment span never contains '\n' — emit the value as-is.
                lines.push(FormatLine::Plain(c.value.clone()));
            }
        }

        prev_end = item.span().end;
    }

    // Preserve trailing blank lines after the last item. Non-directive items
    // (comments, options, includes, plugins) end at the last byte of their
    // content; the file's trailing newlines live in source[prev_end..]. Use
    // the same "first newline is the item's terminator, extras are blank
    // lines" rule that drives between-items gaps.
    //
    // For a blank-only file (no items at all) every newline in the source is
    // a blank line; preserve them verbatim instead of collapsing to a single
    // trailing newline.
    if prev_end < source.len() {
        let trailing = &source[prev_end..];
        let newline_count = trailing.chars().filter(|&c| c == '\n').count();
        let blank_lines = if items.is_empty() {
            newline_count
        } else {
            newline_count.saturating_sub(1)
        };
        for _ in 0..blank_lines {
            lines.push(FormatLine::Plain(String::new()));
        }
    }

    let mut formatted = render_lines(&lines, &config.alignment);

    // An empty file still needs a trailing newline; render_lines emits none
    // for an empty line list.
    if !formatted.ends_with('\n') {
        formatted.push('\n');
    }

    // Preserve the source's line-ending style. `render_lines` always
    // emits LF; if the source used CRLF (any `\r\n` is present), we
    // rewrite the output to match so a Windows-authored file
    // round-trips byte-for-byte through `rledger format`.
    //
    // Policy:
    //
    // * Any `\r\n` in source → output is CRLF-only (CRLF wins, so
    //   mixed-ending files normalize to CRLF).
    // * No `\r\n` in source → output is LF-only.
    // * Files using bare CR ONLY (no `\n`, legacy classic-Mac) round-
    //   trip as LF — `format_source` does NOT preserve bare CR. That
    //   platform is extinct in practice. If you have a real bare-CR
    //   file, run it through `dos2unix -c mac in.bean` first.
    //
    // The collapse path normalizes ALL CR bytes from the rendered
    // output before re-applying CRLF, so:
    //
    // 1. CRLFs introduced by a future renderer collapse to single LF
    //    and then re-expand to CRLF (idempotent round-trip).
    // 2. Lone bare CR bytes (a Display impl carrying an embedded `\r`
    //    inside a string literal) are stripped so the output never
    //    contains mixed `\r` + `\r\n` line endings. A bare CR mid-line
    //    is uniformly garbage — neither LF nor CRLF platforms render
    //    it usefully, and `wc -l` parity breaks with mixed endings.
    //
    // Guard the collapse on `contains('\r')` so the common case stays
    // O(N) (one pass for the final LF→CRLF replace).
    if source.contains("\r\n") {
        if formatted.contains('\r') {
            // Collapse `\r\n` first (pair-wise), THEN strip any lone
            // `\r` survivors. Doing the strip second avoids tearing
            // valid CRLF pairs into orphan LFs.
            formatted = formatted.replace("\r\n", "\n");
            if formatted.contains('\r') {
                formatted = formatted.replace('\r', "");
            }
        }
        formatted = formatted.replace('\n', "\r\n");
    }

    // Preserve a leading UTF-8 BOM. Whether the source had one is
    // recorded as a single boolean on the ParseResult by the parser
    // (see `crate::bom`'s module docstring for the architectural
    // rationale). The formatter does not inspect the source for a BOM
    // itself — that decision was already made, once, at the parser's
    // strip-at-entry boundary. Trusting the flag rather than re-
    // checking `source` is what keeps the two ends of the round-trip
    // in agreement.
    crate::bom::restore_leading(formatted, parse_result.has_leading_bom)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    fn fmt(source: &str) -> String {
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        format_source(source, &result, &FormatConfig::default())
    }

    #[test]
    fn preserves_standalone_comments() {
        let src = "; a leading comment\n2024-01-01 open Assets:Cash\n";
        let out = fmt(src);
        assert!(out.starts_with("; a leading comment\n"));
        assert!(out.contains("2024-01-01 open Assets:Cash"));
    }

    #[test]
    fn preserves_blank_lines_between_directives() {
        let src = "2024-01-01 open Assets:Cash\n\n2024-01-02 open Assets:Bank\n";
        let out = fmt(src);
        assert_eq!(
            out, "2024-01-01 open Assets:Cash\n\n2024-01-02 open Assets:Bank\n",
            "single blank line between directives should be preserved"
        );
    }

    #[test]
    fn preserves_trailing_blank_lines() {
        // Trailing blank lines inside the last directive's span survive
        // round-trip (matches bean-format and the original CLI behavior).
        let src = "2024-01-01 open Assets:Cash\n\n\n";
        let out = fmt(src);
        assert_eq!(out, "2024-01-01 open Assets:Cash\n\n\n");
    }

    /// Regression for Copilot review on PR #1244: when the last item is a
    /// standalone comment, options, include, or plugin (whose spans do not
    /// include the trailing newline), trailing blank lines after that item
    /// must still be preserved.
    #[test]
    fn preserves_trailing_blank_lines_after_comment() {
        let src = "; trailing comment\n\n\n";
        assert_eq!(fmt(src), src);
    }

    #[test]
    fn preserves_trailing_blank_lines_after_option() {
        let src = "option \"title\" \"x\"\n\n\n";
        assert_eq!(fmt(src), src);
    }

    /// CRLF-encoded source must round-trip byte-stable. `render_lines`
    /// always emits LF; `format_source` rewrites the output to match the
    /// source's line endings.
    #[test]
    fn preserves_crlf_line_endings() {
        let src = "2024-01-01 open Assets:Cash\r\n2024-01-02 open Assets:Bank\r\n";
        assert_eq!(fmt(src), src);
    }

    /// Leading UTF-8 BOM (`EF BB BF` / `\u{FEFF}`) is consumed by the
    /// lexer as whitespace, but `format_source` re-prepends it so the
    /// output round-trips byte-stable for Windows / spreadsheet exports.
    #[test]
    fn preserves_leading_bom() {
        let src = "\u{FEFF}2024-01-01 open Assets:Cash\n";
        assert_eq!(fmt(src), src);
    }

    /// BOM + CRLF combination is the common Windows export shape.
    #[test]
    fn preserves_bom_and_crlf_together() {
        let src = "\u{FEFF}2024-01-01 open Assets:Cash\r\n";
        assert_eq!(fmt(src), src);
    }

    /// Two-pass idempotence: formatting an already-formatted source
    /// must produce a byte-identical result. Covers the cross product
    /// of BOM × CRLF × LF — the cell that previously regressed across
    /// architecture iterations was the BOM + format-twice combination,
    /// where contract drift between `bom_filter` and `format_source`
    /// caused the second pass to drop the BOM.
    ///
    /// Now that the BOM decision is made once at `parse()`'s strip-at-
    /// entry boundary and recorded on `has_leading_bom`, every pass
    /// sees the same flag and agrees on the output.
    #[test]
    fn format_source_two_pass_idempotent() {
        let inputs = [
            // LF, no BOM
            "2024-01-01 open Assets:Cash\n",
            // CRLF, no BOM
            "2024-01-01 open Assets:Cash\r\n",
            // LF, with BOM
            "\u{FEFF}2024-01-01 open Assets:Cash\n",
            // CRLF, with BOM
            "\u{FEFF}2024-01-01 open Assets:Cash\r\n",
            // Multi-directive LF + BOM
            "\u{FEFF}2024-01-01 open Assets:Cash\n2024-01-02 open Assets:Bank\n",
        ];
        for src in inputs {
            let pass1 = fmt(src);
            let pass2 = fmt(&pass1);
            assert_eq!(
                pass1, pass2,
                "two-pass formatting must be idempotent for {src:?}; \
                 pass1={pass1:?}, pass2={pass2:?}"
            );
        }
    }

    /// The `has_leading_bom` flag is the single source of truth.
    /// Constructing a `ParseResult` by hand with `has_leading_bom: false`
    /// and passing it to `format_source` with a BOM-prefixed source
    /// must NOT re-prepend a BOM (the flag wins). This pins that the
    /// formatter trusts the flag rather than re-inspecting the source.
    #[test]
    fn format_source_trusts_flag_not_source_inspection() {
        let src = "\u{FEFF}2024-01-01 open Assets:Cash\n";
        let mut parsed = parse(src);
        assert!(parsed.has_leading_bom, "sanity: parse detected BOM");

        // Now flip the flag and verify the formatter respects it.
        parsed.has_leading_bom = false;
        let out = format_source(src, &parsed, &FormatConfig::default());
        assert!(
            !out.starts_with(crate::bom::BOM_CHAR),
            "formatter must respect has_leading_bom=false even when source has a BOM; \
             got {out:?}"
        );
    }

    /// Mirror of the above: a source without a BOM, but a parse result
    /// claiming there was one, produces output WITH a BOM. The flag is
    /// authoritative either direction.
    #[test]
    fn format_source_flag_authoritative_other_direction() {
        let src = "2024-01-01 open Assets:Cash\n";
        let mut parsed = parse(src);
        parsed.has_leading_bom = true;
        let out = format_source(src, &parsed, &FormatConfig::default());
        assert!(
            out.starts_with(crate::bom::BOM_CHAR),
            "formatter must respect has_leading_bom=true; got {out:?}"
        );
    }

    /// Regression: a file containing only blank lines must preserve every
    /// newline, not collapse to a single trailing newline. The old
    /// implementation gated the trailing-blanks block on `!items.is_empty()`,
    /// dropping the entire run.
    #[test]
    fn preserves_blank_only_file() {
        let src = "\n\n\n\n";
        assert_eq!(fmt(src), src);
    }

    /// Regression: directives whose `Spanned::file_id == SYNTHESIZED_FILE_ID`
    /// (no source backing, `Span::ZERO`) must be skipped — otherwise they
    /// sort to the top of the file regardless of caller intent.
    #[test]
    fn skips_synthesized_directives() {
        use rustledger_core::{Directive, NaiveDate, Open, SYNTHESIZED_FILE_ID, Spanned};
        let mut pr = parse("2024-01-01 open Assets:Real\n");
        // Append a synthesized directive after a real one. format_source
        // should ignore it; without the filter, its span.start == 0 would
        // collide with the real directive and reorder the output.
        let synth = Spanned::synthesized(Directive::Open(Open {
            date: NaiveDate::constant(2024, 6, 1),
            account: "Assets:Synth".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        }));
        assert_eq!(synth.file_id, SYNTHESIZED_FILE_ID);
        pr.directives.push(synth);
        let src = "2024-01-01 open Assets:Real\n";
        let out = format_source(src, &pr, &FormatConfig::default());
        assert!(
            !out.contains("Assets:Synth"),
            "synthesized directive should be excluded from format_source output; got {out:?}"
        );
        assert_eq!(out, src);
    }

    #[test]
    fn empty_file_gets_trailing_newline() {
        let out = fmt("");
        assert_eq!(out, "\n");
    }

    #[test]
    fn aligns_postings_file_wide() {
        // Two transactions with different account-name widths: the narrower
        // one should align to the same currency column as the wider one.
        let src = "\
2024-01-01 * \"A\"
  Assets:Cash  10.00 USD
  Expenses:Food

2024-01-02 * \"B\"
  Assets:Very:Long:Account:Name  20.00 USD
  Expenses:Stuff
";
        let out = fmt(src);
        let lines: Vec<&str> = out.lines().collect();
        let col = |needle: &str| {
            lines
                .iter()
                .find(|l| l.contains(needle))
                .and_then(|l| l.find(needle))
                .unwrap()
        };
        assert_eq!(
            col("10.00 USD"),
            col("20.00 USD"),
            "amounts in different transactions should share a currency column"
        );
    }

    #[test]
    fn preserves_options_includes_plugins_in_order() {
        let src = "\
option \"title\" \"My Ledger\"
include \"other.beancount\"
plugin \"beancount.plugins.auto\"
2024-01-01 open Assets:Cash
";
        let out = fmt(src);
        let title = out.find("option \"title\"").unwrap();
        let include = out.find("include").unwrap();
        let plugin = out.find("plugin").unwrap();
        let open = out.find("open Assets:Cash").unwrap();
        assert!(title < include && include < plugin && plugin < open);
    }
}
