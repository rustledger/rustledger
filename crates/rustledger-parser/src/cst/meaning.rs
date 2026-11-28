//! What "the formatter kept what a file means" is, for beancount: the meaning,
//! the comment stream and the error lines of one parse, as the format-neutral
//! certifier (`certify.rs`, ADR 0009) compares them item by item and the
//! round-trip oracle (`fuzz/fuzz_targets/common/format_roundtrip.rs`) compares
//! them on whole files. The oracle calls these same functions, so the product
//! and its tests cannot disagree about what "the same meaning" is
//! (Canonical-Function Discipline).
//!
//! Everything here is about one parse of one text, in that text's own byte
//! frame (BOM included, as `ParseResult` spans are).

use rustledger_core::{Decimal, Directive};

use super::certify::{CommentEvent, LineIndex, floor_boundary, lines_at};
use crate::{ParseResult, SyntaxKind};

/// Whether two directives mean the same thing.
///
/// Structural equality (`PartialEq`, which already ignores where a value sits
/// in the file) plus the three things `PartialEq` deliberately does not see
/// and the formatter must keep:
///
/// * a decimal's scale and sign (`1.5 == 1.50`, `-0 == 0` for `PartialEq`;
///   beancount's display precision and tolerance read the scale),
/// * the order metadata keys were written in (`Metadata`'s equality is
///   order-independent),
///
/// while one difference is not a change of meaning: blanks after a comment's
/// text, which the canonical form trims.
#[must_use]
pub fn same_directive(a: &Directive, b: &Directive) -> bool {
    let structurally = a == b || {
        let (mut a, mut b) = (a.clone(), b.clone());
        trim_comment_blanks(&mut a);
        trim_comment_blanks(&mut b);
        a == b
    };
    structurally && same_numbers(a, b) && same_metadata_order(a, b)
}

/// Every decimal of `a` and `b` has the same exact representation (value,
/// scale and sign), position by position.
fn same_numbers(a: &Directive, b: &Directive) -> bool {
    let mut numbers: Vec<&Decimal> = Vec::new();
    rustledger_core::visit::visit_numbers(a, &mut |n| numbers.push(n));
    let mut at = 0;
    let mut same = true;
    rustledger_core::visit::visit_numbers(b, &mut |n| {
        same &= numbers
            .get(at)
            .is_some_and(|m| m.serialize() == n.serialize());
        at += 1;
    });
    same && at == numbers.len()
}

/// Every metadata block of `a` and `b` lists its keys in the same order.
fn same_metadata_order(a: &Directive, b: &Directive) -> bool {
    let mut blocks = Vec::new();
    rustledger_core::visit::visit_metadata(a, &mut |m| blocks.push(m));
    let mut at = 0;
    let mut same = true;
    rustledger_core::visit::visit_metadata(b, &mut |m| {
        same &= blocks.get(at).is_some_and(|n| n.keys().eq(m.keys()));
        at += 1;
    });
    same && at == blocks.len()
}

/// Remove the trailing blanks of every comment attached to `d`.
fn trim_comment_blanks(d: &mut Directive) {
    fn trim(list: &mut rustledger_core::CommentList) {
        if let Some(comments) = list.as_comments_mut() {
            for c in comments {
                let kept = c.trim_end_matches([' ', '\t']).len();
                c.truncate(kept);
            }
        }
    }
    if let Directive::Transaction(t) = d {
        trim(&mut t.trailing_comments);
        for p in &mut t.postings {
            trim(&mut p.value.comments);
            trim(&mut p.value.trailing_comments);
        }
    }
}

/// One thing a parse yields that carries meaning.
#[derive(Debug, Clone, Copy)]
pub enum Meaning<'p> {
    Directive(&'p Directive),
    Option(&'p str, &'p str),
    Include(&'p str),
    Plugin(&'p str, Option<&'p str>),
}

impl Meaning<'_> {
    /// See [`same_directive`].
    pub fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Directive(a), Self::Directive(b)) => same_directive(a, b),
            (Self::Option(k, v), Self::Option(l, w)) => k == l && v == w,
            (Self::Include(a), Self::Include(b)) => a == b,
            (Self::Plugin(n, c), Self::Plugin(m, d)) => n == m && c == d,
            _ => false,
        }
    }
}

/// Everything `r` yields that carries meaning, each with the byte span (in
/// `r`'s source frame) it was read from.
pub fn meanings(r: &ParseResult) -> Vec<(std::ops::Range<usize>, Meaning<'_>)> {
    let mut out: Vec<(std::ops::Range<usize>, Meaning<'_>)> = Vec::with_capacity(
        r.directives.len() + r.options.len() + r.includes.len() + r.plugins.len(),
    );
    out.extend(
        r.directives
            .iter()
            .map(|d| (d.span.start..d.span.end, Meaning::Directive(&d.value))),
    );
    out.extend(
        r.options
            .iter()
            .map(|(k, v, s)| (s.start..s.end, Meaning::Option(k, v))),
    );
    out.extend(
        r.includes
            .iter()
            .map(|(p, s)| (s.start..s.end, Meaning::Include(p))),
    );
    out.extend(
        r.plugins
            .iter()
            .map(|(n, c, s)| (s.start..s.end, Meaning::Plugin(n, c.as_deref()))),
    );
    out
}

/// Whether two meaning lists are the same, item by item.
pub fn same_meanings(a: &[Meaning<'_>], b: &[Meaning<'_>]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.same(y))
}

const fn is_comment(kind: SyntaxKind) -> bool {
    super::convert::is_comment_kind(kind)
}

const fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::WHITESPACE | SyntaxKind::NEWLINE | SyntaxKind::BOM
    ) || is_comment(kind)
}

/// The comments of `src` (parsed as `r`), in order, interleaved with the
/// structure they sit in, each with the byte offset (in `src`'s frame) it is
/// placed at.
///
/// Structure markers are placed at a node's first non-trivia token rather
/// than where the node starts, so which node the CST hangs a comment's trivia
/// on (leading trivia of the next directive, trailing trivia of the last)
/// does not matter: only the comment's place in the source does. A comment
/// that moves from one posting to the next, from inside a string to after it,
/// or from a header to the body changes the stream.
pub fn comment_events(src: &str, r: &ParseResult) -> Vec<(usize, CommentEvent)> {
    /// The walk state: what is emitted, the markers waiting for their node's
    /// first token, and where the next token starts.
    struct Walk<'s> {
        src: &'s str,
        out: Vec<(usize, CommentEvent)>,
        pending: Vec<CommentEvent>,
        at: usize,
    }
    impl Walk<'_> {
        // Over the green tree, not the red one: the walk visits every token of
        // the file, twice per formatting run, and red nodes are allocated on
        // the way.
        fn node(&mut self, node: &rowan::GreenNodeData, top: bool) {
            for child in node.children() {
                match child {
                    rowan::NodeOrToken::Node(n) => {
                        match <crate::BeancountLanguage as rowan::Language>::kind_from_raw(n.kind())
                        {
                            SyntaxKind::ERROR_NODE => self.pending.push(CommentEvent::Marker("E")),
                            _ if top => self.pending.push(CommentEvent::Marker("D")),
                            SyntaxKind::POSTING => self.pending.push(CommentEvent::Marker("P")),
                            SyntaxKind::META_ENTRY => self.pending.push(CommentEvent::Marker("M")),
                            _ => {}
                        }
                        self.node(n, false);
                    }
                    rowan::NodeOrToken::Token(t) => {
                        let start = self.at;
                        self.at += usize::from(t.text_len());
                        let kind =
                            <crate::BeancountLanguage as rowan::Language>::kind_from_raw(t.kind());
                        if is_comment(kind) {
                            let before = &self.src[..floor_boundary(self.src, start)];
                            let line_start = before.rfind('\n').map_or(0, |i| i + 1);
                            let lead = before[line_start..].trim_start_matches('\u{FEFF}');
                            self.out.push((
                                start,
                                CommentEvent::Comment {
                                    trailing: !lead.trim().is_empty(),
                                    text: t.text().trim_end_matches([' ', '\t', '\r']).to_string(),
                                },
                            ));
                        } else if !is_trivia(kind) && !self.pending.is_empty() {
                            let pending = std::mem::take(&mut self.pending);
                            self.out.extend(pending.into_iter().map(|e| (start, e)));
                        }
                    }
                }
            }
        }
    }
    let root = r.syntax_node();
    let mut walk = Walk {
        src,
        out: Vec::new(),
        pending: Vec::new(),
        // The CST is in post-BOM coordinates.
        at: if r.has_leading_bom { 3 } else { 0 },
    };
    walk.node(root.green(), true);
    let Walk {
        mut out, pending, ..
    } = walk;
    out.extend(pending.into_iter().map(|e| (src.len(), e)));
    out
}

/// [`comment_events`] in the round-trip oracle's text form. **Internal**:
/// for `format_roundtrip.rs`, which checks whole files with the same
/// definition the certifier checks items with.
#[doc(hidden)]
#[must_use]
pub fn __comment_stream(src: &str, r: &ParseResult) -> Vec<String> {
    comment_events(src, r)
        .into_iter()
        .map(|(_, e)| e.render())
        .collect()
}

/// [`same_meanings`] over two whole parses, leaving out what touches a line
/// in `skip_a` / `skip_b` (0-based, each in its own text). **Internal**: for
/// the round-trip oracle. `Err` names the first difference.
///
/// # Errors
///
/// A description of the first entry that differs, when the two differ.
#[doc(hidden)]
pub fn __same_meaning(
    (src_a, a, skip_a): (&str, &ParseResult, &[usize]),
    (src_b, b, skip_b): (&str, &ParseResult, &[usize]),
) -> Result<(), String> {
    fn keep<'r>(src: &str, r: &'r ParseResult, skip: &[usize]) -> Vec<Meaning<'r>> {
        let lines = LineIndex::new(src);
        meanings(r)
            .into_iter()
            .filter(|(span, _)| !lines.touches(span, skip))
            .map(|(_, m)| m)
            .collect()
    }
    let (ma, mb) = (keep(src_a, a, skip_a), keep(src_b, b, skip_b));
    if same_meanings(&ma, &mb) {
        return Ok(());
    }
    let first = ma
        .iter()
        .zip(&mb)
        .position(|(x, y)| !x.same(y))
        .unwrap_or(ma.len().min(mb.len()));
    Err(format!(
        "{} vs {} items; first difference at {first}\n--- before ---\n{:?}\n--- after ---\n{:?}",
        ma.len(),
        mb.len(),
        ma.get(first),
        mb.get(first),
    ))
}

/// The text of each line of `src` holding a reported parse error of `r`, in
/// order, each once. **Internal**: for the round-trip oracle.
#[doc(hidden)]
#[must_use]
pub fn __error_lines(src: &str, r: &ParseResult) -> Vec<String> {
    lines_at(
        src,
        &LineIndex::new(src),
        r.errors.iter().map(|e| e.span.start),
    )
    .into_iter()
    .map(|l| format!("{l:?}"))
    .collect()
}

/// [`__error_lines`], the lines holding an error quieted by bison's
/// recovery window (`ParseResult::defect_spans`) included. **Internal**.
#[doc(hidden)]
#[must_use]
pub fn __defect_lines(src: &str, r: &ParseResult) -> Vec<String> {
    lines_at(
        src,
        &LineIndex::new(src),
        r.errors
            .iter()
            .map(|e| e.span.start)
            .chain(r.defect_spans.iter().map(|s| s.start)),
    )
    .into_iter()
    .map(|l| format!("{l:?}"))
    .collect()
}

/// Whether `kind` is a directive node: an item the certifier can demote.
pub fn is_directive_kind(kind: SyntaxKind) -> bool {
    <super::ast::Directive as super::ast::AstNode>::can_cast(kind)
}

/// The first and the last token of `n` that are not trivia, found by stepping
/// in from either end (over the trivia only, not the whole node).
pub fn content_span(n: &crate::SyntaxNode) -> Option<(crate::SyntaxToken, crate::SyntaxToken)> {
    let range = n.text_range();
    let inside = |t: &crate::SyntaxToken| range.contains_range(t.text_range());
    let first = std::iter::successors(n.first_token(), crate::SyntaxToken::next_token)
        .take_while(inside)
        .find(|t| !is_trivia(t.kind()))?;
    let last = std::iter::successors(n.last_token(), crate::SyntaxToken::prev_token)
        .take_while(inside)
        .find(|t| !is_trivia(t.kind()))?;
    Some((first, last))
}

#[cfg(test)]
mod tests {
    use super::super::certify::FormatReport;
    use super::super::format::{__format_source_report, EMIT_FAULT};
    use crate::format::{GroupingStyle, format_source};

    /// Format `src` with `fault` injected into the emitter.
    fn format_with(src: &str, fault: fn(&str) -> Option<String>) -> (String, FormatReport) {
        EMIT_FAULT.with(|f| f.set(Some(fault)));
        let result = __format_source_report(src, GroupingStyle::default());
        EMIT_FAULT.with(|f| f.set(None));
        result
    }

    /// The fault applied again to the output: formatting stays idempotent
    /// under the same (still broken) emitter.
    fn assert_idempotent_with(out: &str, fault: fn(&str) -> Option<String>) {
        let (again, _) = format_with(out, fault);
        assert_eq!(again, out, "not idempotent under the fault");
    }

    const TWO_TXNS: &str = "2024-01-01 *   \"a\"\n  Assets:A    1.50 USD\n  Assets:B\n\n2024-01-02 *   \"b\"\n  Assets:A    2.50 USD\n  Assets:B\n";

    #[test]
    fn test_same_directive_sees_decimal_scale() {
        let a = crate::parse("2024-01-01 price A 1.5 USD\n");
        let b = crate::parse("2024-01-01 price A 1.50 USD\n");
        assert_eq!(a.directives[0].value, b.directives[0].value);
        assert!(!super::same_directive(
            &a.directives[0].value,
            &b.directives[0].value
        ));
        assert!(super::same_directive(
            &a.directives[0].value,
            &a.directives[0].value
        ));
    }

    #[test]
    fn test_same_directive_sees_metadata_order() {
        let a = crate::parse("2024-01-01 open Assets:A\n  xa: 1\n  yb: 2\n");
        let b = crate::parse("2024-01-01 open Assets:A\n  yb: 2\n  xa: 1\n");
        assert_eq!(a.directives[0].value, b.directives[0].value);
        assert!(!super::same_directive(
            &a.directives[0].value,
            &b.directives[0].value
        ));
    }

    #[test]
    fn test_same_directive_ignores_comment_blanks() {
        let a = crate::parse("2024-01-01 * \"a\"\n  Assets:A 1 USD ; c  \n  Assets:B\n");
        let b = crate::parse("2024-01-01 * \"a\"\n  Assets:A 1 USD ; c\n  Assets:B\n");
        assert!(super::same_directive(
            &a.directives[0].value,
            &b.directives[0].value
        ));
    }

    #[test]
    fn test_certify_clean_file_has_no_demotion() {
        let (out, report) = __format_source_report(TWO_TXNS, GroupingStyle::default());
        assert!(report.is_clean(), "{report:?}");
        assert_eq!(out, format_source(TWO_TXNS));
    }

    /// An emitter that changes a number's scale changes what the item means:
    /// that item, and only it, is kept as written.
    #[test]
    fn test_certify_demotes_an_item_whose_meaning_changed() {
        fn fault(text: &str) -> Option<String> {
            text.contains("1.50").then(|| text.replace("1.50", "1.5"))
        }
        let (out, report) = format_with(TWO_TXNS, fault);
        assert_eq!(report.demoted, 1, "{report:?}");
        assert!(!report.kept_whole_file);
        assert_eq!(report.reason, Some("meaning changed"));
        assert_eq!(
            out,
            "2024-01-01 *   \"a\"\n  Assets:A    1.50 USD\n  Assets:B\n\n2024-01-02 * \"b\"\n  Assets:A  2.50 USD\n  Assets:B\n"
        );
        assert_idempotent_with(&out, fault);
    }

    /// An emitter that drops a comment is caught by the comment stream.
    #[test]
    fn test_certify_demotes_an_item_that_lost_a_comment() {
        fn fault(text: &str) -> Option<String> {
            text.contains("; keep").then(|| text.replace(" ; keep", ""))
        }
        let src = "2024-01-01 open   Assets:A ; keep\n2024-01-02 open   Assets:B\n";
        let (out, report) = format_with(src, fault);
        assert_eq!(report.demoted, 1, "{report:?}");
        assert_eq!(report.reason, Some("comments changed"));
        assert_eq!(
            out,
            "2024-01-01 open   Assets:A ; keep\n2024-01-02 open Assets:B\n"
        );
        assert_idempotent_with(&out, fault);
    }

    /// An emitter whose output it would format differently again (here, a
    /// blank line it adds after the directive every time) is not a fixed
    /// point: the item is demoted, and when its verbatim copy is rebuilt
    /// differently again (formatting the output does not know it was
    /// demoted), the file is kept as written. Either way the result is a
    /// fixed point.
    #[test]
    fn test_certify_keeps_a_file_that_does_not_reach_a_fixed_point() {
        fn fault(text: &str) -> Option<String> {
            text.contains("Assets:A").then(|| format!("{text}\n"))
        }
        let src = "2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B\n";
        let (out, report) = format_with(src, fault);
        assert_eq!(report.demoted, 1, "{report:?}");
        assert!(report.kept_whole_file, "{report:?}");
        assert_eq!(
            report.reason,
            Some("formatting the output again changed it")
        );
        assert_eq!(out, src);
        assert_idempotent_with(&out, fault);
    }

    /// An emitter whose text reads back as a different number of directives
    /// fails the boundary check.
    #[test]
    fn test_certify_demotes_an_item_that_split() {
        fn fault(text: &str) -> Option<String> {
            text.contains("Assets:A")
                .then(|| format!("{text}2024-01-01 open Assets:Z\n"))
        }
        let src = "2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B\n";
        let (out, report) = format_with(src, fault);
        assert_eq!(report.demoted, 1, "{report:?}");
        assert_eq!(report.reason, Some("an item was not read back as one node"));
        assert_eq!(
            out,
            "2024-01-01 open   Assets:A\n2024-01-02 open Assets:B\n"
        );
    }

    /// `2024-01-01 A; ` (a broken line) gained a comment when the formatter
    /// trimmed the blank after the `;` or added a newline after it; the
    /// certifier kept such files as written (phase A). A broken line is now
    /// copied byte for byte, and a last line copied as written gets no
    /// newline, so nothing is demoted.
    #[test]
    fn test_certify_broken_line_ending_in_a_semicolon_is_copied_verbatim() {
        for src in [
            "2024-01-01 A; ",
            "2024-01-01 A; \n",
            "2024-01-01 A;A ",
            "\u{feff}2024-01-01 A; ",
        ] {
            let (out, report) = __format_source_report(src, GroupingStyle::default());
            assert!(report.is_clean(), "{src:?}: {report:?}");
            assert_eq!(out, src.trim_start_matches('\u{feff}'));
            assert_eq!(format_source(&out), out, "{src:?}");
        }
    }
}
