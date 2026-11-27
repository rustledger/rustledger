//! rledger's deliberate parse-error differences from beancount 3.2.3, as
//! [`DeviationOverlay`]s over the beancount reference oracle.
//!
//! Each overlay is documented in `docs/reference/compatibility.md`, under
//! "Parse-Error Differences", in the section its
//! [`compatibility_section`](DeviationOverlay::compatibility_section) names.
//! None changes what rledger reports by itself: each says where the
//! reference's verdict does not apply, so that the reconciler keeps rledger's
//! behavior there.

use std::cell::Cell;

use super::lexer::Lexeme;
use crate::cst::oracle::{DeviationOverlay, LineIndex, Reference, SlotKind};
use crate::{ParseError, ParseErrorKind};

/// The UTF-8 encoding of U+FEFF.
const BOM: &[u8] = b"\xEF\xBB\xBF";

/// rledger strips a UTF-8 BOM at byte 0 and accepts the file; beancount reads
/// it as the start of an invalid token. The reference starts reading after
/// it.
pub(super) struct ByteZeroBom;

impl DeviationOverlay<Lexeme> for ByteZeroBom {
    fn name(&self) -> &'static str {
        "byte-0-bom"
    }
    fn compatibility_section(&self) -> &'static str {
        "p1-a-bom-at-the-start-of-the-file"
    }
    fn input_start(&self, src: &str) -> usize {
        if src.as_bytes().starts_with(BOM) {
            BOM.len()
        } else {
            0
        }
    }
}

/// beancount reports a syntax error whose lookahead is an end of line on the
/// line after it (bison takes the lexer's line, which has counted the `\n`);
/// rledger reports it on the line whose statement fails there (#2993).
pub(super) struct EolErrorOnFailingLine;

impl DeviationOverlay<Lexeme> for EolErrorOnFailingLine {
    fn name(&self) -> &'static str {
        "eol-error-on-failing-line"
    }
    fn compatibility_section(&self) -> &'static str {
        "p2-an-error-at-the-end-of-a-line"
    }
    fn transform_reference(&self, src: &str, reference: &mut Reference) {
        for slot in &mut reference.slots {
            if slot.kind == SlotKind::Syntax
                && src.as_bytes().get(slot.span.start) == Some(&b'\n')
                && slot.span.len() == 1
            {
                // An EOL token carries the number of the line after it.
                slot.line = slot.line.saturating_sub(1).max(1);
            }
        }
    }
}

/// A stray `\r` (one not part of a CRLF line end) is a blank to beancount's
/// lexer; rledger reports one before a token that lexes, or at a line start,
/// as an error of its own (#2980). It is claimed as rledger's own: on a line
/// beancount reports errors on, it takes the place of one of them (the
/// reconciler counts rledger's own errors against the line's slots first),
/// and it stands on a line beancount reports nothing on, but not on one
/// beancount's recovery swallows whole.
pub(super) struct StrayCarriageReturn;

impl DeviationOverlay<Lexeme> for StrayCarriageReturn {
    fn name(&self) -> &'static str {
        "stray-carriage-return"
    }
    fn compatibility_section(&self) -> &'static str {
        "p3-a-stray-carriage-return"
    }
    fn claim_own_errors(
        &self,
        src: &str,
        errors: &[ParseError],
        reference: &Reference,
        own: &mut [bool],
    ) {
        let b = src.as_bytes();
        let is_stray = |i: usize| b.get(i) == Some(&b'\r') && b.get(i + 1) != Some(&b'\n');
        // The line index, the quiet lines and the lines with slots (sorted),
        // built once on the first stray `\r`.
        let mut index: Option<(LineIndex, Vec<u32>, Vec<u32>)> = None;
        for (e, own) in errors.iter().zip(own.iter_mut()) {
            if !is_stray(e.span.start) {
                continue;
            }
            // On a line beancount's recovery swallows whole (no error of its
            // own there), the `\r` is as quiet as the rest of the line.
            let (lines, quiet, with_slots) = index.get_or_insert_with(|| {
                let lines = LineIndex::new(src);
                let quiet = reference.quiet_lines(&lines);
                let mut with_slots: Vec<u32> = reference.slots.iter().map(|s| s.line).collect();
                with_slots.sort_unstable();
                (lines, quiet, with_slots)
            });
            let line = lines.line_of(e.span.start);
            let swallowed =
                quiet.binary_search(&line).is_ok() && with_slots.binary_search(&line).is_err();
            *own = !swallowed;
        }
    }
}

/// beancount's builder reports a tag or link line after a transaction's first
/// posting on the transaction's header line; rledger reports it on the tag
/// line, where the mistake is (#2575). It is no syntax error to the
/// reference, so the diagnostic stands as rledger's own.
pub(super) struct TagsAfterFirstPosting;

impl DeviationOverlay<Lexeme> for TagsAfterFirstPosting {
    fn name(&self) -> &'static str {
        "tags-after-first-posting"
    }
    fn compatibility_section(&self) -> &'static str {
        "p4-a-tag-line-after-the-first-posting"
    }
    fn claim_own_errors(
        &self,
        _src: &str,
        errors: &[ParseError],
        _reference: &Reference,
        own: &mut [bool],
    ) {
        for (e, own) in errors.iter().zip(own.iter_mut()) {
            if let ParseErrorKind::SyntaxError(m) = &e.kind
                && m.contains("not allowed after a transaction's first posting")
            {
                *own = true;
            }
        }
    }
}

/// rledger reads a line of blanks and a `;` comment after a gap (a blank
/// line, a column-0 comment or a line beancount's lexer skips, or the top of
/// the file; other such lines between) as a comment; beancount reports
/// `unexpected INDENT` there. rledger does not report that error, but follows
/// beancount's recovery from it (`  ; c` then `  $x` is one error, on the `$x`
/// line), so the overlay drops the slot and keeps the recovery.
#[derive(Default)]
pub(super) struct IndentedCommentAfterGap {
    /// The start of the last line found to follow a gap, and the answer: the
    /// walks back over consecutive indented comments stop there, so they stay
    /// linear over a whole file.
    last: Cell<Option<(usize, bool)>>,
}

impl IndentedCommentAfterGap {
    /// Whether `line` (without its `\n`) is a gap.
    fn is_gap(line: &[u8]) -> bool {
        if line.iter().all(|&c| matches!(c, b' ' | b'\t' | b'\r')) || line.first() == Some(&b';') {
            return true;
        }
        let tag = |c: u8| c.is_ascii_alphanumeric() || matches!(c, b'-' | b'_' | b'/' | b'.');
        match line {
            [b'#', second, ..] => !tag(*second),
            [first, _, ..] => matches!(first, b'*' | b':' | b'!' | b'&' | b'?' | b'%'),
            _ => false,
        }
    }

    /// Whether the line starting at `start` is blanks then a `;` comment.
    fn is_indented_comment(b: &[u8], start: usize) -> bool {
        let rest = b.get(start..).unwrap_or_default();
        let n = rest
            .iter()
            .take_while(|&&c| matches!(c, b' ' | b'\t'))
            .count();
        n > 0 && rest.get(n) == Some(&b';')
    }

    /// Whether the line starting at `start` follows a gap, walking back over
    /// indented comment lines.
    fn after_gap(&self, b: &[u8], start: usize) -> bool {
        let mut at = start;
        let answer = loop {
            if at == 0 {
                break true;
            }
            if let Some((line, gap)) = self.last.get()
                && line == at
                && at != start
            {
                break gap;
            }
            let prev_end = at - 1;
            let prev_start = b[..prev_end]
                .iter()
                .rposition(|&c| c == b'\n')
                .map_or(0, |i| i + 1);
            if !Self::is_indented_comment(b, prev_start) {
                break Self::is_gap(&b[prev_start..prev_end]);
            }
            at = prev_start;
        };
        self.last.set(Some((start, answer)));
        answer
    }
}

impl DeviationOverlay<Lexeme> for IndentedCommentAfterGap {
    fn name(&self) -> &'static str {
        "indented-comment-after-gap"
    }
    fn compatibility_section(&self) -> &'static str {
        "p5-an-indented-comment-after-a-gap"
    }
    fn transform_reference(&self, src: &str, reference: &mut Reference) {
        let b = src.as_bytes();
        reference.slots.retain(|s| {
            let at_line_start = s.span.start == 0 || b.get(s.span.start - 1) == Some(&b'\n');
            !(s.kind == SlotKind::Syntax
                && at_line_start
                && s.span.start < s.span.end
                && Self::is_indented_comment(b, s.span.start)
                && self.after_gap(b, s.span.start))
        });
    }
}

/// On an indented line no entry continues (an orphan, after a gap), beancount
/// reports its indent and then each invalid token; where the line's first
/// token is an invalid one holding a BOM, rledger's BOM diagnostic stands for
/// both (it names the BOM), so such a line keeps rledger's own errors. After a
/// directive that takes no indented lines (`option`, `pushtag`), rledger
/// reports both, as beancount does, and the line is not claimed.
pub(super) struct BomOrphanLine;

impl BomOrphanLine {
    /// The 1-based lines of `reference` (over `src`, which the reference read
    /// whole) where an orphan line's indent error is followed right away by
    /// an invalid token holding a BOM.
    fn lines(src: &str, reference: &Reference) -> Vec<u32> {
        let b = src.as_bytes();
        let holds_bom = |r: &std::ops::Range<usize>| {
            b.get(r.clone())
                .is_some_and(|t| t.windows(BOM.len()).any(|w| w == BOM))
        };
        let gaps = IndentedCommentAfterGap::default();
        let mut out = Vec::new();
        for (i, s) in reference.slots.iter().enumerate() {
            let at_indent = s.kind == SlotKind::Syntax
                && s.span.start < s.span.end
                && (s.span.start == 0 || b.get(s.span.start - 1) == Some(&b'\n'))
                && matches!(b.get(s.span.start), Some(b' ' | b'\t'));
            if at_indent
                && let Some(next) = reference.slots.get(i + 1)
                && next.line == s.line
                && next.kind == SlotKind::Lexical
                && next.span.start == s.span.end
                && holds_bom(&next.span)
                && gaps.after_gap(b, s.span.start)
            {
                out.push(s.line);
            }
        }
        out
    }
}

impl DeviationOverlay<Lexeme> for BomOrphanLine {
    fn name(&self) -> &'static str {
        "bom-orphan-line"
    }
    fn compatibility_section(&self) -> &'static str {
        "p6-a-bom-on-an-orphan-indented-line"
    }
    fn claim_own_lines(
        &self,
        src: &str,
        _errors: &[ParseError],
        reference: &Reference,
        lines: &mut Vec<u32>,
    ) {
        // The claim hooks see the source rledger parsed: read past a byte-0
        // BOM as the reference did, with the reference's offsets moved back
        // into that frame.
        let start = ByteZeroBom.input_start(src);
        let mut moved = reference.clone();
        if start > 0 {
            for s in &mut moved.slots {
                s.span = s.span.start - start..s.span.end - start;
            }
        }
        lines.extend(Self::lines(&src[start..], &moved));
    }
}

/// beancount drops an entry whose next column-0 line starts with an invalid
/// token (its parser still waits for the entry's indented lines there), and
/// with it the builder's errors; rledger keeps the entry and those errors.
/// In the reduction trace, such an entry counts as built.
pub(super) struct KeptEntries;

impl DeviationOverlay<Lexeme> for KeptEntries {
    fn name(&self) -> &'static str {
        "kept-entries"
    }
    fn compatibility_section(&self) -> &'static str {
        "p7-an-entry-before-an-unreadable-line"
    }
    fn transform_reference(&self, src: &str, reference: &mut Reference) {
        let b = src.as_bytes();
        for s in &mut reference.statements {
            let at = s.end;
            let at_column_0 = at > 0
                && b.get(at - 1) == Some(&b'\n')
                && b.get(at).is_some_and(|c| !matches!(c, b' ' | b'\t'));
            if !s.built && at_column_0 {
                s.built = true;
            }
        }
    }
}

/// rledger supports cost merging (`{*}`), which beancount's builder refuses
/// ("Cost merging is not supported yet"). That is no syntax error to the
/// reference either (its grammar takes `*` in a cost), so this overlay has no
/// hook: it keeps the list of deviations complete, and its test pins that the
/// reference reports nothing there.
pub(super) struct CostMerge;

impl DeviationOverlay<Lexeme> for CostMerge {
    fn name(&self) -> &'static str {
        "cost-merge"
    }
    fn compatibility_section(&self) -> &'static str {
        "p8-cost-merging"
    }
}

/// An arithmetic expression that cannot be evaluated (a division by zero,
/// an overflow) is rledger's own error, reported where it is. beancount
/// crashes or garbles its token stream there (a division by zero replaces the
/// next token with a lexer error), a bug rledger does not copy (Python
/// compatibility policy: fixable). rledger words a malformed expression the
/// same way; that one is a syntax error to the reference too, so only an
/// expression on a line the reference reads without a syntax error is
/// claimed.
pub(super) struct DivideByZero;

impl DeviationOverlay<Lexeme> for DivideByZero {
    fn name(&self) -> &'static str {
        "divide-by-zero"
    }
    fn compatibility_section(&self) -> &'static str {
        "p9-an-expression-that-cannot-be-evaluated"
    }
    fn claim_own_errors(
        &self,
        src: &str,
        errors: &[ParseError],
        reference: &Reference,
        own: &mut [bool],
    ) {
        // The line index, the quiet lines and the lines with syntax slots
        // (sorted), built once on the first such error.
        let mut index: Option<(LineIndex, Vec<u32>, Vec<u32>)> = None;
        for (e, own) in errors.iter().zip(own.iter_mut()) {
            if let ParseErrorKind::SyntaxError(m) = &e.kind
                && m.starts_with("invalid arithmetic expression")
            {
                let (lines, quiet, syntax) = index.get_or_insert_with(|| {
                    let lines = LineIndex::new(src);
                    let quiet = reference.quiet_lines(&lines);
                    let mut syntax: Vec<u32> = reference
                        .slots
                        .iter()
                        .filter(|s| s.kind == SlotKind::Syntax)
                        .map(|s| s.line)
                        .collect();
                    syntax.sort_unstable();
                    (lines, quiet, syntax)
                });
                let line = lines.line_of(e.span.start);
                // Not in beancount's recovery either: it evaluates nothing
                // there.
                *own = quiet.binary_search(&line).is_err() && syntax.binary_search(&line).is_err();
            }
        }
    }
}

/// A number beyond the ~28 significant digits rledger's decimal type holds is
/// rledger's own error (beancount's decimals are arbitrary precision).
pub(super) struct DecimalPrecision;

impl DeviationOverlay<Lexeme> for DecimalPrecision {
    fn name(&self) -> &'static str {
        "decimal-precision"
    }
    fn compatibility_section(&self) -> &'static str {
        "p10-numbers-beyond-28-digits"
    }
    fn claim_own_errors(
        &self,
        _src: &str,
        errors: &[ParseError],
        _reference: &Reference,
        own: &mut [bool],
    ) {
        for (e, own) in errors.iter().zip(own.iter_mut()) {
            if let ParseErrorKind::SyntaxError(m) = &e.kind
                && m.starts_with("invalid number in amount (likely exceeds")
            {
                *own = true;
            }
        }
    }
}

/// Every overlay, constructed for one parse (some keep per-parse state).
#[derive(Default)]
pub(super) struct Overlays {
    indented_comment: IndentedCommentAfterGap,
}

impl Overlays {
    pub(super) fn new() -> Self {
        Self::default()
    }

    /// In the order they apply.
    pub(super) fn all(&self) -> Vec<&dyn DeviationOverlay<Lexeme>> {
        vec![
            &ByteZeroBom,
            &EolErrorOnFailingLine,
            &StrayCarriageReturn,
            &TagsAfterFirstPosting,
            &self.indented_comment,
            &BomOrphanLine,
            &KeptEntries,
            &CostMerge,
            &DivideByZero,
            &DecimalPrecision,
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::super::reference;
    use super::*;

    const COMPATIBILITY_MD: &str =
        include_str!("../../../../../../docs/reference/compatibility.md");

    /// The GitHub anchor of a markdown heading.
    fn anchor(heading: &str) -> String {
        heading
            .trim()
            .to_lowercase()
            .chars()
            .filter_map(|c| match c {
                ' ' => Some('-'),
                c if c.is_alphanumeric() || c == '-' || c == '_' => Some(c),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn test_overlays_cite_existing_compatibility_sections() {
        let anchors: Vec<String> = COMPATIBILITY_MD
            .lines()
            .filter_map(|l| l.strip_prefix("### "))
            .map(anchor)
            .collect();
        let set = Overlays::new();
        let mut names = Vec::new();
        for o in set.all() {
            assert!(
                anchors.iter().any(|a| a == o.compatibility_section()),
                "overlay `{}` cites `#{}`, which is no section of docs/reference/compatibility.md",
                o.name(),
                o.compatibility_section()
            );
            assert!(
                !names.contains(&o.name()),
                "duplicate overlay name {}",
                o.name()
            );
            names.push(o.name());
        }
    }

    fn slot_lines(src: &str) -> Vec<u32> {
        reference(src, false).slots.iter().map(|s| s.line).collect()
    }

    #[test]
    fn test_byte_zero_bom_is_not_read() {
        assert_eq!(
            slot_lines("\u{feff}2024-01-01 open Assets:A\n"),
            [] as [u32; 0]
        );
        assert_eq!(slot_lines("x\u{feff}\n"), [1]);
    }

    #[test]
    fn test_eol_error_moves_to_the_failing_line() {
        assert_eq!(slot_lines("\noption \"a\"\n"), [2]);
        // At the end of the input the error is on the statement's line.
        assert_eq!(slot_lines("\noption \"a\""), [2]);
    }

    #[test]
    fn test_indented_comment_after_a_gap_is_a_comment() {
        // After a byte-0 BOM, the first line starts after it.
        assert_eq!(slot_lines("\u{feff} ;c\n  kk: \"v\"\n"), [] as [u32; 0]);
        assert_eq!(slot_lines("; c\n  ; d\n  ; e\n\n  ; f\n"), [] as [u32; 0]);
        // Beancount's recovery from the indent it reports goes on.
        assert_eq!(slot_lines("  ; c\n  $x\n"), [2]);
        assert_eq!(slot_lines("  ; c\n\n\n  $x\n"), [4, 4]);
        assert_eq!(slot_lines("  ; top\n"), [] as [u32; 0]);
        // After a directive that takes no metadata, both report it.
        assert_eq!(slot_lines("option \"a\" \"b\"\n  ; c\n"), [2]);
    }

    #[test]
    fn test_bom_orphan_line_keeps_rledgers_errors() {
        let lines = |src: &str| BomOrphanLine::lines(src, &reference(src, false));
        assert_eq!(lines("  \u{feff}x\n"), [1]);
        assert_eq!(lines("; c\n  \u{feff}x\n"), [2]);
        assert_eq!(lines("  $x\n"), [] as [u32; 0]);
        assert_eq!(lines("  $x \u{feff}y\n"), [] as [u32; 0]);
        assert_eq!(
            lines("pushtag #a\n  \u{feff}x\npoptag #a\n"),
            [] as [u32; 0]
        );
        // The reference keeps both of beancount's errors there.
        assert_eq!(slot_lines("  \u{feff}x\n"), [1, 1]);
    }

    #[test]
    fn test_cost_merge_is_no_syntax_error() {
        assert_eq!(
            slot_lines("2024-01-01 * \"x\"\n  Assets:A -1 ABC {*}\n  Assets:B\n"),
            [] as [u32; 0]
        );
    }

    #[test]
    fn test_kept_entries_count_as_built() {
        let src = "2024-01-01 open Assets:A \"FIFO\"\n$\n";
        let r = reference(src, false);
        assert!(r.statements.iter().all(|s| s.built), "{:?}", r.statements);
        // A statement dropped inside its own line stays dropped.
        let r = reference("2024-01-01 open Assets:A $\n", false);
        assert!(r.statements.iter().any(|s| !s.built));
    }
}
