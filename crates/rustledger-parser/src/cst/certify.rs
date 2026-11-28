//! What "the formatter kept what a file means" is, as one definition shared
//! by the formatter's certifier and its round-trip tests (ADR 0009).
//!
//! The formatter certifies its own output: it reparses what it wrote and
//! checks, item by item, that every item reads as it did (the same
//! directives, decimal scale included; the same comments in the same slots;
//! errors on the same lines), demoting an item that fails to a verbatim copy.
//! The checks here are the ones the round-trip oracle
//! (`fuzz/fuzz_targets/common/format_roundtrip.rs`) asserts on whole files;
//! the oracle calls these same functions, so the product and its tests cannot
//! disagree about what "the same meaning" is (Canonical-Function Discipline).
//!
//! Everything here is about one parse of one text, in that text's own byte
//! frame (BOM included, as `ParseResult` spans are).

use rustledger_core::{Decimal, Directive};

use crate::{NodeOrToken, ParseResult, SyntaxKind, WalkEvent};

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

/// Where a comment sits: the structure a comment stream interleaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommentEvent {
    /// A top-level directive starts.
    Directive,
    /// An unparsable region starts.
    Error,
    /// A posting starts.
    Posting,
    /// A metadata line starts.
    Meta,
    /// A comment, `trailing` when text precedes it on its line, its text
    /// without trailing blanks.
    Comment { trailing: bool, text: String },
}

impl CommentEvent {
    /// The oracle's text form (`D`, `E`, `P`, `M`, `C "…"`, `Ct "…"`).
    fn render(&self) -> String {
        match self {
            Self::Directive => "D".to_string(),
            Self::Error => "E".to_string(),
            Self::Posting => "P".to_string(),
            Self::Meta => "M".to_string(),
            Self::Comment { trailing, text } => {
                format!("C{} {text:?}", if *trailing { "t" } else { "" })
            }
        }
    }
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
    let root = r.syntax_node();
    // The CST is in post-BOM coordinates.
    let base = if r.has_leading_bom { 3 } else { 0 };
    let mut out = Vec::new();
    let mut pending: Vec<CommentEvent> = Vec::new();
    for event in root.preorder_with_tokens() {
        match event {
            WalkEvent::Enter(NodeOrToken::Node(n)) => {
                let top = n
                    .parent()
                    .is_some_and(|p| p.kind() == SyntaxKind::SOURCE_FILE);
                match n.kind() {
                    SyntaxKind::ERROR_NODE => pending.push(CommentEvent::Error),
                    _ if top => pending.push(CommentEvent::Directive),
                    SyntaxKind::POSTING => pending.push(CommentEvent::Posting),
                    SyntaxKind::META_ENTRY => pending.push(CommentEvent::Meta),
                    _ => {}
                }
            }
            WalkEvent::Enter(NodeOrToken::Token(t)) => {
                let kind = t.kind();
                let start = usize::from(t.text_range().start()) + base;
                if is_comment(kind) {
                    let before = &src[..floor_boundary(src, start)];
                    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
                    let lead = before[line_start..].trim_start_matches('\u{FEFF}');
                    out.push((
                        start,
                        CommentEvent::Comment {
                            trailing: !lead.trim().is_empty(),
                            text: t.text().trim_end_matches([' ', '\t', '\r']).to_string(),
                        },
                    ));
                } else if !is_trivia(kind) {
                    out.extend(std::mem::take(&mut pending).into_iter().map(|e| (start, e)));
                }
            }
            WalkEvent::Leave(_) => {}
        }
    }
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
    lines_at(src, r.errors.iter().map(|e| e.span.start))
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
        r.errors
            .iter()
            .map(|e| e.span.start)
            .chain(r.defect_spans.iter().map(|s| s.start)),
    )
    .into_iter()
    .map(|l| format!("{l:?}"))
    .collect()
}

/// The largest char boundary of `s` at or before `at` (clamped to `s`).
pub fn floor_boundary(s: &str, at: usize) -> usize {
    let at = at.min(s.len());
    (0..=at).rev().find(|&i| s.is_char_boundary(i)).unwrap_or(0)
}

/// The line starts of a text, for byte-offset → line lookups.
pub struct LineIndex {
    /// Byte offset of each line's start (after a `\n`); `starts[0] == 0`.
    starts: Vec<usize>,
}

impl LineIndex {
    pub fn new(src: &str) -> Self {
        let mut starts = vec![0];
        starts.extend(src.match_indices('\n').map(|(i, _)| i + 1));
        Self { starts }
    }

    /// The 0-based line holding byte `at` (how many `\n`s precede it).
    pub fn line(&self, at: usize) -> usize {
        self.starts.partition_point(|&s| s <= at).saturating_sub(1)
    }

    /// Whether `span` covers a line listed in `lines` (sorted or not).
    pub fn touches(&self, span: &std::ops::Range<usize>, lines: &[usize]) -> bool {
        if lines.is_empty() {
            return false;
        }
        let a = self.line(span.start);
        let b = self.line(span.end.saturating_sub(1).max(span.start));
        lines.iter().any(|l| (a..=b).contains(l))
    }
}

/// The text of the line of `src` holding byte `at`, its trailing blanks
/// removed. The file's leading BOM is not part of its first line.
pub fn line_text(src: &str, at: usize) -> &str {
    let at = floor_boundary(src, at);
    let start = src[..at].rfind('\n').map_or(0, |i| i + 1);
    let end = src[at..].find('\n').map_or(src.len(), |i| at + i);
    let line = src[start..end].trim_end_matches([' ', '\t', '\r']);
    if start == 0 {
        line.strip_prefix('\u{FEFF}').unwrap_or(line)
    } else {
        line
    }
}

/// Whether `needle` is `hay` with some items left out, order kept.
pub fn is_subsequence<T: PartialEq>(needle: &[T], hay: &[T]) -> bool {
    let mut hay = hay.iter();
    needle.iter().all(|n| hay.any(|h| h == n))
}

/// The text of each line of `src` holding one of the offsets `at` (sorted
/// ascending), in order, each once.
pub fn lines_at(src: &str, at: impl Iterator<Item = usize>) -> Vec<&str> {
    let mut starts: Vec<usize> = at
        .map(|a| {
            let a = floor_boundary(src, a);
            src[..a].rfind('\n').map_or(0, |i| i + 1)
        })
        .collect();
    starts.sort_unstable();
    starts.dedup();
    starts.into_iter().map(|s| line_text(src, s)).collect()
}

// ---- The certifier ---------------------------------------------------------
//
// What the formatter checks about its own output, item by item. An item is a
// top-level node of the source's tree (a directive or an unparsable region);
// the text between items (blank lines, file-level comments, a BOM) is the
// separator. Each check reads the source as beancount reads it and the output
// as beancount will read it, and compares what each item yields.

use super::format::{Plan, Prepared};

/// Why an output was not certified.
pub(super) struct Failure {
    /// The items (by index) that do not read back as they did; empty when
    /// no item can be blamed.
    pub(super) items: Vec<usize>,
    /// Which check failed first.
    pub(super) why: &'static str,
}

impl Failure {
    const fn whole(why: &'static str) -> Self {
        Self {
            items: Vec::new(),
            why,
        }
    }
}

/// What one region of a text yields.
#[derive(Default)]
struct Region<'p> {
    meaning: Vec<Meaning<'p>>,
    comments: Vec<CommentEvent>,
    /// Where each reported error starts.
    error_at: Vec<usize>,
    /// Where each error, reported or quieted (`defect_spans`), starts.
    defect_at: Vec<usize>,
}

/// What a text yields, split by item.
pub(super) struct Facts<'p> {
    text: &'p str,
    items: Vec<Region<'p>>,
    separator: Region<'p>,
    has_errors: bool,
    /// Items the formatter copies verbatim whatever the certifier says (an
    /// unparsable region, a directive holding an error), by item.
    opaque: Vec<bool>,
    /// Items holding a token that is not trivia, by item.
    content: Vec<bool>,
}

impl<'p> Facts<'p> {
    /// The facts of `raw`, the parse of `prep.source` as beancount reads it,
    /// split by `prep`'s items.
    pub(super) fn of_input(prep: &Prepared<'p, '_>, raw: &'p ParseResult) -> Self {
        let ranges = prep.item_ranges();
        let fold = match &prep.normalized {
            std::borrow::Cow::Borrowed(_) => None,
            std::borrow::Cow::Owned(n) => Some(fold_map(prep.source, n)),
        };
        let locate = |at: usize| {
            let at = fold.as_ref().map_or(at, |m| m[at.min(m.len() - 1)]);
            let i = ranges.partition_point(|&(_, end)| end <= at);
            ranges.get(i).filter(|&&(start, _)| start <= at).map(|_| i)
        };
        let mut facts = Self::collect(prep.source, raw, ranges.len(), locate);
        let root = prep.parsed.syntax_node();
        for (i, n) in root.children().enumerate() {
            let directive = is_directive_kind(n.kind());
            facts.opaque[i] = !directive || prep.broken.overlaps(n.text_range());
            facts.content[i] = has_content(&n);
        }
        facts
    }

    /// The facts of `parsed`, the parse of `out`, split by where `plan` says
    /// each item was written.
    fn of_output(out: &'p str, parsed: &'p ParseResult, plan: &Plan, items: usize) -> Self {
        let ranges = written_ranges(plan);
        let locate = |at: usize| locate_written(out, &ranges, at);
        Self::collect(out, parsed, items, locate)
    }

    fn collect(
        text: &'p str,
        r: &'p ParseResult,
        items: usize,
        locate: impl Fn(usize) -> Option<usize>,
    ) -> Self {
        let mut facts = Self {
            text,
            items: std::iter::repeat_with(Region::default)
                .take(items)
                .collect(),
            separator: Region::default(),
            has_errors: !r.errors.is_empty(),
            opaque: vec![false; items],
            content: vec![false; items],
        };
        // On a broken file, what touches an error line is a recovery
        // artifact: which values the parser salvages from a line it cannot
        // read depends on details the formatter normalizes. Those lines are
        // checked verbatim instead (below).
        let lines = LineIndex::new(text);
        let skip: Vec<usize> = r.errors.iter().map(|e| lines.line(e.span.start)).collect();
        for (span, m) in meanings(r) {
            if !lines.touches(&span, &skip) {
                facts.region(locate(span.start)).meaning.push(m);
            }
        }
        for (at, e) in comment_events(text, r) {
            facts.region(locate(at)).comments.push(e);
        }
        for e in &r.errors {
            let region = facts.region(locate(e.span.start));
            region.error_at.push(e.span.start);
            region.defect_at.push(e.span.start);
        }
        for s in &r.defect_spans {
            facts.region(locate(s.start)).defect_at.push(s.start);
        }
        facts
    }

    fn region(&mut self, item: Option<usize>) -> &mut Region<'p> {
        match item {
            Some(i) => &mut self.items[i],
            None => &mut self.separator,
        }
    }

    /// Whether the formatter copies item `item` verbatim whatever happens.
    pub(super) fn is_opaque(&self, item: usize) -> bool {
        self.opaque.get(item).copied().unwrap_or(true)
    }
}

/// Whether `kind` is a directive node: an item the certifier can demote.
fn is_directive_kind(kind: SyntaxKind) -> bool {
    <super::ast::Directive as super::ast::AstNode>::can_cast(kind)
}

fn has_content(n: &crate::SyntaxNode) -> bool {
    content_span(n).is_some()
}

/// The first and the last token of `n` that are not trivia, found by stepping
/// in from either end (over the trivia only, not the whole node).
fn content_span(n: &crate::SyntaxNode) -> Option<(crate::SyntaxToken, crate::SyntaxToken)> {
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

/// The non-empty written ranges of `plan`, with their items, in order.
fn written_ranges(plan: &Plan) -> Vec<(usize, usize, usize)> {
    plan.written
        .iter()
        .enumerate()
        .filter_map(|(i, w)| w.filter(|&(s, e)| s < e).map(|(s, e)| (s, e, i)))
        .collect()
}

/// The item written over byte `at` of `out`. Text a node reads as leading
/// trivia (the blank lines before an item, which the walk writes as the gap
/// before it) belongs to the item after it.
fn locate_written(out: &str, ranges: &[(usize, usize, usize)], at: usize) -> Option<usize> {
    let i = ranges.partition_point(|&(_, end, _)| end <= at);
    let &(start, _, item) = ranges.get(i)?;
    if start <= at {
        return Some(item);
    }
    out.get(at..start)
        .filter(|gap| {
            gap.bytes()
                .all(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
        })
        .map(|_| item)
}

/// For each byte offset of `source` (and its end), the offset of the same
/// text in `folded`, which is `source` with line-ending `\r`s and stray
/// `[ \t\r]` runs dropped and a space added after a lone marker (see
/// `fold_line_endings`). Only lines matter to the certifier, and the fold
/// keeps every `\n`.
fn fold_map(source: &str, folded: &str) -> Vec<usize> {
    let (s, f) = (source.as_bytes(), folded.as_bytes());
    let mut map = Vec::with_capacity(s.len() + 1);
    let (mut i, mut j) = (0, 0);
    while i < s.len() {
        if j < f.len() && s[i] == f[j] {
            map.push(j);
            i += 1;
            j += 1;
        } else if j < f.len() && f[j] == b' ' && !matches!(s[i], b'\r' | b' ' | b'\t') {
            j += 1;
        } else {
            map.push(j);
            i += 1;
        }
    }
    map.push(j);
    map
}

/// Certify `out`, the output of `prep` under `plan`: every item reads as it
/// did (the same boundaries, meaning, comments and error lines) and formatting
/// `out` again gives `out`.
pub(super) fn check(
    input: &Facts<'_>,
    plan: &Plan,
    out: &str,
    style: crate::format::GroupingStyle<'_>,
) -> Result<(), Failure> {
    let parsed = crate::parse_without_occurrences(out);
    let ranges = written_ranges(plan);
    let node_items = boundaries(input, &ranges, &parsed)?;

    let output = Facts::of_output(out, &parsed, plan, input.items.len());
    if input.has_errors != output.has_errors {
        return Err(Failure::whole(
            "a clean file became broken, or a broken one clean",
        ));
    }
    let mut why = "";
    let failed: Vec<usize> = (0..input.items.len())
        .filter(|&i| {
            let verdict = same_region(
                (input, &input.items[i]),
                (&output, &output.items[i]),
                Some(i),
                &ranges,
            );
            verdict.map_err(|w| why = w).is_err()
        })
        .collect();
    if !failed.is_empty() {
        return Err(Failure { items: failed, why });
    }
    same_region(
        (input, &input.separator),
        (&output, &output.separator),
        None,
        &ranges,
    )
    .map_err(Failure::whole)?;

    // Idempotence: formatting `out` again, with the same items kept
    // verbatim, gives `out`.
    let again = Prepared::new(out, Some(&parsed));
    let mut plan2 = Plan::default();
    if plan.forced.iter().any(|&f| f) {
        let fold = match &again.normalized {
            std::borrow::Cow::Borrowed(_) => None,
            std::borrow::Cow::Owned(n) => Some(fold_map(out, n)),
        };
        let items2 = again.item_ranges();
        for (first, item) in &node_items {
            if plan.forced(*item) {
                let at = fold
                    .as_ref()
                    .map_or(*first, |m| m[(*first).min(m.len() - 1)]);
                let i = items2.partition_point(|&(_, end)| end <= at);
                if items2.get(i).is_some_and(|&(start, _)| start <= at) {
                    plan2.force(i);
                }
            }
        }
    }
    let twice = again.emit(style, &mut plan2);
    if twice == out {
        return Ok(());
    }
    let diff = out
        .bytes()
        .zip(twice.bytes())
        .position(|(a, b)| a != b)
        .unwrap_or(out.len().min(twice.len()));
    // Blame the item the first difference falls in or right after (what an
    // item writes can change the gap after it), else the item after it (a gap
    // is written ahead of the item after it): the first of those still being
    // rebuilt, so a retry that fails at the same place moves on.
    let i = ranges.partition_point(|&(_, end, _)| end < diff);
    let candidates = ranges[i.saturating_sub(usize::from(i == ranges.len()))..]
        .iter()
        .take(2)
        .map(|&(_, _, item)| item);
    Err(Failure {
        items: candidates
            .filter(|&item| !plan.forced(item) && !input.is_opaque(item))
            .take(1)
            .collect(),
        why: "formatting the output again changed it",
    })
}

/// Check that every top-level node of `parsed` (the parse of `out`) lies in
/// one item's written range, and that every item with content was read back
/// as exactly one node. Returns, for each node, where its first token is and
/// its item.
fn boundaries(
    input: &Facts<'_>,
    ranges: &[(usize, usize, usize)],
    parsed: &ParseResult,
) -> Result<Vec<(usize, usize)>, Failure> {
    let bom = if parsed.has_leading_bom { 3 } else { 0 };
    let mut count = vec![0usize; input.items.len()];
    let mut failed = Vec::new();
    let mut nodes = Vec::new();
    for n in parsed.syntax_node().children() {
        let Some((first, last)) = content_span(&n) else {
            continue;
        };
        let (first, last) = (
            usize::from(first.text_range().start()) + bom,
            usize::from(last.text_range().end()) + bom,
        );
        let i = ranges.partition_point(|&(_, end, _)| end <= first);
        match ranges.get(i) {
            Some(&(start, end, item)) if start <= first => {
                count[item] += 1;
                nodes.push((first, item));
                if last > end {
                    failed.push(item);
                    // The node runs on into the items after it.
                    failed.extend(
                        ranges[i + 1..]
                            .iter()
                            .take_while(|&&(s, _, _)| s < last)
                            .map(|&(_, _, it)| it),
                    );
                }
            }
            // A node read from the gap between items: blame the items on
            // either side of it.
            _ => {
                let before = i.checked_sub(1).and_then(|b| ranges.get(b));
                let after = ranges.get(i);
                if before.is_none() && after.is_none() {
                    return Err(Failure::whole(
                        "a node was read from text outside every item",
                    ));
                }
                failed.extend(before.into_iter().chain(after).map(|&(_, _, it)| it));
            }
        }
    }
    for &(_, _, item) in ranges {
        if count[item] != usize::from(input.content[item]) {
            failed.push(item);
        }
    }
    if failed.is_empty() {
        Ok(nodes)
    } else {
        failed.sort_unstable();
        failed.dedup();
        Err(Failure {
            items: failed,
            why: "an item was not read back as one node",
        })
    }
}

/// Whether region `b` of the output reads as region `a` of the input did.
/// `item` is the item both regions are of (`None` for the separator).
fn same_region(
    (input, a): (&Facts<'_>, &Region<'_>),
    (output, b): (&Facts<'_>, &Region<'_>),
    item: Option<usize>,
    ranges: &[(usize, usize, usize)],
) -> Result<(), &'static str> {
    if !same_meanings(&a.meaning, &b.meaning) {
        return Err("meaning changed");
    }
    // On a broken file the structure markers come from error recovery, which
    // the formatter's normalization of a broken region may reshape; the
    // comments themselves, in order, must still all be there.
    let comments_same = if input.has_errors {
        let only = |r: &Region<'_>| {
            r.comments
                .iter()
                .filter(|e| matches!(e, CommentEvent::Comment { .. }))
                .cloned()
                .collect::<Vec<CommentEvent>>()
        };
        only(a) == only(b)
    } else {
        a.comments == b.comments
    };
    if !comments_same {
        return Err("comments changed");
    }
    if a.defect_at.is_empty() && b.defect_at.is_empty() {
        return Ok(());
    }
    // A line may hold a reported error only where the input held one,
    // reported or quieted (bison's recovery window hides an error the
    // formatter's normalization can uncover), and every line holding a
    // reported error is kept byte for byte.
    let in_errors = lines_at(input.text, a.error_at.iter().copied());
    let in_defects = lines_at(input.text, a.defect_at.iter().copied());
    let out_errors = lines_at(output.text, b.error_at.iter().copied());
    if !is_subsequence(&out_errors, &in_defects) {
        return Err("a line gained a parse error");
    }
    if in_errors.is_empty() {
        return Ok(());
    }
    let out_lines = region_lines(output.text, item, ranges);
    if is_subsequence(&in_errors, &out_lines) {
        Ok(())
    } else {
        Err("a line holding a parse error was not kept verbatim")
    }
}

/// The text of every line of `out` in `item`'s written range (for the
/// separator, every line starting outside all of them).
fn region_lines<'s>(
    out: &'s str,
    item: Option<usize>,
    ranges: &[(usize, usize, usize)],
) -> Vec<&'s str> {
    // Each line as `(start, end)`, its `\n` excluded.
    let mut lines = Vec::new();
    let mut start = 0;
    for (i, _) in out.match_indices('\n') {
        lines.push((start, i));
        start = i + 1;
    }
    if start < out.len() || start == 0 {
        lines.push((start, out.len()));
    }
    lines
        .into_iter()
        .filter(|&(s, e)| {
            if let Some(it) = item {
                // A line the item's written range overlaps.
                ranges
                    .iter()
                    .find(|&&(_, _, x)| x == it)
                    .is_some_and(|&(rs, re, _)| s < re && rs <= e)
            } else {
                // A line starting outside every written range.
                let i = ranges.partition_point(|&(_, end, _)| end <= s);
                ranges.get(i).is_none_or(|&(rs, _, _)| rs > s)
            }
        })
        .map(|(s, _)| line_text(out, s))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::format::{__format_source_report, EMIT_FAULT, FormatReport};
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
    /// blank line it adds after the directive every time) is caught by the
    /// second pass.
    #[test]
    fn test_certify_demotes_an_item_that_is_not_idempotent() {
        fn fault(text: &str) -> Option<String> {
            text.contains("Assets:A").then(|| format!("{text}\n"))
        }
        let src = "2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B\n";
        let (out, report) = format_with(src, fault);
        assert_eq!(report.demoted, 1, "{report:?}");
        assert_eq!(
            report.reason,
            Some("formatting the output again changed it")
        );
        assert_eq!(
            out,
            "2024-01-01 open   Assets:A\n2024-01-02 open Assets:B\n"
        );
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

    /// A failure that cannot be pinned on a directive the formatter could
    /// demote leaves the file as written. `2024-01-01 A; ` (a broken line,
    /// copied verbatim, with no final newline) gained a comment when the
    /// newline was added: the `;` before the trailing space read as one.
    #[test]
    fn test_certify_keeps_the_file_when_no_item_can_be_blamed() {
        for src in ["2024-01-01 A; ", "2024-01-01 A; \n"] {
            let (out, report) = __format_source_report(src, GroupingStyle::default());
            assert!(report.kept_whole_file, "{src:?}: {report:?}");
            assert_eq!(out, src);
            assert_eq!(format_source(&out), out, "{src:?}");
        }
    }

    #[test]
    fn test_fold_map_tracks_lines() {
        let map = super::fold_map("a\r\nb \r\n*\r\nc", "a\nb\n* \nc");
        // `\n`s map onto `\n`s.
        assert_eq!(map[2], 1);
        assert_eq!(map[6], 3);
        assert_eq!(map[9], 6);
        assert_eq!(map[10], 7);
        assert_eq!(map.last().copied(), Some(8));
    }
}
