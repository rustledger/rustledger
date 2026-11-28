//! The formatter's driver and certifier (ADR 0009), format-neutral.
//!
//! A [`Frontend`] reads a text of its grammar and supplies three things: the
//! items the text splits into (*segment*), the formatted text with where each
//! item went (*emit*), and what each part of a text yields (*meaning*: values
//! with the span they were read from, the comment stream, the error lines).
//! The driver and the certifier here know nothing else about the grammar:
//! beancount is one frontend (`format.rs`, `meaning.rs`), and another grammar
//! (ledger, hledger) is another implementation of the trait.
//!
//! The driver emits, then certifies the output item by item: the output must
//! hold one node per item, each item must yield what it did (the same values,
//! the same comments in the same slots, errors on the same lines), and an
//! item that fails is demoted to a verbatim copy until the output passes.
//! The certified output is returned only if certifying it again gives it
//! again, so formatting is idempotent by construction. When a failure cannot
//! be pinned on an item that can still be demoted, the input is returned
//! unchanged, which keeps every promise trivially.

use std::ops::Range;

/// One grammar, as the driver and the certifier see it.
pub trait Frontend {
    /// One text as the frontend reads it (its parse, and what the frontend
    /// needs to emit it).
    type Reading<'s>
    where
        Self: 's;
    /// One value a text yields, borrowed from its reading.
    type Meaning<'r>;

    /// Read `text`.
    fn read<'s>(&'s self, text: &'s str) -> Self::Reading<'s>;

    /// The text a reading was read from.
    fn text<'r>(&self, reading: &'r Self::Reading<'_>) -> &'r str;

    /// *Segment*: the top-level items, in order, without overlap.
    fn items(&self, reading: &Self::Reading<'_>) -> Vec<Item>;

    /// *Emit*: the formatted text, copying `plan`'s forced items verbatim and
    /// recording where each item went (`Plan::record`).
    fn emit(&self, reading: &Self::Reading<'_>, plan: &mut Plan) -> String;

    /// Where the content (the first to the last token that is not trivia) of
    /// each top-level node of the reading starts and ends, in order.
    fn node_contents(&self, reading: &Self::Reading<'_>) -> Vec<(usize, usize)>;

    /// *Meaning*: every value the reading yields, with the span it was read
    /// from.
    fn meanings<'r>(
        &self,
        reading: &'r Self::Reading<'_>,
    ) -> Vec<(Range<usize>, Self::Meaning<'r>)>;

    /// Whether two values are the same.
    fn same(a: &Self::Meaning<'_>, b: &Self::Meaning<'_>) -> bool;

    /// The comment stream: each comment, interleaved with the structure it
    /// sits in, at the offset it is placed at.
    fn comments(&self, reading: &Self::Reading<'_>) -> Vec<(usize, CommentEvent)>;

    /// Where each reported parse error starts.
    fn errors(&self, reading: &Self::Reading<'_>) -> Vec<usize>;

    /// Where each error the grammar quiets (a recovery window) starts:
    /// unread text, though no error is reported there.
    fn defects(&self, reading: &Self::Reading<'_>) -> Vec<usize>;
}

/// One top-level item of a text.
#[derive(Debug, Clone, Copy)]
pub struct Item {
    /// Its byte range in the text.
    pub range: (usize, usize),
    /// Copied verbatim whatever the certifier says (it holds an error, or
    /// lies outside the range being formatted).
    pub opaque: bool,
    /// It holds a token that is not trivia.
    pub content: bool,
}

/// Where a comment sits: the structure a comment stream interleaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommentEvent {
    /// A structure starts (the frontend names it: a directive, a posting).
    Marker(&'static str),
    /// A comment, `trailing` when text precedes it on its line, its text
    /// without trailing blanks.
    Comment { trailing: bool, text: String },
}

impl CommentEvent {
    /// The round-trip oracle's text form (the marker, `C "…"`, `Ct "…"`).
    pub fn render(&self) -> String {
        match self {
            Self::Marker(m) => (*m).to_string(),
            Self::Comment { trailing, text } => {
                format!("C{} {text:?}", if *trailing { "t" } else { "" })
            }
        }
    }
}

/// Which items the emitter copies verbatim, and where it wrote each, by item
/// index.
#[derive(Default)]
pub struct Plan {
    /// Items the certifier demoted to a verbatim copy.
    forced: Vec<bool>,
    /// The output byte range each item was written to.
    pub written: Vec<Option<(usize, usize)>>,
}

impl Plan {
    pub fn forced(&self, item: usize) -> bool {
        self.forced.get(item).copied().unwrap_or(false)
    }

    fn force(&mut self, item: usize) {
        if self.forced.len() <= item {
            self.forced.resize(item + 1, false);
        }
        self.forced[item] = true;
    }

    /// Record where item `item` was written.
    pub fn record(&mut self, item: usize, written: Option<(usize, usize)>) {
        if self.written.len() <= item {
            self.written.resize(item + 1, None);
        }
        self.written[item] = written;
    }
}

/// How formatting one text went: what the certifier had to keep as written.
/// **Internal**: observed by the round-trip tests and the fuzz target, which
/// require zero demotions (so an emitter bug still fails them, though users
/// never see it).
#[doc(hidden)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FormatReport {
    /// Items the certifier demoted to a verbatim copy because their
    /// formatted form did not read back as they did.
    pub demoted: usize,
    /// Whether the certifier gave up on the text and returned it unchanged
    /// (a failure it could not pin on one item).
    pub kept_whole_file: bool,
    /// The first check an output failed, if any did.
    pub reason: Option<&'static str>,
}

impl FormatReport {
    /// Whether the certifier changed anything about the formatted output.
    #[must_use]
    pub const fn is_clean(&self) -> bool {
        self.demoted == 0 && !self.kept_whole_file
    }
}

/// Format `input` and certify the result (see the module docs).
pub fn format_certified<F: Frontend>(
    frontend: &F,
    input: &F::Reading<'_>,
) -> (String, FormatReport) {
    let source = frontend.text(input);
    let mut report = FormatReport::default();
    let mut plan = Plan::default();
    let mut facts = None;
    loop {
        let step = certify_items(
            frontend,
            input,
            &mut facts,
            &mut plan,
            &mut report,
            |out, reading| {
                // The fixed point: certifying `out` again gives `out`.
                match certify_items(
                    frontend,
                    reading,
                    &mut None,
                    &mut Plan::default(),
                    &mut FormatReport::default(),
                    |twice, _| twice.to_string(),
                ) {
                    Some(Certified::Output(_, twice)) => twice,
                    Some(Certified::Source) | None => out.to_string(),
                }
            },
        );
        let (out, twice) = match step {
            None => {
                report.kept_whole_file = true;
                return (source.to_string(), report);
            }
            // Already formatted: formatting it again certifies it again to
            // itself (this very computation, on the same input).
            Some(Certified::Source) => return (source.to_string(), report),
            Some(Certified::Output(out, twice)) => (out, twice),
        };
        if twice == out {
            return (out, report);
        }
        report
            .reason
            .get_or_insert("formatting the output again changed it");
        // Blame the item written over the first difference, or the one after
        // it (a gap is written ahead of the item after it). An item already
        // kept as written that its own output rebuilds differently cannot be
        // demoted further: keep the text.
        let diff = out
            .bytes()
            .zip(twice.bytes())
            .position(|(a, b)| a != b)
            .unwrap_or(out.len().min(twice.len()));
        let blamed = plan
            .written
            .iter()
            .enumerate()
            .filter_map(|(i, w)| w.map(|(_, end)| (i, end)))
            .find(|&(_, end)| end >= diff)
            .map(|(i, _)| i)
            .filter(|&i| !plan.forced(i) && facts.as_ref().is_some_and(|f| !f.is_opaque(i)));
        let Some(item) = blamed else {
            report.kept_whole_file = true;
            return (source.to_string(), report);
        };
        plan.force(item);
        report.demoted += 1;
    }
}

/// The result of certifying one input.
enum Certified<X> {
    /// The formatted text is the input itself.
    Source,
    /// A formatted text, and what `then` made of it.
    Output(String, X),
}

/// Emit `input` under `plan` and certify the output item by item, demoting
/// what fails, until an output passes. On success, `then` is given the output
/// and its reading. `None` when a failure cannot be pinned on an item that
/// can still be demoted.
///
/// `facts` caches the facts of the input across calls.
fn certify_items<'r, F: Frontend, X>(
    frontend: &F,
    input: &'r F::Reading<'_>,
    facts: &mut Option<Facts<'r, F>>,
    plan: &mut Plan,
    report: &mut FormatReport,
    then: impl FnOnce(&str, &F::Reading<'_>) -> X,
) -> Option<Certified<X>> {
    loop {
        let out = frontend.emit(input, plan);
        if out == frontend.text(input) {
            return Some(Certified::Source);
        }
        let facts =
            facts.get_or_insert_with(|| Facts::of_input(frontend, input, &frontend.items(input)));
        let reading = frontend.read(&out);
        let failure = match check(frontend, facts, plan, &reading) {
            Ok(()) => {
                let made = then(&out, &reading);
                drop(reading);
                return Some(Certified::Output(out, made));
            }
            Err(failure) => failure,
        };
        report.reason.get_or_insert(failure.why);
        let mut grew = false;
        for item in failure.items {
            if !facts.is_opaque(item) && !plan.forced(item) {
                plan.force(item);
                report.demoted += 1;
                grew = true;
            }
        }
        if !grew {
            return None;
        }
    }
}

/// Why an output was not certified.
struct Failure {
    /// The items (by index) that do not read back as they did; empty when
    /// no item can be blamed.
    items: Vec<usize>,
    /// Which check failed first.
    why: &'static str,
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
struct Region<'r, F: Frontend + ?Sized> {
    meaning: Vec<F::Meaning<'r>>,
    comments: Vec<CommentEvent>,
    /// Where each reported error starts.
    error_at: Vec<usize>,
    /// Where each error, reported or quieted, starts.
    defect_at: Vec<usize>,
}

impl<F: Frontend + ?Sized> Default for Region<'_, F> {
    fn default() -> Self {
        Self {
            meaning: Vec::new(),
            comments: Vec::new(),
            error_at: Vec::new(),
            defect_at: Vec::new(),
        }
    }
}

/// What a text yields, split by item.
struct Facts<'r, F: Frontend + ?Sized> {
    text: &'r str,
    lines: LineIndex,
    items: Vec<Region<'r, F>>,
    separator: Region<'r, F>,
    has_errors: bool,
    /// Items the formatter copies verbatim whatever the certifier says.
    opaque: Vec<bool>,
    /// Items holding a token that is not trivia.
    content: Vec<bool>,
}

impl<'r, F: Frontend> Facts<'r, F> {
    /// The facts of the input, split by its items.
    fn of_input(frontend: &F, input: &'r F::Reading<'_>, items: &[Item]) -> Self {
        let locate = |at: usize| {
            let i = items.partition_point(|it| it.range.1 <= at);
            items.get(i).filter(|it| it.range.0 <= at).map(|_| i)
        };
        let mut facts = Self::collect(frontend, input, items.len(), locate);
        for (i, item) in items.iter().enumerate() {
            facts.opaque[i] = item.opaque;
            facts.content[i] = item.content;
        }
        facts
    }

    /// The facts of an output, split by where `plan` says each item was
    /// written.
    fn of_output(frontend: &F, output: &'r F::Reading<'_>, plan: &Plan, items: usize) -> Self {
        let ranges = written_ranges(plan);
        let out = frontend.text(output);
        let locate = |at: usize| locate_written(out, &ranges, at);
        Self::collect(frontend, output, items, locate)
    }

    fn collect(
        frontend: &F,
        reading: &'r F::Reading<'_>,
        items: usize,
        locate: impl Fn(usize) -> Option<usize>,
    ) -> Self {
        let text = frontend.text(reading);
        let lines = LineIndex::new(text);
        let errors = frontend.errors(reading);
        let mut facts = Self {
            text,
            lines: lines.clone(),
            items: std::iter::repeat_with(Region::default)
                .take(items)
                .collect(),
            separator: Region::default(),
            has_errors: !errors.is_empty(),
            opaque: vec![false; items],
            content: vec![false; items],
        };
        // On a broken text, what touches an error line is a recovery
        // artifact: which values the parser salvages from a line it cannot
        // read depends on details the formatter normalizes. Those lines are
        // checked verbatim instead (below).
        let skip: Vec<usize> = errors.iter().map(|&at| lines.line(at)).collect();
        for (span, m) in frontend.meanings(reading) {
            if !lines.touches(&span, &skip) {
                facts.region(locate(span.start)).meaning.push(m);
            }
        }
        for (at, e) in frontend.comments(reading) {
            facts.region(locate(at)).comments.push(e);
        }
        // An error at the end of the text (`unexpected end of file`) is on the
        // last line holding text: the final newline the formatter adds must
        // not move it onto an empty line of its own, or out of its item.
        let at_text = |at: usize| {
            if at >= text.len() {
                text.len().saturating_sub(1)
            } else {
                at
            }
        };
        for at in errors {
            let at = at_text(at);
            let region = facts.region(locate(at));
            region.error_at.push(at);
            region.defect_at.push(at);
        }
        for at in frontend.defects(reading) {
            let at = at_text(at);
            facts.region(locate(at)).defect_at.push(at);
        }
        facts
    }

    fn region(&mut self, item: Option<usize>) -> &mut Region<'r, F> {
        match item {
            Some(i) => &mut self.items[i],
            None => &mut self.separator,
        }
    }

    /// Whether the formatter copies item `item` verbatim whatever happens.
    fn is_opaque(&self, item: usize) -> bool {
        self.opaque.get(item).copied().unwrap_or(true)
    }
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

/// Certify `output`, the reading of the emitter's output under `plan`: every
/// item reads as it did (the same boundaries, meaning, comments and error
/// lines).
fn check<F: Frontend>(
    frontend: &F,
    input: &Facts<'_, F>,
    plan: &Plan,
    output: &F::Reading<'_>,
) -> Result<(), Failure> {
    let ranges = written_ranges(plan);
    boundaries(frontend, input, &ranges, output)?;
    let output = Facts::of_output(frontend, output, plan, input.items.len());
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
    .map_err(Failure::whole)
}

/// Check that every top-level node of the output lies in one item's written
/// range, and that every item with content was read back as exactly one node.
fn boundaries<F: Frontend>(
    frontend: &F,
    input: &Facts<'_, F>,
    ranges: &[(usize, usize, usize)],
    output: &F::Reading<'_>,
) -> Result<(), Failure> {
    let mut count = vec![0usize; input.items.len()];
    let mut failed = Vec::new();
    for (first, last) in frontend.node_contents(output) {
        let i = ranges.partition_point(|&(_, end, _)| end <= first);
        match ranges.get(i) {
            Some(&(start, end, item)) if start <= first => {
                count[item] += 1;
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
        Ok(())
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
fn same_region<F: Frontend>(
    (input, a): (&Facts<'_, F>, &Region<'_, F>),
    (output, b): (&Facts<'_, F>, &Region<'_, F>),
    item: Option<usize>,
    ranges: &[(usize, usize, usize)],
) -> Result<(), &'static str> {
    if a.meaning.len() != b.meaning.len()
        || !a.meaning.iter().zip(&b.meaning).all(|(x, y)| F::same(x, y))
    {
        return Err("meaning changed");
    }
    // On a broken text the structure markers come from error recovery, which
    // the formatter's normalization of a broken region may reshape; the
    // comments themselves, in order, must still all be there.
    let comments_same = if input.has_errors {
        let only = |r: &Region<'_, F>| {
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
    // reported or quieted (a recovery window hides an error the formatter's
    // normalization can uncover), and every line holding a reported error is
    // kept byte for byte.
    let in_errors = lines_at(input.text, &input.lines, a.error_at.iter().copied());
    let in_defects = lines_at(input.text, &input.lines, a.defect_at.iter().copied());
    let out_errors = lines_at(output.text, &output.lines, b.error_at.iter().copied());
    if !is_subsequence(&out_errors, &in_defects) {
        return Err("a line gained a parse error");
    }
    if in_errors.is_empty() {
        return Ok(());
    }
    let out_lines = region_lines(output, item, ranges);
    if is_subsequence(&in_errors, &out_lines) {
        Ok(())
    } else {
        Err("a line holding a parse error was not kept verbatim")
    }
}

/// The text of every line of the output in `item`'s written range (for the
/// separator, every line starting outside all of them).
fn region_lines<'s, F: Frontend>(
    output: &Facts<'s, F>,
    item: Option<usize>,
    ranges: &[(usize, usize, usize)],
) -> Vec<&'s str> {
    let (out, lines) = (output.text, &output.lines);
    let text = |l: usize| line_text(out, lines.start(l));
    if let Some(it) = item {
        // The lines the item's written range overlaps.
        let Some(&(rs, re, _)) = ranges
            .get(ranges.partition_point(|&(_, _, x)| x < it))
            .filter(|&&(_, _, x)| x == it)
        else {
            return Vec::new();
        };
        return (lines.line(rs)..=lines.line(re.saturating_sub(1).max(rs)))
            .map(text)
            .collect();
    }
    // The lines starting outside every written range.
    (0..lines.count())
        .filter(|&l| {
            let s = lines.start(l);
            (s < out.len() || s == 0) && {
                let i = ranges.partition_point(|&(_, end, _)| end <= s);
                ranges.get(i).is_none_or(|&(rs, _, _)| rs > s)
            }
        })
        .map(text)
        .collect()
}

// ---- Text helpers -------------------------------------------------------

/// The largest char boundary of `s` at or before `at` (clamped to `s`).
pub fn floor_boundary(s: &str, at: usize) -> usize {
    let at = at.min(s.len());
    (0..=at).rev().find(|&i| s.is_char_boundary(i)).unwrap_or(0)
}

/// The line starts of a text, for byte-offset → line lookups.
#[derive(Clone)]
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

    /// Where line `line` starts.
    pub fn start(&self, line: usize) -> usize {
        self.starts.get(line).copied().unwrap_or(0)
    }

    /// How many lines there are.
    pub const fn count(&self) -> usize {
        self.starts.len()
    }

    /// The 0-based line holding byte `at` (how many `\n`s precede it).
    pub fn line(&self, at: usize) -> usize {
        self.starts.partition_point(|&s| s <= at).saturating_sub(1)
    }

    /// Whether `span` covers a line listed in `lines` (sorted or not).
    pub fn touches(&self, span: &Range<usize>, lines: &[usize]) -> bool {
        if lines.is_empty() {
            return false;
        }
        let a = self.line(span.start);
        let b = self.line(span.end.saturating_sub(1).max(span.start));
        lines.iter().any(|l| (a..=b).contains(l))
    }
}

/// The text of the line of `src` holding byte `at`, its trailing blanks
/// removed. The text's leading BOM is not part of its first line.
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

/// The text of each line of `src` holding one of the offsets `at`, in order,
/// each once.
pub fn lines_at<'s>(
    src: &'s str,
    index: &LineIndex,
    at: impl Iterator<Item = usize>,
) -> Vec<&'s str> {
    let mut lines: Vec<usize> = at.map(|a| index.line(floor_boundary(src, a))).collect();
    lines.sort_unstable();
    lines.dedup();
    lines
        .into_iter()
        .map(|l| line_text(src, index.start(l)))
        .collect()
}
