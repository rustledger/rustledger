//! Reference-oracle error reconciliation, independent of the input format.
//!
//! The pattern is "reference oracle -> reconciler -> deviation overlays":
//!
//! * A [`ReferenceOracle`] says, for a source text, which syntax errors the
//!   reference implementation of the format reports ([`Slot`]s: where, on
//!   which line, of which kind, with what was expected), which bytes its
//!   parser consumed while recovering from an error, and which statements it
//!   built or dropped ([`Reference`]).
//! * [`reconcile`] makes rledger's own diagnostics agree with the reference,
//!   line by line: on a line with reference slots, rledger's syntax
//!   diagnostics are assigned to the slots (kept for their better messages),
//!   a missing one is synthesized, and an extra one dropped; on a line the
//!   reference's recovery swallowed, rledger's syntax diagnostics are dropped;
//!   anywhere else they stand.
//! * [`DeviationOverlay`]s record where rledger deliberately parts from the
//!   reference. Each is named, cites its section of
//!   `docs/reference/compatibility.md`, and acts through three hooks: a
//!   rewrite of the input or the reference's tokens before it parses, a
//!   transform of the reference's errors, and a claim on rledger errors (or
//!   whole lines) that are rledger's own and stand whatever the reference
//!   says.
//!
//! Nothing here knows a format. A format frontend supplies the oracle, its
//! token type and its overlays, and classifies rledger's diagnostics
//! ([`ErrorClass`]); the beancount frontend lives in [`beancount`].

pub mod beancount;

use std::cell::Cell;
use std::ops::Range;
use std::sync::OnceLock;

use crate::ParseError;

thread_local! {
    /// How deep in nested parses this thread is (the recovery model parses
    /// parts of its input again).
    static DEPTH: Cell<u32> = const { Cell::new(0) };
    /// A per-thread override of the switch, for tests.
    pub static OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
}

/// The switch from the environment: `RLEDGER_ERROR_ORACLE=1` turns the
/// reconciliation on while it is off by default.
static FROM_ENV: OnceLock<bool> = OnceLock::new();

/// Whether parses reconcile their errors with the reference oracle.
pub fn enabled() -> bool {
    OVERRIDE.with(Cell::get).unwrap_or_else(|| {
        *FROM_ENV.get_or_init(|| std::env::var("RLEDGER_ERROR_ORACLE").is_ok_and(|v| v == "1"))
    })
}

/// Turns the reconciliation on or off for parses on this thread (`None`:
/// back to the environment's setting). For tests and measurements.
pub fn set_enabled_on_this_thread(on: Option<bool>) {
    OVERRIDE.with(|o| o.set(on));
}

/// Marks one parse in progress on this thread, for its lifetime.
pub struct NestingGuard {
    outermost: bool,
}

impl NestingGuard {
    pub fn enter() -> Self {
        let depth = DEPTH.with(|d| {
            let n = d.get() + 1;
            d.set(n);
            n
        });
        Self {
            outermost: depth == 1,
        }
    }

    /// Whether no other parse encloses this one.
    pub const fn is_outermost(&self) -> bool {
        self.outermost
    }
}

impl Drop for NestingGuard {
    fn drop(&mut self) {
        DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
    }
}

/// What kind of error a reference slot is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SlotKind {
    /// The reference's lexer rejected the text (an invalid token).
    Lexical,
    /// The reference's grammar rejected the token at the slot.
    Syntax,
    /// The reference's parser gave up (for example, its stack overflowed).
    Fatal,
}

/// One error the reference reports.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Slot {
    /// The offending token, as byte offsets in the source rledger parsed.
    pub span: Range<usize>,
    /// The 1-based line rledger reports the error on (after overlays: the
    /// reference's own line may differ, which an overlay records).
    pub line: u32,
    pub kind: SlotKind,
    /// A message for a diagnostic synthesized at this slot, in rledger's
    /// wording.
    pub message: String,
}

/// One statement of the reference's reduction trace.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Statement {
    /// Byte offsets in the source rledger parsed.
    pub start: usize,
    pub end: usize,
    /// Built by the reference, or dropped by its error recovery.
    pub built: bool,
}

/// What the reference says about one source text.
#[derive(Clone, Default, Debug)]
pub struct Reference {
    /// In source order.
    pub slots: Vec<Slot>,
    /// Byte ranges the reference's parser consumed while recovering from an
    /// error, sorted and disjoint.
    pub recovery: Vec<Range<usize>>,
    /// Statements the reference's recovery started (in the middle of a line
    /// it was discarding, say) and then built: their lines carry the
    /// reference's verdict, as the recovered lines do. Sorted.
    pub rebuilt: Vec<Range<usize>>,
    /// The reduction trace: every dropped statement, and the built ones when
    /// the oracle was asked for them.
    pub statements: Vec<Statement>,
}

impl Reference {
    /// Moves every offset `by` bytes later: from the frame of a text the
    /// reference read to that of a source it is a suffix of.
    pub fn shift(&mut self, by: usize) {
        let mv = |r: &mut Range<usize>| *r = r.start + by..r.end + by;
        for s in &mut self.slots {
            mv(&mut s.span);
        }
        self.recovery.iter_mut().for_each(mv);
        self.rebuilt.iter_mut().for_each(mv);
        for s in &mut self.statements {
            s.start += by;
            s.end += by;
        }
    }
}

/// A source of reference errors for one input format.
pub trait ReferenceOracle {
    /// The reference's token, which overlays may rewrite before it parses.
    type Token;

    /// The reference's verdict on `src`, with `overlays` applied.
    fn reference(
        &self,
        src: &str,
        overlays: &[&dyn DeviationOverlay<Self::Token>],
        full_trace: bool,
    ) -> Reference;
}

/// A deliberate, documented difference between rledger and the reference.
///
/// Every hook defaults to "no change"; an overlay implements the ones its
/// difference needs.
pub trait DeviationOverlay<T> {
    /// A short, stable name.
    fn name(&self) -> &'static str;

    /// The `docs/reference/compatibility.md` section documenting the
    /// difference (its heading anchor).
    fn compatibility_section(&self) -> &'static str;

    /// Where in `src` the reference starts reading: rledger parses a source
    /// whose first `n` bytes the reference never sees. Offsets stay those of
    /// `src`.
    fn input_start(&self, _src: &str) -> usize {
        0
    }

    /// Whether [`rewrite_token`](Self::rewrite_token) is implemented: the
    /// reference skips the per-token call for overlays that do not.
    fn rewrites_tokens(&self) -> bool {
        false
    }

    /// Rewrites one reference token before the reference parses it; `false`
    /// drops it.
    fn rewrite_token(&self, _src: &str, _token: &mut T) -> bool {
        true
    }

    /// Transforms the reference's verdict. `src` is the text the reference
    /// read (from [`input_start`](Self::input_start) on), and the reference's
    /// offsets are in its frame.
    fn transform_reference(&self, _src: &str, _reference: &mut Reference) {}

    /// Marks rledger's diagnostics that are its own, deliberate errors: they
    /// stand beside the reference's, whatever it says about their line.
    fn claim_own_errors(
        &self,
        _src: &str,
        _errors: &[ParseError],
        _reference: &Reference,
        _own: &mut [bool],
    ) {
    }

    /// Lines (1-based) on which rledger's diagnostics stand as they are and
    /// the reference's slots are not applied.
    fn claim_own_lines(
        &self,
        _src: &str,
        _errors: &[ParseError],
        _reference: &Reference,
        _lines: &mut Vec<u32>,
    ) {
    }
}

/// How the reconciler treats one rledger diagnostic.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ErrorClass {
    /// A syntax diagnostic: the reference decides whether its line has one,
    /// and how many.
    Syntax,
    /// A diagnostic the reference's oracle does not model (a check made after
    /// parsing, a state error at the end of the file): it stands.
    Other,
}

/// Line numbers of byte offsets in one source text.
pub struct LineIndex {
    /// Offsets of every `\n`.
    newlines: Vec<usize>,
}

impl LineIndex {
    pub fn new(src: &str) -> Self {
        Self {
            newlines: src
                .bytes()
                .enumerate()
                .filter_map(|(i, b)| (b == b'\n').then_some(i))
                .collect(),
        }
    }

    /// The 1-based line holding byte `at` (a `\n` is on the line it ends).
    pub fn line_of(&self, at: usize) -> u32 {
        u32::try_from(self.newlines.partition_point(|&nl| nl < at) + 1).unwrap_or(u32::MAX)
    }
}

/// rledger diagnostics and lines that overlays claimed as rledger's own.
#[derive(Default, Debug)]
pub struct Claims {
    /// Parallel to the diagnostics: `true` for one that stands whatever the
    /// reference says.
    pub own: Vec<bool>,
    /// Sorted lines on which rledger's diagnostics stand as they are and no
    /// slot is applied.
    pub own_lines: Vec<u32>,
}

/// Makes rledger's `errors` (sorted by start, spans in the frame `lines`
/// indexes) agree with `reference`, line by line, as the module documentation
/// describes.
///
/// `classify` sorts rledger's diagnostics, `claims` holds what overlays
/// claimed, and `synthesize` builds the diagnostic for a slot no rledger
/// diagnostic covers. The result is sorted by start.
pub fn reconcile(
    lines: &LineIndex,
    errors: Vec<ParseError>,
    reference: &Reference,
    claims: &Claims,
    classify: impl Fn(&ParseError) -> ErrorClass,
    synthesize: impl Fn(&Slot) -> ParseError,
) -> Vec<ParseError> {
    let owned_line = |line: u32| claims.own_lines.binary_search(&line).is_ok();
    // Lines the reference's recovery consumed something on, or that a
    // statement it rebuilt holds.
    let mut quiet_lines: Vec<u32> = Vec::new();
    for r in reference.recovery.iter().chain(&reference.rebuilt) {
        let first = lines.line_of(r.start);
        let last = lines.line_of(r.end.saturating_sub(1).max(r.start));
        for line in first..=last {
            if quiet_lines.last() != Some(&line) {
                quiet_lines.push(line);
            }
        }
    }
    quiet_lines.sort_unstable();
    quiet_lines.dedup();
    let quiet = |line: u32| quiet_lines.binary_search(&line).is_ok();

    // Slots grouped by line (an overlay may have moved one out of order).
    let mut by_line: Vec<&Slot> = reference.slots.iter().collect();
    by_line.sort_by_key(|s| (s.line, s.span.start));
    let mut groups: Vec<(u32, Vec<&Slot>)> = Vec::new();
    for slot in by_line {
        match groups.last_mut() {
            Some((line, group)) if *line == slot.line => group.push(slot),
            _ => groups.push((slot.line, vec![slot])),
        }
    }
    let has_slots = |line: u32| groups.binary_search_by_key(&line, |(l, _)| *l).is_ok();

    let mut out: Vec<ParseError> = Vec::with_capacity(errors.len());
    // rledger's syntax diagnostics on lines with slots, to assign to them.
    let mut pending: Vec<(u32, ParseError)> = Vec::new();
    // Lines with slots where a diagnostic stands anyway (an overlay's claim,
    // one the oracle does not model): each already reports the line, so it
    // takes the place of one slot no syntax diagnostic covers.
    let mut standing: Vec<u32> = Vec::new();
    for (i, e) in errors.into_iter().enumerate() {
        let line = lines.line_of(e.span.start);
        if owned_line(line) {
            out.push(e);
        } else if claims.own.get(i).copied().unwrap_or(false) || classify(&e) == ErrorClass::Other {
            if has_slots(line) {
                standing.push(line);
            }
            out.push(e);
        } else if has_slots(line) {
            pending.push((line, e));
        } else if !quiet(line) {
            // The reference reports nothing here and was not recovering:
            // rledger's own verdict on the line stands.
            out.push(e);
        }
    }
    pending.sort_by_key(|(line, e)| (*line, e.span.start));
    standing.sort_unstable();

    // Each line's slots take its syntax diagnostics: first a diagnostic on
    // the slot's own token, then the rest in order. A slot left over gets a
    // synthesized diagnostic, unless a standing diagnostic on the line takes
    // its place; a syntax diagnostic left over is dropped. Slots and
    // diagnostics are both in source order, so one merge pass pairs them.
    let mut pending = pending.into_iter().peekable();
    for (line, slots) in &groups {
        let mut candidates: Vec<Option<ParseError>> = Vec::new();
        while let Some((_, e)) = pending.next_if(|(l, _)| l == line) {
            candidates.push(Some(e));
        }
        if owned_line(*line) {
            continue;
        }
        let mut stand_ins =
            standing.partition_point(|&l| l <= *line) - standing.partition_point(|&l| l < *line);
        let mut taken: Vec<Option<ParseError>> = Vec::with_capacity(slots.len());
        let mut j = 0;
        for slot in slots {
            // Diagnostics wholly before this slot cannot overlap a later one.
            while candidates
                .get(j)
                .is_some_and(|c| c.as_ref().is_some_and(|e| ends_before(e.span, &slot.span)))
            {
                j += 1;
            }
            let hit = candidates
                .get_mut(j)
                .filter(|c| c.as_ref().is_some_and(|e| overlaps(e.span, &slot.span)))
                .and_then(Option::take);
            if hit.is_some() {
                j += 1;
            }
            taken.push(hit);
        }
        let mut rest = candidates.into_iter().flatten();
        for (slot, hit) in slots.iter().zip(taken) {
            if let Some(e) = hit.or_else(|| rest.next()) {
                out.push(e);
            } else if stand_ins > 0 {
                stand_ins -= 1;
            } else {
                out.push(synthesize(slot));
            }
        }
    }
    out.sort_by_key(|e| e.span.start);
    out
}

/// Whether a diagnostic ends before a slot's token starts (and so overlaps
/// no later slot either).
fn ends_before(span: crate::Span, slot: &Range<usize>) -> bool {
    span.end.max(span.start + 1) <= slot.start
}

/// Whether a diagnostic's span and a slot's token overlap (an empty range
/// counts as its one position).
fn overlaps(span: crate::Span, slot: &Range<usize>) -> bool {
    span.start < slot.end.max(slot.start + 1) && slot.start < span.end.max(span.start + 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseErrorKind, Span};

    fn err(start: usize, end: usize, msg: &str) -> ParseError {
        ParseError::new(
            ParseErrorKind::SyntaxError(msg.to_string()),
            Span::new(start, end),
        )
    }

    fn slot(span: Range<usize>, line: u32) -> Slot {
        Slot {
            span,
            line,
            kind: SlotKind::Syntax,
            message: "synth".to_string(),
        }
    }

    fn run(src: &str, errors: Vec<ParseError>, reference: &Reference) -> Vec<String> {
        let lines = LineIndex::new(src);
        reconcile(
            &lines,
            errors,
            reference,
            &Claims::default(),
            |e| match &e.kind {
                ParseErrorKind::SyntaxError(_) => ErrorClass::Syntax,
                _ => ErrorClass::Other,
            },
            |s| err(s.span.start, s.span.end, &s.message),
        )
        .into_iter()
        .map(|e| format!("{}:{}", lines.line_of(e.span.start), e.message()))
        .collect()
    }

    #[test]
    fn test_reconcile_assigns_synthesizes_and_drops() {
        let src = "aaa bbb\nccc\nddd\neee\n";
        let reference = Reference {
            // Line 1 has two slots, line 3 one, line 2 was swallowed.
            slots: vec![slot(0..3, 1), slot(4..7, 1), slot(12..15, 3)],
            recovery: std::iter::once(8..11).collect(),
            rebuilt: Vec::new(),
            statements: vec![],
        };
        let errors = vec![
            err(4, 7, "mine"),     // line 1, keeps the second slot
            err(8, 11, "quiet"),   // line 2, swallowed by recovery
            err(12, 13, "one"),    // line 3, keeps the slot
            err(13, 14, "extra"),  // line 3, beyond the slot count
            err(16, 19, "stands"), // line 4, the reference says nothing
        ];
        assert_eq!(
            run(src, errors, &reference),
            [
                "1:parse error: synth",
                "1:parse error: mine",
                "3:parse error: one",
                "4:parse error: stands"
            ]
        );
    }

    #[test]
    fn test_reconcile_other_errors_stand() {
        let src = "x\n";
        let reference = Reference {
            slots: vec![],
            recovery: std::iter::once(0..1).collect(),
            rebuilt: Vec::new(),
            statements: vec![],
        };
        let errors = vec![ParseError::new(
            ParseErrorKind::InvalidPoptag("t".to_string()),
            Span::new(0, 1),
        )];
        assert_eq!(run(src, errors, &reference).len(), 1);
    }

    #[test]
    fn test_line_index_lines_and_ranges() {
        let src = "ab\ncd\n";
        let lines = LineIndex::new(src);
        assert_eq!(lines.line_of(0), 1);
        assert_eq!(lines.line_of(2), 1);
        assert_eq!(lines.line_of(3), 2);
        assert_eq!(lines.line_of(6), 3);
    }
}
