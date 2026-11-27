//! The beancount frontend of the reference oracle: beancount 3.2.3's syntax
//! errors, computed from its token stream and its LALR tables.
//!
//! Provenance: the grammar is pta-standards' clean-room, MIT-licensed
//! `formats/beancount/v3/grammar/beancount.y` and the lexer follows its
//! `LEXICAL.md`, both at rustledger/pta-standards@1463db773ac5. pta-standards
//! wrote them from documentation and black-box experiments only, and checks
//! that they reproduce beancount's syntax-error count, lines and messages on
//! its corpora. [`tables`] is generated from the grammar by
//! `scripts/gen-beancount-lalr-tables.py`; [`lr`] replays it with bison's
//! `yacc.c` semantics. None of this is derived from beancount's sources.
//!
//! [`reconcile_errors`] is what `convert` calls: it runs the oracle over the
//! source and makes rledger's diagnostics agree with it (see
//! [`super::reconcile`]), with the deliberate differences of
//! `docs/reference/compatibility.md` applied as [`overlays`].

pub mod lexer;
pub mod lr;
mod overlays;
pub mod tables;

use std::collections::HashMap;
use std::fmt::Write as _;

use self::lexer::{Lexeme, Lexer};
use self::lr::Event;
use self::tables::Tok;
use super::{
    Claims, DeviationOverlay, ErrorClass, LineIndex, Reference, ReferenceOracle, Slot, SlotKind,
    Statement,
};
use crate::{ParseError, ParseErrorKind, Span};

/// beancount 3.2.3's parser, as a [`ReferenceOracle`].
pub struct BeancountOracle;

impl ReferenceOracle for BeancountOracle {
    type Token = Lexeme;

    fn reference(
        &self,
        src: &str,
        overlays: &[&dyn DeviationOverlay<Lexeme>],
        full_trace: bool,
    ) -> Reference {
        let start = overlays
            .iter()
            .map(|o| o.input_start(src))
            .max()
            .unwrap_or(0)
            .min(src.len());
        // Everything below reads the text the reference reads, from `start`
        // on, so a line start right after a stripped prefix is one; offsets
        // move back to `src`'s frame at the end.
        let text = src.get(start..).unwrap_or_default();
        // Byte offsets are u32 in the lexer, as they are in the syntax tree.
        let Ok(len) = u32::try_from(text.len()) else {
            return Reference::default();
        };
        let rewriters: Vec<&&dyn DeviationOverlay<Lexeme>> =
            overlays.iter().filter(|o| o.rewrites_tokens()).collect();
        let lexer = Lexer::new(text.as_bytes());
        let outcome = if rewriters.is_empty() {
            lr::run(lexer, len, full_trace)
        } else {
            let tokens = lexer.filter_map(|mut l| {
                rewriters
                    .iter()
                    .all(|o| o.rewrite_token(text, &mut l))
                    .then_some(l)
            });
            lr::run(tokens, len, full_trace)
        };
        let recovery: Vec<std::ops::Range<usize>> = outcome
            .recovery
            .iter()
            .map(|&(a, b)| a as usize..b as usize)
            .collect();
        let rebuilt = rebuilt_statements(text, &outcome.statements, &recovery);
        let mut slots: Vec<Slot> = outcome.events.iter().map(|e| slot_of(text, e)).collect();
        if full_trace {
            slots.extend(unbalanced_pops(text, &outcome.statements));
            slots.sort_by_key(|s| s.span.start);
        }
        let mut reference = Reference {
            slots,
            recovery,
            discarded: outcome
                .discarded
                .iter()
                .map(|&(a, b)| a as usize..b as usize)
                .collect(),
            rebuilt,
            statements: outcome
                .statements
                .iter()
                .map(|s| Statement {
                    start: s.start as usize,
                    end: s.end as usize,
                    built: s.built,
                })
                .collect(),
        };
        for o in overlays {
            o.transform_reference(text, &mut reference);
        }
        if start > 0 {
            reference.shift(start);
        }
        reference
    }
}

/// The dated entries bison's recovery started (their first token shifted
/// while it was recovering) away from a line start (in the middle of a line
/// it was discarding, or on an indented line), built or dropped later.
///
/// beancount reads such an entry, and the indented lines after it are its
/// body, so its errors there are the ones that entry's own parse gives
/// (rledger does not emit the entry itself, a recovery artifact).
fn rebuilt_statements(
    src: &str,
    statements: &[lr::Statement],
    recovery: &[std::ops::Range<usize>],
) -> Vec<std::ops::Range<usize>> {
    let b = src.as_bytes();
    statements
        .iter()
        .filter(|s| !s.directive)
        .map(|s| s.start as usize..s.end as usize)
        .filter(|s| {
            let in_recovery = recovery
                .binary_search_by(|r| {
                    if r.end <= s.start {
                        std::cmp::Ordering::Less
                    } else if r.start > s.start {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Equal
                    }
                })
                .is_ok();
            let mid_line = s.start > 0 && b.get(s.start - 1) != Some(&b'\n');
            in_recovery && mid_line
        })
        .collect()
}

/// Takes one push of `name` off `pushed`, if there is one.
fn pop(pushed: &mut HashMap<&str, usize>, name: &str) -> bool {
    match pushed.get_mut(name) {
        Some(n) if *n > 0 => {
            *n -= 1;
            true
        }
        _ => false,
    }
}

/// beancount's builder's errors for the `poptag` / `popmeta` directives its
/// grammar built (in order, `statements` holding every built one) that pop a
/// tag or key no built `pushtag` / `pushmeta` pushed: `Attempting to pop
/// absent tag`, on the directive's line. rledger reports these itself for
/// the directives it builds, but beancount's recovery also builds some
/// rledger does not (`2024-01-03 2024-01-04 poptag #t`, `$` then
/// `\t1poptag #t`), so their lines would otherwise lose the error.
fn unbalanced_pops(src: &str, statements: &[lr::Statement]) -> Vec<Slot> {
    // How many times each tag and key is pushed: a pop needs one, whichever.
    let mut tags: HashMap<&str, usize> = HashMap::new();
    let mut keys: HashMap<&str, usize> = HashMap::new();
    let mut out = Vec::new();
    // Where line counting has got to: statements come in source order.
    let (mut at, mut line) = (0usize, 1u32);
    for s in statements.iter().filter(|s| s.built && s.directive) {
        let (start, end) = (s.start as usize, (s.end as usize).min(src.len()));
        let Some(text) = src.get(start..end) else {
            continue;
        };
        let mut toks = Lexer::new(text.as_bytes());
        let (Some(head), Some(arg)) = (toks.next(), toks.next()) else {
            continue;
        };
        let name = text
            .get(arg.start as usize..arg.end as usize)
            .unwrap_or_default();
        let absent = match head.tok {
            Tok::Pushtag => {
                *tags.entry(name).or_default() += 1;
                None
            }
            Tok::Pushmeta => {
                *keys.entry(name).or_default() += 1;
                None
            }
            Tok::Poptag => (!pop(&mut tags, name))
                .then(|| format!("poptag of tag `{name}`, which was never pushed")),
            Tok::Popmeta => (!pop(&mut keys, name))
                .then(|| format!("popmeta of key `{name}`, which was never pushed")),
            _ => None,
        };
        if let Some(message) = absent {
            let before = src.as_bytes().get(at..start).unwrap_or_default();
            line += before.split(|&b| b == b'\n').count() as u32 - 1;
            at = start.max(at);
            out.push(Slot {
                span: start + head.start as usize..start + head.end as usize,
                // The line of the directive's keyword: beancount reports a
                // builder error on the directive's first line.
                line: line + head.line - 1,
                kind: SlotKind::Semantic,
                message,
            });
        }
    }
    out
}

/// The slot for one parser event, on beancount's own line (an overlay may
/// move it).
fn slot_of(src: &str, event: &Event) -> Slot {
    let (at, kind, message) = match *event {
        Event::Lexer(l) => (l, SlotKind::Lexical, lexer_error_message(src, l)),
        Event::Syntax { at, expected } => {
            (at, SlotKind::Syntax, rledger_message(src, at, expected))
        }
        Event::Exhausted(l) => (
            l,
            SlotKind::Fatal,
            "the input nests too deeply for beancount's parser (its stack holds 10000 states)"
                .to_string(),
        ),
    };
    Slot {
        span: at.start as usize..at.end as usize,
        line: at.line,
        kind,
        message,
    }
}

/// A token's text, shortened for a message: its first line, 40 characters
/// at most.
fn token_text(src: &str, l: Lexeme) -> String {
    let text = src
        .get(l.start as usize..l.end as usize)
        .unwrap_or_default();
    let first = text.split(['\r', '\n']).next().unwrap_or_default();
    let mut out: String = first.chars().take(40).collect();
    if out.len() < text.len() {
        out.push('…');
    }
    out
}

fn lexer_error_message(src: &str, l: Lexeme) -> String {
    format!("unexpected input: invalid token '{}'", token_text(src, l))
}

/// A terminal as rledger names it to a user.
const fn describe(tok: Tok) -> &'static str {
    match tok {
        Tok::Eof => "end of file",
        Tok::Error | Tok::Undef => "an invalid token",
        Tok::Eol => "end of line",
        Tok::Indent => "an indented line",
        Tok::Date => "a date",
        Tok::Account => "an account",
        Tok::Capital | Tok::Currency => "a currency",
        Tok::String => "a string",
        Tok::Number => "a number",
        Tok::Bool => "TRUE or FALSE",
        Tok::None => "NULL",
        Tok::Tag => "a tag",
        Tok::Link => "a link",
        Tok::Key => "a metadata key",
        Tok::Flag => "a flag",
        Tok::Txn => "`txn`",
        Tok::Pipe => "`|`",
        Tok::Atat => "`@@`",
        Tok::At => "`@`",
        Tok::Lcurlcurl => "`{{`",
        Tok::Rcurlcurl => "`}}`",
        Tok::Lcurl => "`{`",
        Tok::Rcurl => "`}`",
        Tok::Comma => "`,`",
        Tok::Tilde => "`~`",
        Tok::Hash => "`#`",
        Tok::Asterisk => "`*`",
        Tok::Slash => "`/`",
        Tok::Colon => "`:`",
        Tok::Plus => "`+`",
        Tok::Minus => "`-`",
        Tok::Lparen => "`(`",
        Tok::Rparen => "`)`",
        Tok::Balance
        | Tok::Open
        | Tok::Close
        | Tok::Commodity
        | Tok::Pad
        | Tok::Event
        | Tok::Price
        | Tok::Note
        | Tok::Document
        | Tok::Query
        | Tok::Custom
        | Tok::Pushtag
        | Tok::Poptag
        | Tok::Pushmeta
        | Tok::Popmeta
        | Tok::Option
        | Tok::Include
        | Tok::Plugin => "a keyword",
        Tok::Negative => "a sign",
    }
}

/// The terminals of an expected set, in bison's order.
fn expected_tokens(expected: u64) -> impl Iterator<Item = Tok> {
    (0..64usize)
        .filter(move |&i| expected & (1 << i) != 0)
        .filter_map(Tok::from_symbol)
}

/// The message rledger gives a syntax error it synthesizes at `at`.
fn rledger_message(src: &str, at: Lexeme, expected: u64) -> String {
    let mut msg = String::from("unexpected ");
    match at.tok {
        Tok::Eof | Tok::Eol => msg.push_str(describe(at.tok)),
        Tok::Indent => msg.push_str("indent"),
        _ => {
            let _ = write!(msg, "\"{}\"", token_text(src, at));
        }
    }
    let mut seen: Vec<&str> = Vec::new();
    for t in expected_tokens(expected) {
        let d = describe(t);
        if !seen.contains(&d) {
            seen.push(d);
        }
    }
    if (1..=4).contains(&seen.len()) {
        msg.push_str(", expected ");
        msg.push_str(&seen.join(" or "));
    }
    msg
}

/// bison's verbose message for a syntax error at `tok`, as beancount prints
/// it (`syntax error, unexpected X, expecting A or B`).
pub fn syntax_message(tok: Tok, expected: u64) -> String {
    let names: Vec<&str> = expected_tokens(expected).map(Tok::name).collect();
    let mut msg = format!("syntax error, unexpected {}", tok.name());
    if (1..=4).contains(&names.len()) {
        msg.push_str(", expecting ");
        msg.push_str(&names.join(" or "));
    }
    msg
}

/// How the reconciler treats an rledger diagnostic: the checks beancount
/// makes in its builder (after its grammar has read the entry) and the state
/// errors of push/pop directives are no syntax errors, so the oracle does not
/// model them and they stand.
fn classify(e: &ParseError) -> ErrorClass {
    match &e.kind {
        ParseErrorKind::UnclosedPushtag(_) | ParseErrorKind::UnclosedPushmeta(_) => {
            ErrorClass::FileLevel
        }
        ParseErrorKind::InvalidPoptag(_)
        | ParseErrorKind::InvalidPopmeta(_)
        | ParseErrorKind::DeprecatedPipeSymbol
        | ParseErrorKind::InvalidBookingMethod(_) => ErrorClass::Other,
        ParseErrorKind::SyntaxError(m)
            if super::super::convert::is_a_builder_message(m)
                || super::super::convert::is_a_builder_error(e)
                || m.starts_with("negative prices are not allowed") =>
        {
            ErrorClass::Other
        }
        _ => ErrorClass::Syntax,
    }
}

/// The diagnostic for a slot no rledger diagnostic covers.
fn synthesize(src: &str, slot: &Slot) -> ParseError {
    let span = Span::new(slot.span.start, slot.span.end);
    let text = src.get(slot.span.clone()).unwrap_or_default();
    // A number beancount's lexer rejects for its grouping or its length is
    // the invalid number rledger's own lexer would name.
    let number = !text.is_empty()
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || b == b',' || b == b'.');
    if slot.kind == SlotKind::Lexical && number && text.as_bytes()[0].is_ascii_digit() {
        return ParseError::new(ParseErrorKind::InvalidNumber(text.to_string()), span);
    }
    ParseError::new(ParseErrorKind::SyntaxError(slot.message.clone()), span)
}

/// beancount's own tokens over `src`, no overlay applied: `(name, line,
/// start, end)`, as `beancount.parser.lexer.lex_iter_string` reports them.
/// For drift tests against beancount.
pub fn reference_tokens(src: &str) -> Vec<(&'static str, u32, usize, usize)> {
    Lexer::new(src.as_bytes())
        .map(|l| (l.tok.name(), l.line, l.start as usize, l.end as usize))
        .collect()
}

/// beancount's own errors over `src`, no overlay applied: `(line, message)`,
/// where a syntax error's message is beancount's and a lexer error's is
/// `LexerError`. For drift tests against beancount.
pub fn reference_errors(src: &str) -> Vec<(u32, String)> {
    let Ok(len) = u32::try_from(src.len()) else {
        return Vec::new();
    };
    lr::run(Lexer::new(src.as_bytes()), len, false)
        .events
        .iter()
        .map(|e| match *e {
            Event::Lexer(l) => (l.line, "LexerError".to_string()),
            Event::Syntax { at, expected } => (at.line, syntax_message(at.tok, expected)),
            Event::Exhausted(l) => (l.line, "memory exhausted".to_string()),
        })
        .collect()
}

/// Whether beancount's grammar drops the statement `text` starts with: it
/// builds no statement starting at `text`'s first token (its recovery pops
/// the one it had started, or its lexer rejects that first token). `text`
/// is a directive's own text from its first token, with what follows it, so
/// an invalid token on the next line that fails the statement counts too.
/// From the reduction trace of beancount's own parse, with none of rledger's
/// deliberate differences applied: the question is what beancount builds.
pub fn drops_statement(text: &str) -> bool {
    let Ok(len) = u32::try_from(text.len()) else {
        return false;
    };
    let mut tokens = Lexer::new(text.as_bytes()).peekable();
    let Some(first) = tokens.peek().map(|l| l.start) else {
        return false;
    };
    let outcome = lr::run(tokens, len, true);
    !outcome
        .statements
        .iter()
        .any(|s| s.built && s.start == first)
}

/// rledger's deliberate parse-error differences from beancount, as `(name,
/// section)`: each overlay's name and the `docs/reference/compatibility.md`
/// section (heading anchor) documenting it.
pub fn deviation_overlays() -> Vec<(&'static str, &'static str)> {
    let set = overlays::Overlays::new();
    set.all()
        .iter()
        .map(|o| (o.name(), o.compatibility_section()))
        .collect()
}

/// The reference's slots on `src`, overlays applied, as `(line, kind)` with
/// `kind` `"lexical"`, `"syntax"` or `"fatal"`: what reconciliation would
/// hold rledger's errors to. For drift tests against beancount.
///
/// The places overlays keep for rledger's own diagnostics
/// (`SlotKind::StandIn`) are no errors of beancount's, so they are left out.
pub fn overlaid_slots(src: &str) -> Vec<(u32, &'static str)> {
    reference(src, false)
        .slots
        .iter()
        .filter_map(|s| {
            let kind = match s.kind {
                SlotKind::Lexical => "lexical",
                SlotKind::Syntax => "syntax",
                SlotKind::Fatal => "fatal",
                SlotKind::Semantic => "semantic",
                SlotKind::StandIn => return None,
            };
            Some((s.line, kind))
        })
        .collect()
}

/// Whether rledger's gate skips the oracle on `src`: its own parse reports
/// no error. The drift check holds the gate to the reference.
pub fn gate_skips_grammar(src: &str) -> bool {
    let _off = ForcedOff::new();
    crate::parse(src).errors.is_empty()
}

/// Turns the reconciliation off on this thread while it lives.
struct ForcedOff(Option<bool>);

impl ForcedOff {
    fn new() -> Self {
        let before = super::OVERRIDE.with(std::cell::Cell::get);
        super::set_enabled_on_this_thread(Some(false));
        Self(before)
    }
}

impl Drop for ForcedOff {
    fn drop(&mut self) {
        super::set_enabled_on_this_thread(self.0);
    }
}

/// The beancount reference's verdict on `source` (the text as given, a
/// byte-0 BOM included), with every overlay applied.
fn reference(source: &str, full_trace: bool) -> Reference {
    let set = overlays::Overlays::new();
    BeancountOracle.reference(source, &set.all(), full_trace)
}

/// Makes rledger's parse `errors` over `source` (spans in `source`'s frame,
/// a byte-0 BOM included) agree with beancount's syntax errors, line by line,
/// keeping the documented deliberate differences.
pub fn reconcile_errors(source: &str, errors: Vec<ParseError>) -> Vec<ParseError> {
    if errors.is_empty() {
        // Where rledger reports nothing, beancount's grammar rejects nothing
        // either (its overlaid reference has no syntax slot) on every input of
        // the parity corpora: `scripts/compat-beancount-oracle-drift.py`
        // checks that on each of them, so a clean file pays nothing for the
        // oracle. Only beancount's lexer can disagree there (a capital at the
        // end of the input), on 20 fuzz inputs, which the check counts.
        return errors;
    }
    let set = overlays::Overlays::new();
    let all = set.all();
    let reference = BeancountOracle.reference(source, &all, true);
    let first = errors.first().cloned();
    let errors = with_rebuilt_builder_errors(source, errors, &reference);
    let mut claims = Claims {
        own: vec![false; errors.len()],
        own_lines: Vec::new(),
    };
    for o in &all {
        o.claim_own_errors(source, &errors, &reference, &mut claims.own);
        o.claim_own_lines(source, &errors, &reference, &mut claims.own_lines);
    }
    claims.own_lines.sort_unstable();
    claims.own_lines.dedup();
    let lines = LineIndex::new(source);
    let mut out = super::reconcile(
        &lines,
        errors,
        &reference,
        &claims,
        classify,
        |slot| synthesize(source, slot),
        |from, to| line_ends_inside_strings(source, from, to),
    );
    name_invalid_tokens(source, &mut out, &reference);
    never_clean(out, first)
}

/// The message rledger's parser gives a token it cannot read, before it is
/// named.
const UNNAMED_INVALID_TOKEN: &str = "unexpected input";

/// Names the token in each of rledger's unnamed `unexpected input` errors
/// that stands for one of beancount's lexer errors (`unexpected input:
/// invalid token 'h'`, as bean-check's `Invalid token: 'h'`), so the editor
/// still names it: the narrowest error on the token, which may be a line
/// error holding it and no other token. `out` is sorted by start, as the
/// slots are.
fn name_invalid_tokens(source: &str, out: &mut [ParseError], reference: &Reference) {
    let lexical: Vec<&Slot> = reference
        .slots
        .iter()
        .filter(|s| s.kind == SlotKind::Lexical && s.span.start < s.span.end)
        .collect();
    if lexical.is_empty() {
        return;
    }
    let overlaps = |e: &ParseError, s: &Slot| {
        s.span.start < e.span.end.max(e.span.start + 1) && e.span.start < s.span.end
    };
    let width = |e: &ParseError| e.span.end - e.span.start;
    // For each error, the first lexical slot it overlaps and how many it
    // does; for each slot, the narrowest error on it. Both lists are sorted
    // by start, so each error steps over only the slots it overlaps.
    let mut narrowest = vec![usize::MAX; lexical.len()];
    let mut first_slot: Vec<Option<(usize, usize)>> = Vec::with_capacity(out.len());
    let mut k = 0;
    for e in out.iter() {
        while lexical.get(k).is_some_and(|s| s.span.end <= e.span.start) {
            k += 1;
        }
        let n = lexical[k.min(lexical.len())..]
            .iter()
            .take_while(|s| overlaps(e, s))
            .count();
        for w in &mut narrowest[k..k + n] {
            *w = (*w).min(width(e));
        }
        first_slot.push((n > 0).then_some((k, n)));
    }
    for (e, at) in out.iter_mut().zip(first_slot) {
        // Only an error on one token is named by it, and only the narrowest
        // there: not a line error holding several tokens, nor one holding a
        // token another error names.
        let Some((k, 1)) = at else { continue };
        if width(e) > narrowest[k]
            || !matches!(&e.kind, ParseErrorKind::SyntaxError(m) if m == UNNAMED_INVALID_TOKEN)
        {
            continue;
        }
        let text = source.get(lexical[k].span.clone()).unwrap_or_default();
        e.kind = ParseErrorKind::SyntaxError(format!(
            "{UNNAMED_INVALID_TOKEN}: invalid token '{}'",
            super::super::convert::invalid_token_name(text)
        ));
    }
}

/// Whether every line end in bytes `from..to` of `src` is inside a string:
/// a statement runs over a line end only inside one (`event "x\nb" x`). The
/// text is read from `from` on, so a string open before it is not seen; an
/// rledger error starts at a statement's token, never inside a string.
/// Linear in the range.
fn line_ends_inside_strings(src: &str, from: usize, to: usize) -> bool {
    let Some(text) = src.as_bytes().get(from..to.min(src.len())) else {
        return false;
    };
    let mut in_string = false;
    let mut escaped = false;
    for &b in text {
        match b {
            _ if escaped => escaped = false,
            b'\\' if in_string => escaped = true,
            b'"' => in_string = !in_string,
            b'\n' if !in_string => return false,
            _ => {}
        }
    }
    true
}

/// `errors` plus the builder errors of the entries bison's recovery builds
/// in the middle of a line (the reference's `rebuilt` statements): beancount
/// builds such an entry, so it runs its builder's checks on it (an invalid
/// booking method, a negative price), where rledger, which reads the entry
/// as part of a failed line, does not. Each such entry's text is parsed on
/// its own once (the nesting guard keeps that parse from consulting the
/// oracle in turn), and its errors that are no syntax errors are added at
/// their place, unless rledger already reports the same one. Sorted by start.
fn with_rebuilt_builder_errors(
    source: &str,
    mut errors: Vec<ParseError>,
    reference: &Reference,
) -> Vec<ParseError> {
    if reference.rebuilt.is_empty() {
        return errors;
    }
    // Only the ones beancount builds: it checks nothing of a dropped one.
    // Looked up in a set, and `errors` (sorted by start) searched by start,
    // so many rebuilt entries stay linear.
    let built_spans: std::collections::HashSet<(usize, usize)> = reference
        .statements
        .iter()
        .filter(|s| s.built)
        .map(|s| (s.start, s.end))
        .collect();
    let built = |r: &std::ops::Range<usize>| built_spans.contains(&(r.start, r.end));
    let given = errors.len();
    let mut added: HashMap<(usize, usize), Vec<ParseErrorKind>> = HashMap::new();
    for r in &reference.rebuilt {
        let Some(text) = source.get(r.clone()) else {
            continue;
        };
        let built = built(r);
        for mut e in crate::parse(text).errors {
            // Of one beancount drops, only what its grammar reported while it
            // read it: a pipe in the header, before the drop.
            let wanted = if built {
                classify(&e) == ErrorClass::Other
            } else {
                matches!(e.kind, ParseErrorKind::DeprecatedPipeSymbol)
            };
            if !wanted {
                continue;
            }
            e.span = Span::new(e.span.start + r.start, e.span.end + r.start);
            let at = errors[..given].partition_point(|x| x.span.start < e.span.start);
            let reported = errors[at..given]
                .iter()
                .take_while(|x| x.span.start == e.span.start)
                .any(|x| x.span == e.span && x.kind == e.kind);
            let kinds = added.entry((e.span.start, e.span.end)).or_default();
            if !reported && !kinds.contains(&e.kind) {
                kinds.push(e.kind.clone());
                errors.push(e);
            }
        }
    }
    errors.sort_by_key(|e| e.span.start);
    errors
}

/// A parse rledger found an error in never comes out clean: the error oracle
/// decides where its errors are and how many, not whether it has any. (So a
/// source keeps a parse error exactly when it had one, which the loader's
/// cache relies on.) `first` is rledger's first error before reconciling.
fn never_clean(mut out: Vec<ParseError>, first: Option<ParseError>) -> Vec<ParseError> {
    if out.is_empty()
        && let Some(e) = first
    {
        out.push(e);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(line, message)` for each of beancount's errors on `src`, before
    /// overlays.
    fn beancount_errors(src: &str) -> Vec<(u32, String)> {
        let out = lr::run(Lexer::new(src.as_bytes()), src.len() as u32, false);
        out.events
            .iter()
            .map(|e| match *e {
                Event::Lexer(l) => (l.line, "LexerError".to_string()),
                Event::Syntax { at, expected } => (at.line, syntax_message(at.tok, expected)),
                Event::Exhausted(l) => (l.line, "memory exhausted".to_string()),
            })
            .collect()
    }

    /// `(line, message)` of the builder slots on `src`.
    fn pops(src: &str) -> Vec<(u32, String)> {
        reference(src, true)
            .slots
            .into_iter()
            .filter(|s| s.kind == SlotKind::Semantic)
            .map(|s| (s.line, s.message))
            .collect()
    }

    #[test]
    fn test_name_invalid_tokens_names_the_narrowest_error_on_one_token() {
        let messages = |src: &str| -> Vec<String> {
            crate::parse(src)
                .errors
                .iter()
                .map(ToString::to_string)
                .collect()
        };
        let head = "2024-01-01 open Assets:A\n2024-01-02 *\n  Assets:A  1 USD\n";
        assert_eq!(
            messages(&format!("{head}  * h\n")),
            ["parse error: unexpected input: invalid token 'h'"]
        );
        // A line error holding several invalid tokens is not named by one;
        // each token's own error is.
        let tags = messages("#TODO buy 27\" monitor\n");
        assert_eq!(tags[0], "parse error: unexpected input", "{tags:?}");
        assert!(
            tags[1..].iter().all(|m| m.contains("invalid token")),
            "{tags:?}"
        );
    }

    #[test]
    fn test_unbalanced_pops_replays_beancounts_tag_and_key_stacks() {
        assert_eq!(pops("pushtag #t\npoptag #t\n"), [] as [(u32, String); 0]);
        assert_eq!(
            pops("\npoptag #t\n"),
            [(2, "poptag of tag `#t`, which was never pushed".to_string())]
        );
        assert_eq!(
            pops("pushmeta kk: 1\npopmeta kk:\npopmeta kk:\n"),
            [(3, "popmeta of key `kk`, which was never pushed".to_string())]
        );
        // Built by bison's recovery in the middle of a line rledger fails.
        assert_eq!(
            pops("2024-01-02 123\n2024-01-03 2024-01-04 poptag #t\n").len(),
            1
        );
        assert_eq!(pops("$\n\t1poptag #t\n")[0].0, 2);
        // A push inside a line bison fails is not built, so its pop is absent.
        assert_eq!(pops("pushtag #t $\npoptag #t\n")[0].0, 2);
    }

    #[test]
    fn test_never_clean_keeps_an_error_where_there_was_one() {
        let e = ParseError::new(ParseErrorKind::SyntaxError("x".into()), Span::new(0, 1));
        assert_eq!(
            never_clean(Vec::new(), Some(e.clone())),
            std::slice::from_ref(&e)
        );
        assert_eq!(never_clean(Vec::new(), None), [] as [ParseError; 0]);
        let other = ParseError::new(ParseErrorKind::SyntaxError("y".into()), Span::new(2, 3));
        assert_eq!(never_clean(vec![other.clone()], Some(e)), [other]);
    }

    #[test]
    fn test_syntax_message_matches_beancounts_wording() {
        assert_eq!(
            beancount_errors("2024-01-01 open Assets:A\n  Assets:B 1 USD\n"),
            [(
                2,
                "syntax error, unexpected ACCOUNT, expecting end of file or EOL or KEY".to_string()
            )]
        );
        assert_eq!(
            beancount_errors("2024-01-01 * \"x\"\n  Assets:A 1 USD {1 USD,}\n"),
            [(
                2,
                "syntax error, unexpected RCURL, expecting HASH or CAPITAL or CURRENCY".to_string()
            )]
        );
    }

    #[test]
    fn test_rledger_message_names_tokens_for_users() {
        let src = "2024-01-01 open\n";
        let reference = reference(src, false);
        assert_eq!(reference.slots.len(), 1);
        assert_eq!(
            reference.slots[0].message,
            "unexpected end of line, expected an account"
        );
        assert_eq!(
            reference.slots[0].line, 1,
            "moved back to the failing line (#2993)"
        );
    }

    /// The smaller input size of the linear-time test.
    const LINEAR_N: usize = 5_000;

    /// Seconds to compute the reference and reconcile `errors` over `src`,
    /// best of three.
    fn cost(src: &str, errors: &[ParseError]) -> f64 {
        (0..3)
            .map(|_| {
                let t = std::time::Instant::now();
                std::hint::black_box(reconcile_errors(src, errors.to_vec()));
                t.elapsed().as_secs_f64()
            })
            .fold(f64::MAX, f64::min)
    }

    /// An rledger error at the start of every line of `src`, for the
    /// reconciler to work through.
    fn an_error_per_line(src: &str) -> Vec<ParseError> {
        let mut at = 0;
        let mut out = Vec::new();
        for line in src.split_inclusive('\n') {
            out.push(ParseError::new(
                ParseErrorKind::SyntaxError("x".to_string()),
                Span::new(at, at + 1),
            ));
            at += line.len();
        }
        out
    }

    /// The oracle (lexer, driver, overlays, reconciler) does work linear in
    /// its input on every shape that makes one of its parts look ahead or
    /// back: four times the input costs about four times the time, nowhere
    /// near the sixteen a quadratic step would.
    #[test]
    fn test_reference_work_is_linear_in_the_input() {
        let shapes: [(&str, fn(usize) -> String); 15] = [
            ("invalid lines", |n| "$\n".repeat(n)),
            ("indented comments after a gap", |n| {
                "; c\n".to_string() + &"  ; c\n".repeat(n)
            }),
            ("orphan BOM lines", |n| "\n  \u{feff}x\n".repeat(n)),
            ("failed postings", |n| {
                "2024-01-01 *\n".to_string() + &"  Assets:A 1 USD 5\n".repeat(n)
            }),
            ("nested signs", |n| {
                format!("2024-01-01 custom \"x\" {}1\n", "-".repeat(n))
            }),
            ("nested parentheses", |n| {
                format!("2024-01-01 custom \"x\" {}1\n", "(".repeat(n))
            }),
            ("one long line of pipes", |n| {
                format!("2024-01-01 * {}\n", "|".repeat(n))
            }),
            ("strings cut by a backslash", |n| "\"a b c\\\n".repeat(n)),
            ("multi-line strings in recovery", |n| {
                "$ \"a\n\n\n\"\n".repeat(n)
            }),
            ("one invalid run", |n| "x".repeat(n * 4)),
            ("currency tails", |n| {
                ("AB".to_string() + &"'".repeat(15) + "x ").repeat(n)
            }),
            ("stray carriage returns", |n| {
                "2024-01-01 open Assets:A\r\r x\n".repeat(n)
            }),
            ("entries before unreadable lines", |n| {
                "2024-01-01 open Assets:A\n$\n".repeat(n)
            }),
            ("ignored lines", |n| "* heading\n#!x\n".repeat(n)),
            ("unbalanced pops", |n| "poptag #t\npushtag #u\n".repeat(n)),
        ];
        for (label, make) in shapes {
            let (small, large) = (make(LINEAR_N), make(4 * LINEAR_N));
            let (es, el) = (an_error_per_line(&small), an_error_per_line(&large));
            linear(label, &small, &es, &large, &el);
        }
        // One line holding thousands of slots, with as many rledger errors.
        let line = |n: usize| "$ ".repeat(n) + "\n";
        let at_each = |src: &str| -> Vec<ParseError> {
            (0..src.len() / 2)
                .map(|i| {
                    ParseError::new(
                        ParseErrorKind::SyntaxError("x".to_string()),
                        Span::new(2 * i, 2 * i + 1),
                    )
                })
                .collect()
        };
        let (small, large) = (line(LINEAR_N), line(4 * LINEAR_N));
        linear(
            "one line of invalid tokens",
            &small,
            &at_each(&small),
            &large,
            &at_each(&large),
        );
    }

    /// Asserts the work on `large` (four times `small`) is about four times
    /// the work on `small`.
    fn linear(label: &str, small: &str, es: &[ParseError], large: &str, el: &[ParseError]) {
        let (ts, tl) = (cost(small, es), cost(large, el));
        assert!(
            tl < ts.mul_add(9.0, 0.02),
            "{label}: {:.1} ms for {} bytes, {:.1} ms for {} bytes",
            ts * 1e3,
            small.len(),
            tl * 1e3,
            large.len()
        );
    }

    /// A whole parse with the oracle does work linear in its input on every
    /// shape of beancount's error recovery: failed lines and the quiet ones
    /// after them, entries its recovery starts mid-line (each parsed once
    /// more on its own for its builder's errors), stray `\r`s, BOMs. (These
    /// are the shapes the hand-modeled recovery passes were held linear on.)
    #[test]
    fn test_parse_with_the_oracle_is_linear_on_recovery_shapes() {
        let shapes: [(&str, fn(usize) -> String); 24] = [
            ("`$` lines", |n| "$\n".repeat(n)),
            ("`!` lines", |n| "!\n".repeat(n)),
            ("`$` and a posting", |n| "$\n  Assets:A 1 USD\n".repeat(n)),
            ("`$` then postings", |n| {
                "$\n".to_string() + &"  Assets:A 1 USD\n".repeat(n)
            }),
            ("`pushmeta k:` lines", |n| "pushmeta k: \"v\"\n".repeat(n)),
            ("one long `$` line", |n| "$ ".repeat(n) + "\n"),
            ("failed headers and blanks", |n| {
                "pushtag #a $\n\n  2024-02-30 5\n".repeat(n)
            }),
            ("bad postings", |n| {
                "2024-01-02 * \"n\"\n".to_string() + &"  Assets:A 1 USD 5\n".repeat(n)
            }),
            ("second-date entries", |n| {
                "2024-01-02 2024-01-03 * \"n\"\n  Assets:A 1 USD\n".repeat(n)
            }),
            ("entries on one line", |n| {
                "$ 2024-01-02 * \"y\" ".repeat(n) + "\n"
            }),
            ("nested entries", |n| {
                "$\n".to_string() + &"  2024-01-02 * \"n\"\n".repeat(n)
            }),
            ("statements after windows", |n| {
                "$\n2024-01-30 open\n".repeat(n)
            }),
            ("BOM-led lines", |n| {
                "\u{FEFF}g \u{FEFF}Assets:A\n".repeat(n)
            }),
            ("entries with an invalid token", |n| {
                "$ 2024-01-02 * \"y\" $\n  Assets:A 1 USD\n".repeat(n)
            }),
            ("orphan indented lines", |n| "  $x\n\n\n".repeat(n)),
            ("orphan lines after indented comments", |n| {
                "\n".to_string() + &"  ; c\n  ; d\n\n  $x\n\n\n".repeat(n)
            }),
            ("lines after options in a body", |n| {
                "2024-01-02 * \"n\"\n".to_string()
                    + &"  option \"title\" \"x\"\n  $x\n  Assets:B 1 USD\n".repeat(n)
            }),
            ("undated declarations failing mid-line", |n| {
                "~ popmeta kk: @ x\n~ pushmeta kk: \"v\" @\n".repeat(n)
            }),
            ("stray `\\r` lines", |n| "\r$\n  Assets:A 1 USD\n".repeat(n)),
            // Many expressions that cannot be evaluated, each claimed as
            // rledger's own: once quadratic in their number.
            ("expressions dividing by zero", |n| {
                "2024-01-01 custom \"x\" 1/0 $\n".repeat(n)
            }),
            // Many entries recovery rebuilds, each with a builder error to
            // merge: once quadratic in their number.
            ("rebuilt entries with stray `\\r`s", |n| {
                "$\n".to_string()
                    + &"  2024-01-02 open\rAssets:Z\n  2024-01-02 open Assets:Z\n".repeat(n)
            }),
            ("entries nested in entries", |n| {
                "$\n".to_string() + &"  2024-01-02 open Assets:Z \"XYZ\"\n".repeat(n)
            }),
            ("windows going on past an entry's body", |n| {
                "$ 2024-01-02 * \"y\"\n  2024-02-30 5\n\"s\"\n".repeat(n)
            }),
            ("pipes in entries recovery drops", |n| {
                "AB-C\nkey:2024/01/03  P | 1\n".repeat(n)
            }),
        ];
        super::super::set_enabled_on_this_thread(Some(true));
        let time = |src: &str| {
            (0..2)
                .map(|_| {
                    let t = std::time::Instant::now();
                    std::hint::black_box(crate::parse(src));
                    t.elapsed().as_secs_f64()
                })
                .fold(f64::MAX, f64::min)
        };
        for (label, make) in shapes {
            let (small, large) = (make(500), make(2000));
            let (ts, tl) = (time(&small), time(&large));
            assert!(
                tl < ts.mul_add(9.0, 0.05),
                "{label}: {:.1} ms for {} bytes, {:.1} ms for {} bytes",
                ts * 1e3,
                small.len(),
                tl * 1e3,
                large.len()
            );
        }
        super::super::set_enabled_on_this_thread(None);
    }

    /// No input makes the oracle panic: each ASCII byte in each position the
    /// lexer tells apart, and every prefix of a ledger using every construct.
    #[test]
    fn test_reference_never_panics() {
        let ledger = "\u{feff}2024-01-01 open Assets:A USD \"FIFO\"\n  k: 1\n\
            2024-01-02 * \"p\" \"n\" #t ^l\n  ! Assets:A  -1.5 HOOL {1,000.00 # 2 USD, \
            2024-01-01, \"x\"} @@ 3 USD\n\tAssets:B\n  ; c\n\
            2024-01-03 balance Assets:A 1 ~ 0.1 USD\r\npushmeta k: (1 + 2) * -3 /6J\n";
        for end in 0..=ledger.len() {
            if ledger.is_char_boundary(end) {
                let _ = reconcile_errors(&ledger[..end], an_error_per_line(&ledger[..end]));
                let _ = reference_errors(&ledger[..end]);
            }
        }
        for b in 0u8..=127 {
            let c = char::from(b);
            for src in [
                format!("{c}"),
                format!("{c}{c}x\n"),
                format!("  {c}\n"),
                format!("2024-01-01 {c} \"a\"\n  Assets:A {c}1 USD\n"),
                format!("A{c}B:C{c}"),
                format!("\"{c}\\{c}\""),
                format!("1{c},000{c}.5"),
            ] {
                let _ = reconcile_errors(&src, an_error_per_line(&src));
            }
        }
    }
}
