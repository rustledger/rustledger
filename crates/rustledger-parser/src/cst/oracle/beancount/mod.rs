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
/// it was discarding, or on an indented line) and then built.
///
/// beancount BUILDS such an entry, and the indented lines after it are its
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
        .filter(|s| s.built && !s.directive)
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

/// A token's text, shortened for a message.
fn token_text(src: &str, l: Lexeme) -> String {
    let text = src
        .get(l.start as usize..l.end as usize)
        .unwrap_or_default();
    let mut out: String = text.chars().take(40).collect();
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
            let _ = write!(msg, "`{}`", token_text(src, at));
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
        ParseErrorKind::InvalidPoptag(_)
        | ParseErrorKind::UnclosedPushtag(_)
        | ParseErrorKind::InvalidPopmeta(_)
        | ParseErrorKind::UnclosedPushmeta(_)
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
fn synthesize(slot: &Slot) -> ParseError {
    ParseError::new(
        ParseErrorKind::SyntaxError(slot.message.clone()),
        Span::new(slot.span.start, slot.span.end),
    )
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
pub fn overlaid_slots(src: &str) -> Vec<(u32, &'static str)> {
    reference(src, false)
        .slots
        .iter()
        .map(|s| {
            let kind = match s.kind {
                SlotKind::Lexical => "lexical",
                SlotKind::Syntax => "syntax",
                SlotKind::Fatal => "fatal",
                SlotKind::Semantic => "semantic",
            };
            (s.line, kind)
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
    if reference.slots.is_empty() && errors.is_empty() {
        return errors;
    }
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
    let first = errors.first().cloned();
    let out = super::reconcile(&lines, errors, &reference, &claims, classify, synthesize);
    never_clean(out, first)
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
