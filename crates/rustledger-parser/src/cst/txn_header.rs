//! Transaction-header token-sequence validation (#2008).
//!
//! beancount's grammar for a transaction header is
//!
//! ```text
//! transaction : DATE txn txn_strings tags_links eol posting_or_kv_list
//! txn_strings : %empty | txn_strings STRING
//! tags_links  : %empty | tags_links LINK | tags_links TAG
//! ```
//!
//! so strings come first, then tags and links in any order, then EOL. The
//! `>2 strings` case parses but is rejected by the builder with *"Too many
//! strings on transaction description"*.
//!
//! Our CST parser is deliberately permissive — it is lossless and recovers
//! rather than rejecting — so nothing downstream re-imposed that shape, and
//! three constructs beancount refuses loaded here without a word: a string
//! after a tag, junk after the narration, and more than two strings (#2008
//! cases 3, 4, and 6/7 — two fixtures of the same construct). Being *more*
//! permissive than the reference is the wrong
//! direction for a compatibility reimplementation: the file looks fine here
//! and breaks for anyone who takes it back to beancount.
//!
//! # One rule, two walkers
//!
//! The check is expressed once, over `(SyntaxKind, Range<usize>)` pairs, so
//! the red walker (`convert::transaction_header_check`) and the green walker
//! (`green::tl_transaction_header_check`) share the *logic* and differ only in
//! how they enumerate tokens. Per the Canonical-Function Discipline in
//! AGENTS.md, the green/red parser mirrors are a known drift source; a rule
//! this fiddly is exactly the kind that drifts. `fuzz_green_eq_red` and the
//! parity tests pin the two walkers against each other.
//!
//! Kind and byte range are all the rule needs — even the single-character
//! `CURRENCY` flag (`2012-12-17 P "Payee" "Narration"`) is decided by
//! `range.len() == 1`, with no access to the source text.

use crate::SyntaxKind;
use std::ops::Range;

/// What is wrong with a transaction header's token sequence.
///
/// At most one is reported per header. beancount stops at the first problem
/// too (a parse error aborts the rule; `Too many strings` returns `None` from
/// the builder), and a malformed header otherwise produces a cascade —
/// `A:*:B` alone lexes into five tokens that are each individually
/// unexpected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum HeaderDefect {
    /// A `STRING` after a `TAG`/`LINK`. beancount: `syntax error, unexpected
    /// STRING, expecting end of file or EOL or TAG or LINK`.
    StringAfterTagOrLink,
    /// More than two header strings; the payload is the total count.
    /// beancount: `Too many strings on transaction description`.
    TooManyStrings(usize),
    /// A token with no place in a transaction header at all.
    UnexpectedToken,
    /// A one-letter flag (`P`) with something other than a space, a tab or a
    /// `\n` right after it: beancount reads a lone capital as its `CAPITAL`
    /// token only there, so `P"x"`, `P;c` and `P\r\n` are an invalid token
    /// (#2802).
    GluedLetterFlag,
    /// No flag between the date and the first string, tag or link
    /// (`2024-01-02 "x"`). beancount's `txn` is not optional, so this is
    /// `syntax error, unexpected STRING` (or `TAG`, `LINK`) there (#2905).
    /// Reported at that token.
    MissingFlag,
}

/// Trivia and separators that may appear anywhere in a header.
///
/// `COMMENT` covers the trailing `; note` form. The `%`/`#!`/`#+` comment
/// kinds are attached as leading trivia by the Directive-Terminator Rule, so
/// they are skipped before the header even starts, but they are listed for
/// symmetry with `Transaction::header_tokens`.
const fn is_header_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::WHITESPACE
            | SyntaxKind::NEWLINE
            | SyntaxKind::COMMENT
            | SyntaxKind::PERCENT_COMMENT
            | SyntaxKind::SHEBANG
            | SyntaxKind::EMACS_DIRECTIVE
            // A mid-header BOM is already reported as `BomInDirectiveBody`;
            // do not double-report it as an unexpected token.
            | SyntaxKind::BOM
            // The deprecated `|` payee/narration separator has its own
            // recoverable diagnostic (`DeprecatedPipeSymbol`), which keeps
            // the directive. Claiming it here would turn a warning-shaped
            // legacy accommodation into a hard rejection.
            | SyntaxKind::PIPE
    )
}

/// Tokens valid in the flag position — between `DATE` and the first
/// `STRING`/`TAG`/`LINK`. Mirrors `TransactionFlag::cast`, including its
/// single-character rule for `CURRENCY` (a ticker letter used as a flag).
///
/// beancount's `txn` is ONE token (`TXN | FLAG | ASTERISK | HASH | CAPITAL`),
/// so a second flag (`2024-01-01 * * "x"`, `2024-01-01 !*`, `2024-01-01 * A
/// "x"`) is a syntax error there. [`first_header_defect`] counts them (#2802,
/// stage 3); this only says which tokens may stand in the flag position.
fn is_flag_position_token(kind: SyntaxKind, range: &Range<usize>) -> bool {
    match kind {
        SyntaxKind::DATE
        | SyntaxKind::STAR
        | SyntaxKind::PENDING_KW
        | SyntaxKind::FLAG
        | SyntaxKind::HASH
        | SyntaxKind::TXN_KW => true,
        SyntaxKind::CURRENCY => range.len() == 1,
        _ => false,
    }
}

/// The first defect in a transaction header's token sequence, if any.
///
/// `tokens` must be the header region only: from the first non-trivia token
/// up to but **not including** the terminating `NEWLINE`, which is what both
/// callers pass (red `header_tokens()` uses `take_while(!= NEWLINE)`, green
/// breaks on it). `NEWLINE` is still in the trivia set below so that feeding
/// one in cannot change the verdict, but no caller should. Ranges are in
/// whatever frame the caller is working in; they are echoed back untouched.
pub(super) fn first_header_defect<I>(tokens: I) -> Option<(HeaderDefect, Range<usize>)>
where
    I: IntoIterator<Item = (SyntaxKind, Range<usize>)>,
{
    let mut strings: usize = 0;
    let mut third_string: Option<Range<usize>> = None;
    let mut seen_tag_or_link = false;
    let mut seen_header_content = false;
    let mut seen_token = false;
    let mut flags: usize = 0;

    for (kind, range) in tokens {
        // A `%`, `#!` or `#+` after the header's first token is not a comment
        // in beancount: only `;` starts one mid-line, and these lex as a FLAG,
        // or a HASH and a flag, so they are a syntax error there (#2802). Ours
        // read them as a comment to the end of the line, so the rest of the
        // header vanished in silence. Report the one or two characters
        // beancount objects to. Before the first token they are leading
        // trivia (a comment line above the transaction), as before.
        if seen_token && matches!(kind, SyntaxKind::SHEBANG | SyntaxKind::EMACS_DIRECTIVE) {
            // (A mid-line `%` is a FLAG token, not a comment, so it never
            // reaches here.)
            let end = (range.start + 2).min(range.end);
            return Some((HeaderDefect::UnexpectedToken, range.start..end));
        }
        if is_header_trivia(kind) {
            continue;
        }
        seen_token = true;
        // One flag only, as in beancount (see `is_flag_position_token`).
        if kind != SyntaxKind::DATE && !seen_header_content && is_flag_position_token(kind, &range)
        {
            flags += 1;
            if flags > 1 {
                return Some((HeaderDefect::UnexpectedToken, range));
            }
            continue;
        }
        // beancount's `txn` is required: a header whose first string, tag or
        // link comes straight after the date has no flag, and fails there
        // (#2905). `parser::identify_directive` opens a transaction node on
        // any of the three after the date, so the postings stay inside it.
        if flags == 0
            && !seen_header_content
            && matches!(
                kind,
                SyntaxKind::STRING | SyntaxKind::TAG | SyntaxKind::LINK
            )
        {
            return Some((HeaderDefect::MissingFlag, range));
        }
        match kind {
            SyntaxKind::STRING => {
                if seen_tag_or_link {
                    return Some((HeaderDefect::StringAfterTagOrLink, range));
                }
                strings += 1;
                if strings == 3 {
                    third_string = Some(range);
                }
                seen_header_content = true;
            }
            SyntaxKind::TAG | SyntaxKind::LINK => {
                seen_tag_or_link = true;
                seen_header_content = true;
            }
            // Flag-position tokens are only valid BEFORE any string/tag/link.
            // That scoping is what catches #2008 case 4: in
            // `* "Dinner" A:*:B` the `A` lexes as a single-character
            // `CURRENCY` — a perfectly good flag token in the flag position,
            // and junk here.
            _ if !seen_header_content && is_flag_position_token(kind, &range) => {}
            _ => return Some((HeaderDefect::UnexpectedToken, range)),
        }
    }

    // Checked last: it is the one defect that cannot be known until the header
    // ends, and beancount likewise reports it from the builder rather than the
    // grammar.
    third_string.map(|r| (HeaderDefect::TooManyStrings(strings), r))
}

/// [`first_header_defect`], plus the one check that needs the source text: a
/// one-letter flag glued to what follows it ([`HeaderDefect::GluedLetterFlag`]).
/// `src` is the text the ranges index. Like the one-letter-currency rule in
/// `directive_header`, the end of the file counts as a separator, so that
/// formatting, which adds the final newline, stays idempotent.
pub(super) fn first_header_defect_in(
    tokens: Vec<(SyntaxKind, Range<usize>)>,
    src: &str,
) -> Option<(HeaderDefect, Range<usize>)> {
    let glued = tokens
        .iter()
        .filter(|(k, _)| !is_header_trivia(*k))
        .take_while(|(k, _)| !matches!(k, SyntaxKind::STRING | SyntaxKind::TAG | SyntaxKind::LINK))
        .find(|(k, r)| {
            *k == SyntaxKind::CURRENCY
                && r.len() == 1
                && !matches!(src.as_bytes().get(r.end), None | Some(b' ' | b'\t' | b'\n'))
        })
        .map(|(_, r)| (HeaderDefect::GluedLetterFlag, r.clone()));
    let first_invalid = tokens
        .iter()
        .find(|(k, _)| *k == SyntaxKind::ERROR_TOKEN)
        .map(|(_, r)| r.start);
    let grammar = first_header_defect(tokens);
    let defect = match (glued, grammar) {
        (Some(g), Some(d)) => Some(if g.1.start <= d.1.start { g } else { d }),
        (g, d) => g.or(d),
    }?;
    // An invalid token (`ERROR_TOKEN`) at or before the defect is the
    // header's first error, and the lexer reports it as its own: beancount's
    // grammar never sees that token, so it reports no syntax error for the
    // line on top of the `Invalid token`, and its builder does not run.
    if first_invalid.is_some_and(|at| at <= defect.1.start) {
        return None;
    }
    Some(defect)
}

/// Which header strings are the payee and the narration (#2932). Each index
/// is the string's place among the header's `STRING` tokens, counted from 0.
///
/// Computed by [`header_strings`], the one rule every reader of a header's
/// payee and narration uses: red `convert_transaction`, green
/// `convert_transaction_header`, and the typed `ast::Transaction::payee` /
/// `narration` accessors (which the formatter reads).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum HeaderStrings {
    /// No string: no payee, an empty narration.
    Empty,
    /// One string, the narration; no payee.
    Narration(usize),
    /// One string, the payee: the slot after it held an unexpected token, so
    /// the narration is empty.
    Payee(usize),
    /// Two strings, the payee and the narration.
    PayeeNarration(usize, usize),
    /// Three or more strings (beancount: `Too many strings`). The directive
    /// keeps the last as its narration with no payee; the typed accessors
    /// report neither. `last` is the index of the last string.
    TooMany {
        /// Index of the last string.
        last: usize,
    },
}

impl HeaderStrings {
    /// Index of the payee string, if there is one.
    pub(super) const fn payee(self) -> Option<usize> {
        match self {
            Self::Payee(p) | Self::PayeeNarration(p, _) => Some(p),
            Self::Empty | Self::Narration(_) | Self::TooMany { .. } => None,
        }
    }

    /// Index of the narration string, if there is one. `None` for three or
    /// more strings: the typed accessors call that ambiguous.
    pub(super) const fn narration(self) -> Option<usize> {
        match self {
            Self::Narration(n) | Self::PayeeNarration(_, n) => Some(n),
            Self::Empty | Self::Payee(_) | Self::TooMany { .. } => None,
        }
    }

    /// Index of the string the directive's narration comes from: as
    /// [`Self::narration`], except that three or more strings keep the last.
    pub(super) const fn directive_narration(self) -> Option<usize> {
        match self {
            Self::TooMany { last } => Some(last),
            other => other.narration(),
        }
    }
}

/// Assign a transaction header's strings to the payee and the narration
/// (#2932).
///
/// `tokens` is the header region, as for [`first_header_defect`]; the ranges
/// are read only for a one-letter `CURRENCY` flag's length, so any frame
/// works.
///
/// beancount assigns strings by count: one string is the narration, two are
/// the payee and the narration, more are an error. That reads only the
/// strings. rledger keeps a transaction whose header holds an unexpected
/// token (an invalid token, or a token the header grammar has no place for:
/// a number, a currency, an account, `~`, `@`, a second flag, ...), and
/// counting only the strings then moved a string to a different field:
/// `* "p" 123` and `* "p" <bad>` loaded with the narration `p`, though `p`
/// was written in the payee's place. beancount drops those transactions.
///
/// The rule, so that no string ever changes field:
///
/// - The string slots run from the flag to the first tag or link. A token in
///   them that is not trivia (see `is_header_trivia`, which keeps the
///   deprecated `|` and a comment out), the flag (the first flag token
///   before any string, as [`first_header_defect`] counts it), a date before
///   the first string (which [`first_header_defect`] accepts there too) or a
///   string is an *unexpected token*, and it holds the slot it sits in. A
///   mid-line `#!` or `#+` is one too (#2802). One after a tag or link is in
///   the tag position, not a string slot, and changes nothing.
/// - Two or more strings: the strings alone decide, as in beancount. Two
///   strings already name both fields, so an unexpected token between or
///   around them moves neither: `* <bad> "p" "n"` and `* "p" <bad> "n"` both
///   give payee `p`, narration `n`.
/// - One string: it is the payee only when an unexpected token follows it
///   and none comes before it. That token held the narration slot, now
///   empty: `* "p" <bad>` is payee `p`. With an unexpected token before the
///   string, that token held the payee slot and the string is the narration,
///   whatever follows: `* <bad> "n"` and `* <bad> "n" <bad>` are narration
///   `n`. Otherwise it is the narration, as in beancount. So a token written
///   after a string never moves that string into another field.
/// - No string: no payee, an empty narration.
///
/// An invalid token runs to the next blank, as in beancount's lexer, so a
/// string glued to one is part of it and no string at all: `* "p" <bad>"y"`
/// has the one string `p`, followed by an unexpected token, so payee `p` and
/// an empty narration; `y` survives in no field.
///
/// Only the fields are recovered here. The unexpected token is reported by
/// the lexer or by [`first_header_defect`] whatever this returns, so the
/// error count does not depend on it.
pub(super) fn header_strings<I>(tokens: I) -> HeaderStrings
where
    I: IntoIterator<Item = (SyntaxKind, Range<usize>)>,
{
    let mut strings: usize = 0;
    let mut seen_token = false;
    let mut seen_flag = false;
    let mut seen_tag_or_link = false;
    let mut unexpected_before_string = false;
    let mut unexpected_after_string = false;

    for (kind, range) in tokens {
        // A `#!` or `#+` after the first token is no comment (#2802), as in
        // `first_header_defect`; before it, it is leading trivia.
        let mid_line_comment =
            seen_token && matches!(kind, SyntaxKind::SHEBANG | SyntaxKind::EMACS_DIRECTIVE);
        if is_header_trivia(kind) && !mid_line_comment {
            continue;
        }
        seen_token = true;
        match kind {
            SyntaxKind::STRING => strings += 1,
            SyntaxKind::TAG | SyntaxKind::LINK => seen_tag_or_link = true,
            _ if seen_tag_or_link => {}
            // The date, and any further date before the first string, which
            // `first_header_defect` accepts in the flag position too.
            SyntaxKind::DATE if strings == 0 => {}
            k if k != SyntaxKind::DATE
                && strings == 0
                && !seen_flag
                && is_flag_position_token(k, &range) =>
            {
                seen_flag = true;
            }
            _ if strings == 0 => unexpected_before_string = true,
            _ => unexpected_after_string = true,
        }
    }

    match strings {
        0 => HeaderStrings::Empty,
        1 if unexpected_after_string && !unexpected_before_string => HeaderStrings::Payee(0),
        1 => HeaderStrings::Narration(0),
        2 => HeaderStrings::PayeeNarration(0, 1),
        n => HeaderStrings::TooMany { last: n - 1 },
    }
}

/// Diagnostic text for a defect. `text` is the source slice of the reported
/// range — the caller has the source, this module does not.
///
/// Built here rather than at each call site so the two walkers cannot report
/// the same defect with different words.
pub(super) fn defect_message(defect: HeaderDefect, text: &str) -> String {
    match defect {
        HeaderDefect::StringAfterTagOrLink => format!(
            "unexpected string {text} after a tag or link: \
             payee and narration must come before any #tag or ^link"
        ),
        HeaderDefect::TooManyStrings(n) => format!(
            "too many strings on transaction description: found {n}, \
             expected at most 2 (payee and narration)"
        ),
        HeaderDefect::UnexpectedToken => {
            format!("unexpected {text:?} in transaction header")
        }
        HeaderDefect::GluedLetterFlag => format!(
            "unexpected {text:?} in transaction header: a one-letter flag must be \
             followed by a space, as beancount reads it"
        ),
        HeaderDefect::MissingFlag => format!(
            "unexpected {text:?} in transaction header: a transaction needs a flag \
             (`*` or `!`) or `txn` after the date"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a token stream with plausible ranges so `CURRENCY` length —
    /// the one place the rule reads a range — is exercised for real.
    fn toks(items: &[(SyntaxKind, &str)]) -> Vec<(SyntaxKind, Range<usize>)> {
        let mut at = 0usize;
        items
            .iter()
            .map(|(k, t)| {
                let r = at..at + t.len();
                at = r.end;
                (*k, r)
            })
            .collect()
    }

    const WS: (SyntaxKind, &str) = (SyntaxKind::WHITESPACE, " ");

    #[test]
    fn accepts_the_canonical_shapes() {
        // date + flag + payee + narration + tag + link
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2014-04-20"),
                WS,
                (SyntaxKind::STAR, "*"),
                WS,
                (SyntaxKind::STRING, "\"payee\""),
                WS,
                (SyntaxKind::STRING, "\"narration\""),
                WS,
                (SyntaxKind::TAG, "#trip"),
                WS,
                (SyntaxKind::LINK, "^abc"),
            ])),
            None
        );
        // `txn` + narration
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2014-04-20"),
                WS,
                (SyntaxKind::TXN_KW, "txn"),
                WS,
                (SyntaxKind::STRING, "\"n\""),
            ])),
            None
        );
        // no strings at all
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2014-01-01"),
                WS,
                (SyntaxKind::STAR, "*")
            ])),
            None
        );
        // trailing comment
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2014-01-01"),
                WS,
                (SyntaxKind::STAR, "*"),
                WS,
                (SyntaxKind::COMMENT, "; note"),
            ])),
            None
        );
    }

    /// `2012-12-17 P "Payee" "Narration"` is real corpus content
    /// (`fava/tests_data_example.beancount`) — a single-letter ticker flag.
    #[test]
    fn accepts_single_char_currency_as_a_flag_but_not_elsewhere() {
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2012-12-17"),
                WS,
                (SyntaxKind::CURRENCY, "P"),
                WS,
                (SyntaxKind::STRING, "\"Payee\""),
                WS,
                (SyntaxKind::STRING, "\"Narration\""),
            ])),
            None
        );
        // The same token AFTER a string is junk, not a flag.
        assert!(matches!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2013-05-02"),
                WS,
                (SyntaxKind::STAR, "*"),
                WS,
                (SyntaxKind::STRING, "\"Dinner\""),
                WS,
                (SyntaxKind::CURRENCY, "A"),
            ])),
            Some((HeaderDefect::UnexpectedToken, _))
        ));
        // A multi-character CURRENCY is not a flag even in the flag position.
        assert!(matches!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2013-05-02"),
                WS,
                (SyntaxKind::CURRENCY, "USD"),
            ])),
            Some((HeaderDefect::UnexpectedToken, _))
        ));
    }

    /// #2905: beancount's `txn` is required, so a string, tag or link straight
    /// after the date is a syntax error there, reported at that token.
    #[test]
    fn rejects_a_header_with_no_flag() {
        for first in [
            (SyntaxKind::STRING, "\"x\""),
            (SyntaxKind::TAG, "#t"),
            (SyntaxKind::LINK, "^l"),
        ] {
            let stream = toks(&[
                (SyntaxKind::DATE, "2024-01-02"),
                WS,
                first,
                WS,
                (SyntaxKind::STRING, "\"y\""),
            ]);
            let at = stream[2].1.clone();
            assert_eq!(
                first_header_defect(stream),
                Some((HeaderDefect::MissingFlag, at)),
                "{first:?}"
            );
        }
    }

    /// #2008 case 3.
    #[test]
    fn rejects_a_string_after_a_tag() {
        let got = first_header_defect(toks(&[
            (SyntaxKind::DATE, "2014-04-20"),
            WS,
            (SyntaxKind::STAR, "*"),
            WS,
            (SyntaxKind::TAG, "#trip"),
            WS,
            (SyntaxKind::STRING, "\"Money from CC\""),
            WS,
            (SyntaxKind::LINK, "^610fa7f17e7a"),
        ]));
        let (defect, range) = got.expect("string after tag must be reported");
        assert_eq!(defect, HeaderDefect::StringAfterTagOrLink);
        // Reported AT the offending string, not at the transaction.
        assert_eq!(range.len(), "\"Money from CC\"".len());
    }

    /// #2008 cases 6 and 7.
    #[test]
    fn rejects_more_than_two_strings() {
        let three = toks(&[
            (SyntaxKind::DATE, "2013-05-18"),
            WS,
            (SyntaxKind::STAR, "*"),
            WS,
            (SyntaxKind::STRING, "\"A\""),
            WS,
            (SyntaxKind::STRING, "\"B\""),
            WS,
            (SyntaxKind::STRING, "\"C\""),
        ]);
        assert_eq!(
            first_header_defect(three.clone()).map(|(d, _)| d),
            Some(HeaderDefect::TooManyStrings(3))
        );
        // Reported at the THIRD string — the first one that is too many.
        // Taken from the token list rather than hand-computed, so the
        // assertion stays true if the fixture above is edited.
        let third = three
            .iter()
            .filter(|(k, _)| *k == SyntaxKind::STRING)
            .nth(2)
            .expect("fixture has three strings")
            .1
            .clone();
        let (_, range) = first_header_defect(three).unwrap();
        assert_eq!(range, third);

        let mut five = vec![
            (SyntaxKind::DATE, "2013-05-18"),
            WS,
            (SyntaxKind::STAR, "*"),
        ];
        for _ in 0..5 {
            five.push(WS);
            five.push((SyntaxKind::STRING, "\"x\""));
        }
        assert_eq!(
            first_header_defect(toks(&five)).map(|(d, _)| d),
            Some(HeaderDefect::TooManyStrings(5))
        );
    }

    /// Exactly two strings is the canonical payee/narration form and must
    /// stay clean — the off-by-one that would break every real ledger.
    #[test]
    fn two_strings_is_not_too_many() {
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2013-05-18"),
                WS,
                (SyntaxKind::STAR, "*"),
                WS,
                (SyntaxKind::STRING, "\"A\""),
                WS,
                (SyntaxKind::STRING, "\"B\""),
            ])),
            None
        );
    }

    /// The `|` separator keeps its own recoverable diagnostic.
    #[test]
    fn ignores_the_deprecated_pipe() {
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2013-05-18"),
                WS,
                (SyntaxKind::STAR, "*"),
                WS,
                (SyntaxKind::STRING, "\"payee\""),
                WS,
                (SyntaxKind::PIPE, "|"),
                WS,
                (SyntaxKind::STRING, "\"narration\""),
            ])),
            None
        );
    }

    /// #2932: the slot rule of [`header_strings`], over every shape it
    /// distinguishes. `s` is a string, `e` an unexpected token of the given
    /// kind, `t` a tag. The expected payee and narration are string indexes.
    #[test]
    fn test_header_strings_moves_no_string() {
        use HeaderStrings as H;
        let s = (SyntaxKind::STRING, "\"x\"");
        let bad = (SyntaxKind::ERROR_TOKEN, "\u{11}");
        let t = (SyntaxKind::TAG, "#t");
        let l = (SyntaxKind::LINK, "^l");
        let star = (SyntaxKind::STAR, "*");
        let date = (SyntaxKind::DATE, "2024-01-02");
        let cases: Vec<(Vec<(SyntaxKind, &str)>, HeaderStrings)> = vec![
            // Without an unexpected token: beancount's count rule.
            (vec![date, star], H::Empty),
            (vec![date, star, s], H::Narration(0)),
            (vec![date, (SyntaxKind::TXN_KW, "txn"), s], H::Narration(0)),
            (vec![date, (SyntaxKind::CURRENCY, "P"), s], H::Narration(0)),
            (vec![date, star, s, s], H::PayeeNarration(0, 1)),
            (vec![date, star, s, s, s, s], H::TooMany { last: 3 }),
            (vec![date, star, s, t, l], H::Narration(0)),
            // No flag (#2905): the strings are read the same.
            (vec![date, s, bad], H::Payee(0)),
            // Before the string: it held the payee slot.
            (vec![date, star, bad, s], H::Narration(0)),
            (
                vec![date, (SyntaxKind::FLAG, "!"), star, s],
                H::Narration(0),
            ),
            // After the string: the string keeps the payee slot.
            (vec![date, star, s, bad], H::Payee(0)),
            (vec![date, star, s, bad, t, l], H::Payee(0)),
            // Before AND after: the string stays the narration.
            (vec![date, star, bad, s, bad], H::Narration(0)),
            // Two strings decide whatever surrounds them.
            (vec![date, star, bad, s, s], H::PayeeNarration(0, 1)),
            (vec![date, star, s, bad, s], H::PayeeNarration(0, 1)),
            (vec![date, star, s, s, bad], H::PayeeNarration(0, 1)),
            // After a tag or link: no string slot.
            (vec![date, star, s, t, bad], H::Narration(0)),
            (
                vec![date, star, s, l, (SyntaxKind::NUMBER, "1")],
                H::Narration(0),
            ),
            // Trivia, the deprecated `|` and a comment hold no slot.
            (
                vec![date, star, s, (SyntaxKind::PIPE, "|")],
                H::Narration(0),
            ),
            (
                vec![date, star, s, (SyntaxKind::COMMENT, ";c")],
                H::Narration(0),
            ),
            // A mid-line `#!` is no comment (#2802): it holds the slot.
            (
                vec![date, star, s, (SyntaxKind::SHEBANG, "#!x")],
                H::Payee(0),
            ),
            // A date after the string holds its slot; before it, it is read
            // as `first_header_defect` reads it, in the flag position.
            (vec![date, star, s, date], H::Payee(0)),
            (vec![date, star, date, s, bad], H::Payee(0)),
            // Only unexpected tokens: nothing to place.
            (vec![date, star, bad], H::Empty),
        ];
        // Every kind the header grammar has no place for after a string.
        let junk = [
            (SyntaxKind::NUMBER, "123"),
            (SyntaxKind::CURRENCY, "USD"),
            (SyntaxKind::CURRENCY, "A"),
            (SyntaxKind::ACCOUNT, "Assets:A"),
            (SyntaxKind::TILDE, "~"),
            (SyntaxKind::AT, "@"),
            (SyntaxKind::L_BRACE, "{"),
            (SyntaxKind::L_PAREN, "("),
            (SyntaxKind::COMMA, ","),
            (SyntaxKind::COLON, ":"),
            (SyntaxKind::STAR, "*"),
            (SyntaxKind::PLUS, "+"),
            (SyntaxKind::BOOL_TRUE, "TRUE"),
            (SyntaxKind::META_KEY, "key:"),
            (SyntaxKind::OPEN_KW, "open"),
            (SyntaxKind::TXN_KW, "txn"),
            (SyntaxKind::HASH, "#"),
            (SyntaxKind::FLAG, "!"),
            (SyntaxKind::ERROR_TOKEN, "\u{11}"),
        ];
        let mut all = cases;
        for j in junk {
            all.push((vec![date, star, s, j], H::Payee(0)));
            all.push((vec![date, star, j, s], H::Narration(0)));
            all.push((vec![date, star, j, s, j], H::Narration(0)));
        }
        for (tokens, want) in all {
            let shape = format!("{tokens:?}");
            assert_eq!(header_strings(toks(&tokens)), want, "{shape}");
        }
    }

    /// Only the FIRST defect is reported: `A:*:B` lexes into five tokens that
    /// would each trip the rule.
    #[test]
    fn reports_only_the_first_defect() {
        let stream = toks(&[
            (SyntaxKind::DATE, "2013-05-02"),
            WS,
            (SyntaxKind::STAR, "*"),
            WS,
            (SyntaxKind::STRING, "\"Dinner\""),
            WS,
            (SyntaxKind::CURRENCY, "A"),
            (SyntaxKind::COLON, ":"),
            (SyntaxKind::STAR, "*"),
            (SyntaxKind::COLON, ":"),
            (SyntaxKind::CURRENCY, "B"),
        ]);
        // The `A` of `A:*:B` — the first offending token of five, each of
        // which would trip the rule on its own.
        let first_junk = stream[6].1.clone();
        let (defect, range) = first_header_defect(stream).expect("junk must be reported");
        assert_eq!(defect, HeaderDefect::UnexpectedToken);
        assert_eq!(range, first_junk);
    }
}
