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
///
/// The header's own `DATE` is not one of them: [`first_header_defect`] skips
/// the header's first token when it is the date, and any later `DATE` is an
/// unexpected token, as in beancount (#2951).
fn is_flag_position_token(kind: SyntaxKind, range: &Range<usize>) -> bool {
    match kind {
        SyntaxKind::STAR
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
    let mut flags: usize = 0;
    let mut seen_first = false;

    for (kind, range) in tokens {
        // A `%`, `#!` or `#+` after the header's first token is not a comment
        // in beancount: only `;` starts one mid-line. The lexer reads them as
        // beancount does there (a FLAG, or a HASH and the token after it:
        // #2802, #2928), so they are reported below like any other token the
        // header has no place for; a comment token is a column-0 line only.
        if is_header_trivia(kind) {
            continue;
        }
        // The header's first token is its date. A second date anywhere in
        // the header (`2024-01-02 * 2024-01-03 "n"`) has no place in it:
        // beancount reports `syntax error, unexpected DATE` there, so it
        // falls through to `UnexpectedToken` below (#2951).
        if !seen_first {
            seen_first = true;
            if kind == SyntaxKind::DATE {
                continue;
            }
        }
        // One flag only, as in beancount (see `is_flag_position_token`).
        // Flag-position tokens are only valid BEFORE any string, tag or
        // link. That scoping is what catches #2008 case 4: in
        // `* "Dinner" A:*:B` the `A` lexes as a single-character `CURRENCY`,
        // a good flag token in the flag position and junk after the string.
        if !seen_header_content && is_flag_position_token(kind, &range) {
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
    /// One string, the payee: an invalid token after it stands where the
    /// narration was written, so the narration is empty.
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
/// `kinds` are the kinds of the header region's tokens, in source order, as
/// for [`first_header_defect`].
///
/// beancount assigns strings by count: one string is the narration, two are
/// the payee and the narration, more are an error. rledger keeps a
/// transaction whose header holds an invalid token (`ERROR_TOKEN`, which
/// beancount drops), and an invalid token can hide a string: it runs to the
/// next blank, as in beancount's lexer, so `<bad>"y"` is one token and `"y"`
/// no string. Counting only the strings that survived then moved one to a
/// different field: `* "p" <bad>"y"` loaded with the narration `p`, though
/// `p` was written in the payee's place.
///
/// The rule, so that no string ever changes field:
///
/// - Only an invalid token holds a string slot, because only an invalid
///   token can have swallowed a string. A number, a currency, an account, a
///   date, a second flag or a mid-line `#!` cannot hold a quoted string, so
///   nothing was displaced and the count rule stands: `* "Coffee" 5.00 USD`
///   (a forgotten newline) keeps the narration `Coffee`, as beancount's
///   count would read it. A mid-line BOM lexes as an invalid token, and so
///   holds a slot.
/// - The string slots end at the first tag or link. An invalid token after
///   one is in the tag position, not a string slot, and changes nothing.
/// - Two or more strings: the strings alone decide, as in beancount. Two
///   strings already name both fields, so an invalid token between or around
///   them moves neither: `* <bad> "p" "n"` and `* "p" <bad> "n"` both give
///   payee `p`, narration `n`.
/// - One string: it is the payee only when it stands straight after the
///   flag (nothing but the date and the flag before it) and an invalid token
///   follows it. That token stands where the narration was written, now
///   empty: `* "p" <bad>"y"` is payee `p`, and `y` survives in no field.
///   Anything else before the string, an invalid token or any other token
///   (`* <bad> "n" <bad>`, `* 123 "n" <bad>`, `* 2024-01-03 "n" <bad>`),
///   leaves the string where the count rule puts it, the narration: the
///   header no longer shows which place it was written in. So a token
///   written after a string never moves that string into another field, and
///   the count rule gives way only where the one string is plainly the
///   first of two.
/// - No string: no payee, an empty narration.
///
/// The flag is the first token after the date that is not a string, a tag, a
/// link or an invalid token: a transaction node only opens on a flag token,
/// a string, a tag or a link (`parser::identify_directive`), so no range is
/// needed to tell it apart. A later date is an ordinary token.
///
/// Only the fields are recovered here. The invalid token is reported by the
/// lexer whatever this returns, so the error count does not depend on it.
pub(super) fn header_strings<I>(kinds: I) -> HeaderStrings
where
    I: IntoIterator<Item = SyntaxKind>,
{
    let mut strings: usize = 0;
    let mut seen_date = false;
    let mut seen_flag = false;
    let mut seen_tag_or_link = false;
    let mut other_before_string = false;
    let mut invalid_after_string = false;

    for kind in kinds {
        if is_header_trivia(kind) {
            continue;
        }
        match kind {
            SyntaxKind::STRING => strings += 1,
            SyntaxKind::TAG | SyntaxKind::LINK => seen_tag_or_link = true,
            // The tag position: no string slot.
            _ if seen_tag_or_link => {}
            SyntaxKind::ERROR_TOKEN if strings > 0 => invalid_after_string = true,
            // Only an invalid token holds a slot after the string.
            _ if strings > 0 => {}
            SyntaxKind::DATE if !seen_date => seen_date = true,
            k if !seen_flag && k != SyntaxKind::ERROR_TOKEN => seen_flag = true,
            // Before the string: an invalid token, a second flag, a later
            // date, a number, ...
            _ => other_before_string = true,
        }
    }

    match strings {
        0 => HeaderStrings::Empty,
        1 if invalid_after_string && !other_before_string => HeaderStrings::Payee(0),
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

    /// #2951: only the header's first token may be a date. A second one, in
    /// the flag position or after a string, tag or link, is an unexpected
    /// token, reported at that date.
    #[test]
    fn rejects_a_second_date() {
        let (date, star, s, t) = (
            (SyntaxKind::DATE, "2024-01-03"),
            (SyntaxKind::STAR, "*"),
            (SyntaxKind::STRING, "\"n\""),
            (SyntaxKind::TAG, "#t"),
        );
        for rest in [
            vec![star, WS, date, WS, s],
            vec![star, WS, date],
            vec![star, WS, date, WS, star, WS, s],
            vec![star, WS, s, WS, date],
            vec![star, WS, s, WS, t, WS, date],
        ] {
            let mut items = vec![(SyntaxKind::DATE, "2024-01-02"), WS];
            items.extend(rest);
            let stream = toks(&items);
            let at = stream
                .iter()
                .skip(1)
                .find(|(k, _)| *k == SyntaxKind::DATE)
                .expect("fixture has a second date")
                .1
                .clone();
            assert_eq!(
                first_header_defect(stream),
                Some((HeaderDefect::UnexpectedToken, at)),
                "{items:?}"
            );
        }
        // The header's own date alone is no defect.
        assert_eq!(
            first_header_defect(toks(&[(SyntaxKind::DATE, "2024-01-02"), WS, star, WS, s])),
            None
        );
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
    /// distinguishes. `s` is a string, `bad` an invalid token, `t` a tag.
    #[test]
    fn test_header_strings_moves_no_string() {
        use HeaderStrings as H;
        use SyntaxKind as K;
        let (s, bad, t, l) = (K::STRING, K::ERROR_TOKEN, K::TAG, K::LINK);
        let (star, date, ws) = (K::STAR, K::DATE, K::WHITESPACE);
        let cases: Vec<(Vec<SyntaxKind>, HeaderStrings)> = vec![
            // Without an invalid token: beancount's count rule.
            (vec![date, star], H::Empty),
            (vec![date, star, ws, s], H::Narration(0)),
            (vec![date, K::TXN_KW, s], H::Narration(0)),
            (vec![date, star, s, s], H::PayeeNarration(0, 1)),
            (vec![date, star, s, s, s, s], H::TooMany { last: 3 }),
            (vec![date, star, s, t, l], H::Narration(0)),
            // No flag (#2905): the strings are read the same.
            (vec![date, s, bad], H::Payee(0)),
            // No flag, an invalid token first: it is never the flag, so it
            // stands before the string and the count rule stands.
            (vec![date, bad, s, bad], H::Narration(0)),
            // Before the string: it stands in the payee's place.
            (vec![date, star, bad, s], H::Narration(0)),
            // After the string: the string keeps the payee's place.
            (vec![date, star, s, ws, bad], H::Payee(0)),
            (vec![date, star, s, bad, t, l], H::Payee(0)),
            // Before AND after: the string stays the narration.
            (vec![date, star, bad, s, bad], H::Narration(0)),
            // Two strings decide whatever surrounds them.
            (vec![date, star, bad, s, s], H::PayeeNarration(0, 1)),
            (vec![date, star, s, bad, s], H::PayeeNarration(0, 1)),
            (vec![date, star, s, s, bad], H::PayeeNarration(0, 1)),
            // After a tag or link: no string slot.
            (vec![date, star, s, t, bad], H::Narration(0)),
            (vec![date, star, s, l, bad], H::Narration(0)),
            // A later date before the first string is an ordinary token, so
            // the string is not plainly the payee: the count rule stands.
            (vec![date, star, date, s, bad], H::Narration(0)),
            // A one-letter flag, `txn`, or no flag at all.
            (vec![date, K::CURRENCY, s, bad], H::Payee(0)),
            (vec![date, K::TXN_KW, s, bad], H::Payee(0)),
            // Only invalid tokens: nothing to place.
            (vec![date, star, bad], H::Empty),
        ];
        // Every other kind the header grammar has no place for cannot hold a
        // quoted string, so it holds no slot: the count rule stands.
        let other = [
            K::NUMBER,
            K::CURRENCY,
            K::ACCOUNT,
            K::TILDE,
            K::AT,
            K::L_BRACE,
            K::L_PAREN,
            K::COMMA,
            K::COLON,
            K::STAR,
            K::PLUS,
            K::DATE,
            K::BOOL_TRUE,
            K::META_KEY,
            K::OPEN_KW,
            K::TXN_KW,
            K::HASH,
            K::FLAG,
        ];
        let mut all = cases;
        for o in other {
            all.push((vec![date, star, s, o], H::Narration(0)));
            all.push((vec![date, star, o, s], H::Narration(0)));
            all.push((vec![date, star, o, s, o], H::Narration(0)));
            // After the string, beside an invalid token, it changes nothing.
            all.push((vec![date, star, s, o, bad], H::Payee(0)));
            // Before the string, the header no longer shows the string's
            // place, so the count rule stands.
            all.push((vec![date, star, o, s, bad], H::Narration(0)));
        }
        // Trivia holds no slot and hides no place. (A `SHEBANG` token is a
        // column-0 line only, #2928, so none is in a header in real input.)
        for o in [K::WHITESPACE, K::PIPE, K::COMMENT, K::BOM, K::SHEBANG] {
            all.push((vec![date, star, s, o], H::Narration(0)));
            all.push((vec![date, star, o, s, o, bad], H::Payee(0)));
        }
        for (kinds, want) in all {
            let shape = format!("{kinds:?}");
            assert_eq!(header_strings(kinds), want, "{shape}");
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
