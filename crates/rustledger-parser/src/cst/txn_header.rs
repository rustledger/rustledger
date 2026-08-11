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
//! CLAUDE.md, the green/red parser mirrors are a known drift source; a rule
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
/// Deliberately does NOT enforce *at most one* flag: `2014-01-01 * * "x"` is
/// rejected by beancount but is outside #2008's seven cases, and widening a
/// parser rejection beyond its evidence is how a compatibility fix starts
/// breaking real files.
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

    for (kind, range) in tokens {
        if is_header_trivia(kind) {
            continue;
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
        // bare date + narration (flag implied)
        assert_eq!(
            first_header_defect(toks(&[
                (SyntaxKind::DATE, "2014-04-20"),
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
