//! Token-sequence validation for the header lines of the non-transaction
//! directives (#2802, stage 1) and for metadata lines (stage 2, see
//! [`first_meta_defect`]).
//!
//! Our CST parser groups a directive's header line into flat tokens and each
//! `convert_*` reads the fields it wants and ignores the rest, so a token with
//! no place in the directive was dropped in silence: `2024-01-01 open! Assets:A`
//! loaded clean here and is a syntax error in beancount, and `rledger format`
//! then deleted the `!`. Worse, `open Assets:A U*SD` loaded as the currency list
//! `U,SD`.
//!
//! This module re-imposes beancount's grammar on the header line, one small
//! recognizer per directive, taken from `beancount/parser/grammar.y` (3.2.3):
//!
//! ```text
//! open      : DATE OPEN account currency_list opt_booking eol
//! close     : DATE CLOSE account eol
//! commodity : DATE COMMODITY currency eol
//! pad       : DATE PAD account account eol
//! balance   : DATE BALANCE account amount_tolerance eol
//! price     : DATE PRICE currency amount eol
//! event     : DATE EVENT STRING STRING eol
//! query     : DATE QUERY STRING STRING eol
//! note      : DATE NOTE account STRING tags_links eol
//! document  : DATE DOCUMENT account filename tags_links eol
//! custom    : DATE CUSTOM STRING custom_value_list eol
//! option    : OPTION STRING STRING eol
//! include   : INCLUDE STRING eol
//! plugin    : PLUGIN STRING eol | PLUGIN STRING STRING eol
//! pushtag   : PUSHTAG TAG eol            poptag : POPTAG TAG eol
//! pushmeta  : PUSHMETA key_value eol     popmeta : POPMETA KEY COLON eol
//!
//! currency_list    : %empty | currency | currency_list COMMA currency
//! opt_booking      : STRING | %empty
//! amount           : number_expr currency
//! amount_tolerance : number_expr currency | number_expr TILDE number_expr currency
//! tags_links       : %empty | tags_links LINK | tags_links TAG
//! custom_value     : STRING | DATE | BOOL | amount | number_expr | account
//! key_value_value  : STRING | account | DATE | currency | TAG | BOOL | NONE
//!                  | number_expr | amount | %empty
//! number_expr      : NUMBER | number_expr (PLUS|MINUS|ASTERISK|SLASH) number_expr
//!                  | (MINUS|PLUS) number_expr | LPAREN number_expr RPAREN
//! ```
//!
//! Two consequences of following it exactly, both beancount's behavior:
//!
//! - `currency_list COMMA currency` reduces from `%empty`, so ONE leading
//!   comma is valid (`open Assets:A , USD,EUR`), and two are not.
//! - Only `;` starts a comment in the middle of a line. beancount lexes `%` as
//!   a `FLAG` token and `#!` / `#+` as `HASH` and a flag or `PLUS`, so all
//!   three are syntax errors mid-line; our lexer reads each as a comment that
//!   runs to the end of the line, which silently commented out the rest of the
//!   header (`open Assets:A % USD`). After the header's first token they are
//!   reported here as unexpected.
//!
//! # One rule, one walker
//!
//! The non-transaction converters are shared by the green and red paths (only
//! transactions have a green fast path), so this check runs from the shared
//! directive loop in `convert::parse_via_cst_inner` and needs no green
//! mirror. Transaction headers keep their own rule in [`super::txn_header`].
//!
//! Like that module, the check is over `(SyntaxKind, Range<usize>)` pairs and
//! reports only the first problem: beancount stops at the first syntax error
//! on a line, and `A:*:B`-style junk lexes into several tokens that would each
//! be unexpected.

use crate::SyntaxKind as K;
use std::ops::Range;

/// The first token of a header line that beancount's grammar does not accept.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HeaderDefect {
    /// The offending token; when the line ends before the grammar is
    /// satisfied, the last token on it.
    pub(super) range: Range<usize>,
    /// What the grammar would have accepted there, for the message.
    pub(super) expected: &'static str,
    /// The token's kind; `None` at the end of the line.
    pub(super) found: Option<K>,
}

/// The beancount keyword of a non-transaction directive node, or `None` for
/// any other kind (transactions included: they are checked elsewhere).
pub(super) const fn directive_keyword(kind: K) -> Option<&'static str> {
    Some(match kind {
        K::OPEN_DIRECTIVE => "open",
        K::CLOSE_DIRECTIVE => "close",
        K::COMMODITY_DIRECTIVE => "commodity",
        K::PAD_DIRECTIVE => "pad",
        K::BALANCE_DIRECTIVE => "balance",
        K::PRICE_DIRECTIVE => "price",
        K::EVENT_DIRECTIVE => "event",
        K::QUERY_DIRECTIVE => "query",
        K::NOTE_DIRECTIVE => "note",
        K::DOCUMENT_DIRECTIVE => "document",
        K::CUSTOM_DIRECTIVE => "custom",
        K::OPTION_DIRECTIVE => "option",
        K::INCLUDE_DIRECTIVE => "include",
        K::PLUGIN_DIRECTIVE => "plugin",
        K::PUSHTAG_DIRECTIVE => "pushtag",
        K::POPTAG_DIRECTIVE => "poptag",
        K::PUSHMETA_DIRECTIVE => "pushmeta",
        K::POPMETA_DIRECTIVE => "popmeta",
        _ => return None,
    })
}

type Step = Result<(), HeaderDefect>;

/// A cursor over the header's significant tokens.
struct Cursor<I: Iterator<Item = (K, Range<usize>)>> {
    tokens: std::iter::Peekable<I>,
    /// The last token consumed, where a defect at the end of the line points.
    /// It must be a real token inside the directive, not an empty range at its
    /// end: the error-tolerant formatter copies a directive verbatim only when
    /// an error OVERLAPS it, and an empty range at the end of a file overlaps
    /// nothing, so `pushtag` at EOF was rebuilt as `pushtag ` and then trimmed
    /// to `pushtag` on the next pass, which is not idempotent.
    last: Range<usize>,
}

impl<I: Iterator<Item = (K, Range<usize>)>> Cursor<I> {
    fn peek(&mut self) -> Option<K> {
        self.tokens.peek().map(|(k, _)| *k)
    }

    fn bump(&mut self) {
        if let Some((_, range)) = self.tokens.next() {
            self.last = range;
        }
    }

    fn defect(&mut self, expected: &'static str) -> HeaderDefect {
        match self.tokens.peek() {
            Some((kind, range)) => HeaderDefect {
                // A mid-line `%` / `#!` / `#+` token runs to the end of the
                // line; point at the one or two characters beancount objects to.
                range: match kind {
                    K::PERCENT_COMMENT => range.start..range.start + 1,
                    K::SHEBANG | K::EMACS_DIRECTIVE => range.start..range.start + 2,
                    _ => range.clone(),
                },
                expected,
                found: Some(*kind),
            },
            None => HeaderDefect {
                range: self.last.clone(),
                expected,
                found: None,
            },
        }
    }

    /// Consume one token of `kind`, or report what was found instead.
    fn expect(&mut self, kind: K, expected: &'static str) -> Step {
        if self.peek() == Some(kind) {
            self.bump();
            Ok(())
        } else {
            Err(self.defect(expected))
        }
    }

    /// Consume one token if it is `kind`.
    fn eat(&mut self, kind: K) -> bool {
        let hit = self.peek() == Some(kind);
        if hit {
            self.bump();
        }
        hit
    }

    /// The header must end here.
    fn finish(&mut self) -> Step {
        if self.peek().is_none() {
            Ok(())
        } else {
            Err(self.defect("the end of the line"))
        }
    }
}

const fn starts_number_expr(kind: Option<K>) -> bool {
    matches!(kind, Some(K::NUMBER | K::PLUS | K::MINUS | K::L_PAREN))
}

/// `number_expr`. The left-recursive binary rules and the prefix sign rules
/// accept exactly the strings `unary (op unary)*`, which is what this reads;
/// precedence decides the VALUE, never which strings parse.
fn number_expr<I: Iterator<Item = (K, Range<usize>)>>(c: &mut Cursor<I>) -> Step {
    unary(c)?;
    while matches!(c.peek(), Some(K::PLUS | K::MINUS | K::STAR | K::SLASH)) {
        c.bump();
        unary(c)?;
    }
    Ok(())
}

fn unary<I: Iterator<Item = (K, Range<usize>)>>(c: &mut Cursor<I>) -> Step {
    while matches!(c.peek(), Some(K::PLUS | K::MINUS)) {
        c.bump();
    }
    match c.peek() {
        Some(K::NUMBER) => {
            c.bump();
            Ok(())
        }
        Some(K::L_PAREN) => {
            c.bump();
            number_expr(c)?;
            c.expect(K::R_PAREN, "`)`")
        }
        _ => Err(c.defect("a number")),
    }
}

/// `tags_links`: any run of tags and links.
fn tags_links<I: Iterator<Item = (K, Range<usize>)>>(c: &mut Cursor<I>) {
    while matches!(c.peek(), Some(K::TAG | K::LINK)) {
        c.bump();
    }
}

/// `key_value_value`: what may follow a metadata key, on a metadata line or
/// after `pushmeta`.
fn key_value_value<I: Iterator<Item = (K, Range<usize>)>>(c: &mut Cursor<I>) -> Step {
    match c.peek() {
        Some(
            K::STRING
            | K::ACCOUNT
            | K::DATE
            | K::CURRENCY
            | K::TAG
            | K::BOOL_TRUE
            | K::BOOL_FALSE
            | K::NULL_KW,
        ) => c.bump(),
        k if starts_number_expr(k) => {
            number_expr(c)?;
            // `amount : number_expr currency`
            c.eat(K::CURRENCY);
        }
        // `%empty`
        _ => {}
    }
    Ok(())
}

/// The body of each directive's rule, after its `DATE` and keyword.
fn directive_body<I: Iterator<Item = (K, Range<usize>)>>(directive: K, c: &mut Cursor<I>) -> Step {
    match directive {
        K::OPEN_DIRECTIVE => {
            c.expect(K::ACCOUNT, "an account")?;
            // `currency_list`: from `%empty`, `currency_list COMMA currency`
            // allows one leading comma.
            if c.eat(K::COMMA) {
                c.expect(K::CURRENCY, "a currency")?;
            } else {
                c.eat(K::CURRENCY);
            }
            while c.eat(K::COMMA) {
                c.expect(K::CURRENCY, "a currency")?;
            }
            c.eat(K::STRING);
        }
        K::CLOSE_DIRECTIVE => c.expect(K::ACCOUNT, "an account")?,
        K::COMMODITY_DIRECTIVE => c.expect(K::CURRENCY, "a currency")?,
        K::PAD_DIRECTIVE => {
            c.expect(K::ACCOUNT, "an account")?;
            c.expect(K::ACCOUNT, "the source account")?;
        }
        K::BALANCE_DIRECTIVE => {
            c.expect(K::ACCOUNT, "an account")?;
            number_expr(c)?;
            if c.eat(K::TILDE) {
                number_expr(c)?;
            }
            c.expect(K::CURRENCY, "a currency")?;
        }
        K::PRICE_DIRECTIVE => {
            c.expect(K::CURRENCY, "a currency")?;
            number_expr(c)?;
            c.expect(K::CURRENCY, "a currency")?;
        }
        K::EVENT_DIRECTIVE | K::QUERY_DIRECTIVE | K::OPTION_DIRECTIVE => {
            c.expect(K::STRING, "a string")?;
            c.expect(K::STRING, "a string")?;
        }
        K::NOTE_DIRECTIVE | K::DOCUMENT_DIRECTIVE => {
            c.expect(K::ACCOUNT, "an account")?;
            c.expect(K::STRING, "a string")?;
            tags_links(c);
        }
        K::CUSTOM_DIRECTIVE => {
            c.expect(K::STRING, "a string")?;
            loop {
                match c.peek() {
                    None => break,
                    Some(K::STRING | K::DATE | K::BOOL_TRUE | K::BOOL_FALSE | K::ACCOUNT) => {
                        c.bump();
                    }
                    k if starts_number_expr(k) => {
                        number_expr(c)?;
                        // `amount : number_expr currency`
                        c.eat(K::CURRENCY);
                    }
                    _ => return Err(c.defect("a custom value")),
                }
            }
        }
        K::INCLUDE_DIRECTIVE => c.expect(K::STRING, "a string")?,
        K::PLUGIN_DIRECTIVE => {
            c.expect(K::STRING, "a string")?;
            c.eat(K::STRING);
        }
        K::PUSHTAG_DIRECTIVE | K::POPTAG_DIRECTIVE => c.expect(K::TAG, "a tag")?,
        K::PUSHMETA_DIRECTIVE => {
            // Our lexer folds beancount's `KEY COLON` into one `META_KEY`.
            c.expect(K::META_KEY, "a metadata key")?;
            key_value_value(c)?;
        }
        K::POPMETA_DIRECTIVE => c.expect(K::META_KEY, "a metadata key")?,
        _ => {}
    }
    c.finish()
}

/// Tokens skipped anywhere in the header.
///
/// `COMMENT` is `;` to the end of the line, so nothing significant follows it.
/// A `BOM` is reported as `BomInDirectiveBody` elsewhere; it must not be
/// reported twice.
const fn is_skipped(kind: K) -> bool {
    matches!(kind, K::WHITESPACE | K::COMMENT | K::BOM)
}

/// The first defect in a non-transaction directive's header line, if any.
///
/// `tokens` is the header region only: from the directive's first content
/// token (its `DATE`, or the keyword of an undated directive) up to but not
/// including the `NEWLINE` that ends the line. `end` is where that region
/// ends, used for a defect at the end of the line. `src` is the text the
/// ranges index (read only to tell a run of plain digits apart). Ranges are
/// echoed back in whatever frame the caller uses.
///
/// Returns `None` for a kind that [`directive_keyword`] does not name.
pub(super) fn first_header_defect(
    directive: K,
    tokens: &[(K, Range<usize>)],
    end: usize,
    src: &str,
) -> Option<HeaderDefect> {
    directive_keyword(directive)?;
    let mut c = Cursor {
        tokens: tokens
            .iter()
            .filter(|(k, _)| !is_skipped(*k))
            .cloned()
            .peekable(),
        last: end..end,
    };
    // The leading `DATE` and the keyword are what made the parser build this
    // node, so they are present; consume them without re-checking which.
    if c.peek() == Some(K::DATE) {
        c.bump();
    }
    c.bump();
    let grammar = directive_body(directive, &mut c).err();
    // On a tie the split date wins: it says why the token is unexpected.
    earliest([
        split_beancount_date(tokens, src),
        grammar,
        glued_one_letter_currency(tokens),
    ])
}

/// The defect that starts first on the line; on a tie, the first listed.
fn earliest<const N: usize>(defects: [Option<HeaderDefect>; N]) -> Option<HeaderDefect> {
    defects.into_iter().flatten().min_by_key(|d| d.range.start)
}

/// A one-letter currency with something other than whitespace right after it.
///
/// beancount lexes a lone capital letter as `CAPITAL` (its one-letter
/// currency) only when whitespace or a newline follows it (`[A-Z]/[ \t\n]` in
/// `lexer.l`); two or more letters are a `CURRENCY` wherever they end. So
/// `open Assets:A U,SD` is not a list of `U` and `SD` there but the invalid
/// token `U,SD`, while our lexer reads a `CURRENCY` `U`, a comma, and `SD`.
fn glued_one_letter_currency(tokens: &[(K, Range<usize>)]) -> Option<HeaderDefect> {
    tokens.windows(2).find_map(|pair| {
        let [(kind, range), (next, _)] = pair else {
            return None;
        };
        (*kind == K::CURRENCY && range.len() == 1 && *next != K::WHITESPACE).then(|| HeaderDefect {
            range: range.clone(),
            expected: "a space after a one-letter currency",
            found: Some(K::CURRENCY),
        })
    })
}

/// Text that beancount lexes as ONE date and our lexer splits (#2808).
///
/// beancount's `DATE` is `[0-9]{4,}[-/][0-9]+[-/][0-9]+`; ours is
/// `\d{4}[-/]\d{1,2}[-/]\d{1,2}`. Where they differ, our tokens are glued
/// together with no whitespace between them, in one of two shapes:
///
/// - a `DATE` with a `NUMBER` right after it, when the last field has more
///   than two digits: `2024-02-002`, `2024/02/002`, `2024-2-002` and
///   `2024-02-0002` lex as `DATE 2024-02-00` (or `2024-2-00`) then a number;
/// - `NUMBER`, `-` or `/`, `NUMBER`, `-` or `/`, `NUMBER`, the first two plain
///   digits and the first at least four of them, when the year has more than
///   four digits or the month more than two: `02024-02-02`, `20024-02-02` and
///   `2024-002-02` lex as the number expression `2024 - 002 - 02`.
///
/// The last number may run on past the digits (`2024-002-02.5`,
/// `2024-002-02,000`, `2024-02-002.`): beancount's `DATE` takes the leading
/// digits and then reports what follows, and read our way the run is
/// arithmetic again (2019.5, 22). The first two must be plain digits, since
/// `2024.5-02-02` and `2024-0.5-02` are arithmetic in beancount too.
///
/// Read our way, either shape loads as a wrong value with no error where a
/// value may be a number (a metadata value, a `custom` value, a `pushmeta`
/// value, an amount): `kk: 2024-002-02` was the integer 2020, `kk: 2024-02-002`
/// the integer 2, `custom "x" 2024-02-002` just the number 2 (the invalid
/// date `2024-02-00` is dropped, #2811). beancount reads a date (or rejects
/// an invalid one, `20024-02-02`), so the text is reported. That is stricter
/// than beancount where its date is valid, and deliberately so: the
/// alternative is a silently wrong value. The fix that matches beancount is
/// in the lexer (#2808).
fn split_beancount_date(tokens: &[(K, Range<usize>)], src: &str) -> Option<HeaderDefect> {
    let digits = |r: &Range<usize>| {
        src.get(r.clone())
            .is_some_and(|t| !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit()))
    };
    let glued = |pair: &[(K, Range<usize>)]| pair[0].1.end == pair[1].1.start;
    let defect = |from: usize, to: usize| HeaderDefect {
        range: from..to,
        expected: "YYYY-MM-DD if this is a date: beancount reads it as one \
                   date, which rledger does not support yet (#2808)",
        found: Some(K::NUMBER),
    };
    for (i, (kind, range)) in tokens.iter().enumerate() {
        match kind {
            K::DATE => {
                if let Some(next) = tokens.get(i + 1)
                    && next.0 == K::NUMBER
                    && glued(&tokens[i..i + 2])
                {
                    return Some(defect(range.start, next.1.end));
                }
            }
            K::NUMBER => {
                let Some(run) = tokens.get(i..i + 5) else {
                    continue;
                };
                let shape = run[0].1.len() >= 4
                    && matches!(run[1].0, K::MINUS | K::SLASH)
                    && run[2].0 == K::NUMBER
                    && matches!(run[3].0, K::MINUS | K::SLASH)
                    && run[4].0 == K::NUMBER
                    && run.windows(2).all(glued)
                    && digits(&run[0].1)
                    && digits(&run[2].1);
                if shape {
                    return Some(defect(range.start, run[4].1.end));
                }
            }
            _ => {}
        }
    }
    None
}

/// The first defect in a metadata line (`key: value` under a directive, a
/// transaction or a posting; stage 2 of #2802), if any. beancount's rule is
/// `key_value_line : INDENT key_value eol` with `key_value : KEY COLON
/// key_value_value`, the same `key_value` that follows `pushmeta`.
///
/// `tokens` is the line from its `META_KEY` up to but not including the
/// `NEWLINE`; `end` is where it ends; `src` is the text the ranges index.
/// Ranges are echoed back in the caller's frame.
///
/// Stricter than beancount in two places, deliberately, both because our
/// lexer splits a token beancount reads whole and the pieces used to load as
/// a wrong value with no error:
///
/// - a date beancount's `DATE` takes and ours does not
///   ([`split_beancount_date`]): `kk: 2024-02-002` loaded as the integer 2,
///   `kk: 2024-002-02` as 2020. Fixed properly in the lexer by #2808.
/// - a number with doubled thousands separators: beancount's `NUMBER` is
///   `[0-9][0-9,]+[0-9]`, so `kk: 1,,000` is 1000 there, and ours lexes `1`,
///   `,`, `,`, `000`, which loaded as the integer 1. The stray comma is
///   reported here by the grammar; a posting amount (`1,,000 USD`) and a
///   header amount (`balance Assets:A 1,,000 USD`) already reported it.
///
/// Pinned by `test_parse_reports_a_split_beancount_date_instead_of_misreading_it`
/// and `test_parse_reports_doubled_thousands_separators_instead_of_misreading_them`.
pub(super) fn first_meta_defect(
    tokens: &[(K, Range<usize>)],
    end: usize,
    src: &str,
) -> Option<HeaderDefect> {
    let mut c = Cursor {
        tokens: tokens
            .iter()
            .filter(|(k, _)| !is_skipped(*k))
            .cloned()
            .peekable(),
        last: end..end,
    };
    let grammar = c
        .expect(K::META_KEY, "a metadata key")
        .and_then(|()| key_value_value(&mut c))
        .and_then(|()| c.finish())
        .err();
    // On a tie the split date wins: it says why the token is unexpected.
    earliest([
        split_beancount_date(tokens, src),
        grammar,
        glued_one_letter_currency(tokens),
    ])
}

/// Diagnostic text for a defect. `place` names where it is (`"the open
/// directive"`, `"a metadata line"`); `text` is the source slice of the
/// reported range: the caller has the source, this module does not.
pub(super) fn defect_message(place: &str, defect: &HeaderDefect, text: &str) -> String {
    let expected = defect.expected;
    match defect.found {
        None => format!("unexpected end of line in {place}: expected {expected}"),
        Some(K::PERCENT_COMMENT | K::SHEBANG | K::EMACS_DIRECTIVE) => format!(
            "unexpected {text:?} in {place}: expected {expected}. \
             Only `;` starts a comment in the middle of a line; `{text}` starts one \
             only at the beginning of a line"
        ),
        Some(_) => format!("unexpected {text:?} in {place}: expected {expected}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lex `line` with the real lexer and run the rule over its tokens, the
    /// way the converter does.
    fn defect(line: &str) -> Option<(HeaderDefect, String)> {
        let root = crate::cst::parse_structured(line);
        let node = root.children().next().expect("one directive node");
        let mut tokens = Vec::new();
        let mut end = line.len();
        for el in node.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                break;
            };
            let r = usize::from(t.text_range().start())..usize::from(t.text_range().end());
            if t.kind() == K::NEWLINE {
                end = r.start;
                break;
            }
            tokens.push((t.kind(), r));
        }
        first_header_defect(node.kind(), &tokens, end, line).map(|d| {
            let text = line[d.range.clone()].to_string();
            (d, text)
        })
    }

    #[test]
    fn test_first_header_defect_accepts_every_directive_shape() {
        for line in [
            "2024-01-01 open Assets:A\n",
            "2024-01-01 open Assets:A USD\n",
            "2024-01-01 open Assets:A USD,EUR \"FIFO\"\n",
            "2024-01-01 open Assets:A , USD,EUR\n",
            "2024-01-01 open Assets:A \"FIFO\"\n",
            "2024-01-01 open Assets:A USD ; a comment\n",
            "2024-01-01 close Assets:A\n",
            "2024-01-01 commodity USD\n",
            "2024-01-01 pad Assets:A Equity:B\n",
            "2024-01-01 balance Assets:A 1.00 USD\n",
            "2024-01-01 balance Assets:A 1.00 ~ 0.01 USD\n",
            "2024-01-01 balance Assets:A (1 + 2) * -3 / 4 USD\n",
            "2024-01-01 balance Assets:A - - 1 USD\n",
            "2024-01-01 balance Assets:A 1.*00 USD\n",
            "2024-01-01 price HOOL 1 + 2 USD\n",
            "2024-01-01 event \"e\" \"v\"\n",
            "2024-01-01 query \"q\" \"SELECT 1\"\n",
            "2024-01-01 note Assets:A \"n\" #t ^l #u\n",
            "2024-01-01 document Assets:A \"p.pdf\"\n",
            "2024-01-01 custom \"b\"\n",
            "2024-01-01 custom \"b\" Assets:A \"x\" 10 USD TRUE 2024-01-02 -1 (2)\n",
            "option \"title\" \"T\"\n",
            "include \"x.beancount\"\n",
            "plugin \"p\"\n",
            "plugin \"p\" \"c\"\n",
            "pushtag #t\n",
            "poptag #t\n",
            "pushmeta kk: 1\n",
            "pushmeta kk: 1 USD\n",
            "pushmeta kk: NULL\n",
            "pushmeta kk:\n",
            "2024-01-01 open Assets:A V\n",
            "2024-01-01 open Assets:A USD,V\n",
            "2024-01-01 price V 1 USD\n",
            "popmeta kk:\n",
        ] {
            assert_eq!(defect(line), None, "{line:?}");
        }
    }

    #[test]
    fn test_first_header_defect_reports_the_first_stray_token() {
        for (line, at, found_end) in [
            ("2024-01-01 open! Assets:A\n", "!", false),
            ("2024-01-01 open Assets:A USD @\n", "@", false),
            ("2024-01-01 open Assets:A U*SD\n", "U", false),
            ("2024-01-01 open Assets:A ,,USD\n", ",", false),
            ("2024-01-01 open Assets:A USD,\n", ",", true),
            ("2024-01-01 price HOOL ? 10 USD\n", "?", false),
            ("2024-01-01 close! Assets:A\n", "!", false),
            ("2024-01-01 balance Assets:A 1 ~ USD\n", "USD", false),
            ("2024-01-01 custom \"b\" NULL\n", "NULL", false),
            ("2024-01-01 custom \"b\" USD\n", "USD", false),
            ("2024-01-01 event \"e\"\n", "\"e\"", true),
            ("plugin \"a\" \"b\" \"c\"\n", "\"c\"", false),
            ("pushtag #a #b\n", "#b", false),
            ("popmeta kk: 1\n", "1", false),
            ("2024-01-01 open Assets:A U,SD\n", "U", false),
            ("2024-01-01 open Assets:A V, USD\n", "V", false),
            ("2024-01-01 open Assets:A USD,E,UR\n", "E", false),
        ] {
            let (d, text) = defect(line).unwrap_or_else(|| panic!("{line:?} must be rejected"));
            assert_eq!(text, at, "{line:?}");
            assert_eq!(d.found.is_none(), found_end, "{line:?}");
        }
    }

    /// Only `;` is a comment mid-line; `%`, `#!` and `#+` are flags there.
    #[test]
    fn test_first_header_defect_rejects_a_mid_line_non_semicolon_comment() {
        for line in [
            "2024-01-01 open Assets:A % USD\n",
            "2024-01-01 open Assets:A #!x\n",
            "2024-01-01 open Assets:A #+x\n",
        ] {
            let (d, _) = defect(line).unwrap_or_else(|| panic!("{line:?} must be rejected"));
            let msg = defect_message("the open directive", &d, &line[d.range.clone()]);
            assert!(msg.contains("Only `;` starts a comment"), "{msg}");
        }
    }

    #[test]
    fn test_first_header_defect_ignores_transactions() {
        assert_eq!(first_header_defect(K::TRANSACTION, &[], 0, ""), None);
    }
}
