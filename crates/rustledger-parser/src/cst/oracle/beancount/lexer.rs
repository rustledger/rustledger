//! beancount 3.2.3's tokenization, as the reference oracle needs it.
//!
//! Provenance: written from pta-standards' clean-room, MIT-licensed lexical
//! specification (`formats/beancount/v3/grammar/LEXICAL.md` and its executable
//! form `harness/reflexer.py`, rustledger/pta-standards@1463db773ac5), which was
//! itself derived from black-box experiments on beancount. Nothing here comes
//! from beancount's `lexer.l` or from rustledger's earlier port of it.
//!
//! The matching discipline is flex's, as `LEXICAL.md` states it: at each
//! position every active rule is tried (rules marked BOL only at the start of
//! a line), the longest match wins, counting a rule's trailing context but not
//! consuming it, and ties go to the rule listed first. A rule whose post-check
//! fails yields its text as an error token; where no rule matches, an invalid
//! run up to the next space, tab, CR or LF is one error token.
//!
//! Each candidate below carries its rule number from `LEXICAL.md`'s table,
//! which is the tie-break order. Only the rules that can match at the current
//! byte are tried, so lexing is one pass over the input.

use super::tables::Tok;

/// One token of beancount's lexer: its grammar terminal ([`Tok::Error`] for a
/// lexer error, which beancount's lexer returns as bison's `YYerror`), its byte
/// range, and the line beancount reports it on (the line it ENDS on, 1-based:
/// an `EOL` carries the number of the line after it).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Lexeme {
    pub tok: Tok,
    pub start: u32,
    pub end: u32,
    pub line: u32,
}

/// `LEXICAL.md`'s rule numbers, in priority order: an earlier rule wins a tie.
mod rule {
    pub(super) const INDENT: u8 = 1;
    pub(super) const IGNORED_MARKER_LINE: u8 = 2;
    pub(super) const IGNORED_HASH_LINE: u8 = 3;
    pub(super) const BLANKS: u8 = 4;
    pub(super) const EOL: u8 = 5;
    pub(super) const COMMENT: u8 = 6;
    pub(super) const DATE: u8 = 7;
    pub(super) const KEYWORD: u8 = 8;
    pub(super) const BOOL: u8 = 9;
    pub(super) const NONE: u8 = 10;
    pub(super) const ACCOUNT: u8 = 11;
    pub(super) const CURRENCY: u8 = 12;
    pub(super) const SLASH_CURRENCY: u8 = 13;
    pub(super) const STRING: u8 = 14;
    pub(super) const NUMBER: u8 = 15;
    pub(super) const TAG: u8 = 16;
    pub(super) const LINK: u8 = 17;
    pub(super) const KEY: u8 = 18;
    pub(super) const AT: u8 = 19;
    pub(super) const BRACES: u8 = 20;
    pub(super) const PUNCT: u8 = 21;
    pub(super) const FLAG: u8 = 22;
    pub(super) const CAPITAL: u8 = 23;
}

/// The post-lex check a rule's text must pass, or become an error token.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Check {
    None,
    Date,
    Number,
    Utf8,
}

/// The longest match so far at the current position.
#[derive(Default)]
struct Best(Option<Candidate>);

impl Best {
    /// Offers a rule's match: the longest total wins, the earlier rule a tie.
    const fn offer(&mut self, c: Candidate) {
        match &self.0 {
            Some(b) if b.total > c.total || (b.total == c.total && b.rule <= c.rule) => {}
            _ => self.0 = Some(c),
        }
    }
}

/// A rule's match at the current position.
#[derive(Clone, Copy)]
struct Candidate {
    /// Length including trailing context: what the longest-match rule compares.
    total: usize,
    rule: u8,
    /// `None` for a skipped match (blanks, comments, ignored lines).
    tok: Option<Tok>,
    /// Bytes consumed (the trailing context is not).
    len: usize,
    check: Check,
}

const KEYWORDS: [(&[u8], Tok); 19] = [
    (b"txn", Tok::Txn),
    (b"balance", Tok::Balance),
    (b"open", Tok::Open),
    (b"close", Tok::Close),
    (b"commodity", Tok::Commodity),
    (b"pad", Tok::Pad),
    (b"event", Tok::Event),
    (b"price", Tok::Price),
    (b"note", Tok::Note),
    (b"document", Tok::Document),
    (b"query", Tok::Query),
    (b"custom", Tok::Custom),
    (b"pushtag", Tok::Pushtag),
    (b"poptag", Tok::Poptag),
    (b"pushmeta", Tok::Pushmeta),
    (b"popmeta", Tok::Popmeta),
    (b"option", Tok::Option),
    (b"include", Tok::Include),
    (b"plugin", Tok::Plugin),
];

const fn is_blank(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r')
}

/// `[A-Za-z0-9\-_/.]`: what may follow `#` in a tag or `^` in a link.
const fn is_tag_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'/' | b'.')
}

/// `[A-Z0-9'._\-]`: the inner characters of a currency.
const fn is_currency_char(b: u8) -> bool {
    b.is_ascii_uppercase() || b.is_ascii_digit() || matches!(b, b'\'' | b'.' | b'_' | b'-')
}

/// The length of the validly encoded non-ASCII UTF-8 code point at `i`
/// (`LEXICAL.md`'s `U8`, RFC 3629's table), if there is one.
fn utf8_char_len(s: &[u8], i: usize) -> Option<usize> {
    let b0 = *s.get(i)?;
    let cont = |k: usize, lo: u8, hi: u8| s.get(i + k).is_some_and(|&b| (lo..=hi).contains(&b));
    let (n, lo1, hi1) = match b0 {
        0xC2..=0xDF => (2, 0x80, 0xBF),
        0xE0 => (3, 0xA0, 0xBF),
        0xE1..=0xEC | 0xEE | 0xEF => (3, 0x80, 0xBF),
        0xED => (3, 0x80, 0x9F),
        0xF0 => (4, 0x90, 0xBF),
        0xF1..=0xF3 => (4, 0x80, 0xBF),
        0xF4 => (4, 0x80, 0x8F),
        _ => return None,
    };
    if !cont(1, lo1, hi1) {
        return None;
    }
    (2..n).all(|k| cont(k, 0x80, 0xBF)).then_some(n)
}

/// One account-name character at `i` from `ascii` or `U8`: its length.
#[inline]
fn account_char(s: &[u8], i: usize, ascii: impl Fn(u8) -> bool) -> Option<usize> {
    let b = *s.get(i)?;
    if b.is_ascii() {
        ascii(b).then_some(1)
    } else {
        utf8_char_len(s, i)
    }
}

/// `([A-Za-z0-9\-]|U8)*` from `i`: where the run ends.
fn account_tail(s: &[u8], mut i: usize) -> usize {
    loop {
        // ASCII first: the common case, a byte at a time.
        while s
            .get(i)
            .is_some_and(|&b| b.is_ascii_alphanumeric() || b == b'-')
        {
            i += 1;
        }
        match s.get(i) {
            Some(&b) if !b.is_ascii() => match utf8_char_len(s, i) {
                Some(n) => i += n,
                None => return i,
            },
            _ => return i,
        }
    }
}

/// Rule 11, `ACCOUNT`: the match length at `p`.
fn match_account(s: &[u8], p: usize) -> Option<usize> {
    let first = account_char(s, p, |b| b.is_ascii_uppercase())?;
    let mut end = account_tail(s, p + first);
    let mut components = 0;
    while s.get(end) == Some(&b':') {
        let Some(n) = account_char(s, end + 1, |b| b.is_ascii_uppercase() || b.is_ascii_digit())
        else {
            break;
        };
        end = account_tail(s, end + 1 + n);
        components += 1;
    }
    (components > 0).then_some(end - p)
}

/// The end of the longest `[A-Z0-9'._\-]*[A-Z0-9]` starting at `i`, if any
/// (the regex's greedy run backed off to its last letter or digit).
fn currency_body_end(s: &[u8], i: usize) -> Option<usize> {
    let mut j = i;
    let mut last = None;
    while let Some(&b) = s.get(j) {
        if !is_currency_char(b) {
            break;
        }
        j += 1;
        if b.is_ascii_uppercase() || b.is_ascii_digit() {
            last = Some(j);
        }
    }
    last
}

/// Rule 12, `CURRENCY`: `[A-Z][A-Z0-9'._\-]*[A-Z0-9]`.
fn match_currency(s: &[u8], p: usize) -> Option<usize> {
    if !s.get(p)?.is_ascii_uppercase() {
        return None;
    }
    currency_body_end(s, p + 1).map(|e| e - p)
}

/// Rule 13, `CURRENCY`: `/[0-9'._\-]*[A-Z]([A-Z0-9'._\-]*[A-Z0-9])?`.
fn match_slash_currency(s: &[u8], p: usize) -> Option<usize> {
    let mut j = p + 1;
    while s
        .get(j)
        .is_some_and(|&b| b.is_ascii_digit() || matches!(b, b'\'' | b'.' | b'_' | b'-'))
    {
        j += 1;
    }
    if !s.get(j)?.is_ascii_uppercase() {
        return None;
    }
    let end = currency_body_end(s, j + 1).unwrap_or(j + 1);
    Some(end - p)
}

/// Rule 14, `STRING`: `"([^"\\]|\\[^\n])*"`. A backslash before a newline or
/// the end of input matches nothing, and neither does an unterminated string.
fn match_string(s: &[u8], p: usize) -> Option<usize> {
    let mut j = p + 1;
    loop {
        match *s.get(j)? {
            b'"' => return Some(j + 1 - p),
            b'\\' => match s.get(j + 1) {
                Some(&b) if b != b'\n' => j += 2,
                _ => return None,
            },
            _ => j += 1,
        }
    }
}

/// Rule 15, `NUMBER`: `[0-9]([0-9,]*[0-9])?(\.[0-9]*)?`.
fn match_number(s: &[u8], p: usize) -> Option<usize> {
    if !s.get(p)?.is_ascii_digit() {
        return None;
    }
    let mut j = p + 1;
    let mut int_end = j;
    while let Some(&b) = s.get(j) {
        if b.is_ascii_digit() {
            j += 1;
            int_end = j;
        } else if b == b',' {
            j += 1;
        } else {
            break;
        }
    }
    let mut end = int_end;
    if s.get(end) == Some(&b'.') {
        end += 1;
        while s.get(end).is_some_and(u8::is_ascii_digit) {
            end += 1;
        }
    }
    Some(end - p)
}

/// Rule 7, `DATE`: `[0-9]{4,}[-/][0-9]+[-/][0-9]+`.
fn match_date(s: &[u8], at: usize) -> Option<usize> {
    let digits = |from: usize| {
        let mut j = from;
        while s.get(j).is_some_and(u8::is_ascii_digit) {
            j += 1;
        }
        j
    };
    let separator = |j: usize| matches!(s.get(j), Some(b'-' | b'/'));
    let year_end = digits(at);
    if year_end - at < 4 || !separator(year_end) {
        return None;
    }
    let month_end = digits(year_end + 1);
    if month_end == year_end + 1 || !separator(month_end) {
        return None;
    }
    let day_end = digits(month_end + 1);
    if day_end == month_end + 1 {
        return None;
    }
    Some(day_end - at)
}

/// The value of a run of ASCII digits, or `None` past `u32` (every such value
/// fails the date check anyway).
fn small_number(digits: &[u8]) -> Option<u32> {
    let digits = match digits.iter().position(|&b| b != b'0') {
        Some(i) => &digits[i..],
        None => return Some(0),
    };
    if digits.len() > 9 {
        return None;
    }
    Some(
        digits
            .iter()
            .fold(0, |acc, &b| acc * 10 + u32::from(b - b'0')),
    )
}

/// The date check: a valid proleptic-Gregorian date with year 1..=9999.
fn date_ok(text: &[u8]) -> bool {
    let mut fields = text.split(|&b| b == b'-' || b == b'/').map(small_number);
    let (Some(Some(y)), Some(Some(m)), Some(Some(d))) =
        (fields.next(), fields.next(), fields.next())
    else {
        return false;
    };
    if !(1..=9999).contains(&y) || !(1..=12).contains(&m) || d == 0 {
        return false;
    }
    let leap = y % 4 == 0 && (y % 100 != 0 || y % 400 == 0);
    let days = match m {
        2 if leap => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    };
    d <= days
}

/// The number check: at most 255 characters without commas, and an integer
/// part grouped as `[0-9]{1,3}(,[0-9]{3})*` (or the observed quirk
/// `[0-9],,[0-9]{3}(,[0-9]{3})*`) when it holds a comma.
fn number_ok(text: &[u8]) -> bool {
    if text.iter().filter(|&&b| b != b',').count() > 255 {
        return false;
    }
    let int = text.split(|&b| b == b'.').next().unwrap_or_default();
    if !int.contains(&b',') {
        return true;
    }
    let groups_of_three = |rest: &[u8]| {
        rest.split(|&b| b == b',')
            .all(|g| g.len() == 3 && g.iter().all(u8::is_ascii_digit))
    };
    let mut groups = int.splitn(2, |&b| b == b',');
    let head = groups.next().unwrap_or_default();
    let rest = groups.next().unwrap_or_default();
    if (1..=3).contains(&head.len()) && groups_of_three(rest) {
        return true;
    }
    // `1,,000`: one digit, two commas, then groups of three.
    head.len() == 1 && rest.first() == Some(&b',') && groups_of_three(&rest[1..])
}

fn run_check(check: Check, text: &[u8]) -> bool {
    match check {
        Check::Date => date_ok(text),
        Check::Number => number_ok(text),
        Check::Utf8 => std::str::from_utf8(text).is_ok(),
        Check::None => true,
    }
}

/// beancount's lexer over `src`. Iterates [`Lexeme`]s, lexer errors included,
/// without an end-of-input token (the parser driver supplies that).
pub struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    line: u32,
}

impl<'a> Lexer<'a> {
    pub const fn new(src: &'a [u8]) -> Self {
        Self {
            src,
            pos: 0,
            line: 1,
        }
    }

    /// The candidates that can match at `p`, given its first byte `b`.
    fn candidates(&self, p: usize, b: u8, out: &mut Best) {
        let s = self.src;
        let bol = p == 0 || s.get(p - 1) == Some(&b'\n');
        let mut push = |rule: u8, tok: Option<Tok>, len: usize, tc: usize, check: Check| {
            out.offer(Candidate {
                total: len + tc,
                rule,
                tok,
                len,
                check,
            });
        };
        if bol {
            if matches!(b, b' ' | b'\t') {
                let mut j = p;
                while matches!(s.get(j), Some(b' ' | b'\t')) {
                    j += 1;
                }
                if s.get(j)
                    .is_some_and(|&c| !matches!(c, b' ' | b'\t' | b'\r' | b'\n'))
                {
                    push(rule::INDENT, Some(Tok::Indent), j - p, 1, Check::None);
                }
            }
            if matches!(b, b'*' | b':' | b'!' | b'&' | b'?' | b'%') {
                let rest = s[p + 1..]
                    .iter()
                    .position(|&c| c == b'\n')
                    .unwrap_or(s.len() - p - 1);
                if rest > 0 {
                    push(rule::IGNORED_MARKER_LINE, None, 1 + rest, 0, Check::None);
                }
            }
            if b == b'#' && s.get(p + 1).is_some_and(|&c| c != b'\n' && !is_tag_char(c)) {
                let rest = s[p + 1..]
                    .iter()
                    .position(|&c| c == b'\n')
                    .unwrap_or(s.len() - p - 1);
                push(rule::IGNORED_HASH_LINE, None, 1 + rest, 0, Check::None);
            }
        }
        match b {
            b' ' | b'\t' | b'\r' => {
                let n = s[p..].iter().take_while(|&&c| is_blank(c)).count();
                push(rule::BLANKS, None, n, 0, Check::None);
            }
            b'\n' => push(rule::EOL, Some(Tok::Eol), 1, 0, Check::None),
            b';' => {
                let n = s[p..]
                    .iter()
                    .position(|&c| c == b'\n')
                    .unwrap_or(s.len() - p);
                push(rule::COMMENT, None, n, 0, Check::None);
            }
            b'0'..=b'9' => {
                if let Some(n) = match_date(s, p) {
                    push(rule::DATE, Some(Tok::Date), n, 0, Check::Date);
                }
                if let Some(n) = match_number(s, p) {
                    push(rule::NUMBER, Some(Tok::Number), n, 0, Check::Number);
                }
            }
            b'a'..=b'z' => {
                // Keywords need no word boundary; at most two share a first
                // letter, so only those are compared.
                for (kw, tok) in KEYWORDS {
                    if kw[0] == b && s.get(p..p + kw.len()) == Some(kw) {
                        push(rule::KEYWORD, Some(tok), kw.len(), 0, Check::None);
                    }
                }
                let n = 1 + s[p + 1..]
                    .iter()
                    .take_while(|&&c| c.is_ascii_alphanumeric() || matches!(c, b'-' | b'_'))
                    .count();
                if n >= 2 && s.get(p + n) == Some(&b':') {
                    push(rule::KEY, Some(Tok::Key), n, 1, Check::None);
                }
            }
            b'A'..=b'Z' => {
                for (lit, rule, tok) in [
                    (&b"TRUE"[..], rule::BOOL, Tok::Bool),
                    (b"FALSE", rule::BOOL, Tok::Bool),
                    (b"NULL", rule::NONE, Tok::None),
                ] {
                    if s[p..].starts_with(lit) {
                        push(rule, Some(tok), lit.len(), 0, Check::None);
                    }
                }
                if let Some(n) = match_account(s, p) {
                    push(rule::ACCOUNT, Some(Tok::Account), n, 0, Check::None);
                }
                if let Some(n) = match_currency(s, p) {
                    push(rule::CURRENCY, Some(Tok::Currency), n, 0, Check::None);
                }
                if matches!(s.get(p + 1), Some(b' ' | b'\t' | b'\n')) {
                    push(rule::CAPITAL, Some(Tok::Capital), 1, 1, Check::None);
                }
            }
            0x80..=0xFF => {
                if let Some(n) = match_account(s, p) {
                    push(rule::ACCOUNT, Some(Tok::Account), n, 0, Check::None);
                }
            }
            b'/' => {
                if let Some(n) = match_slash_currency(s, p) {
                    push(rule::SLASH_CURRENCY, Some(Tok::Currency), n, 0, Check::None);
                }
                push(rule::PUNCT, Some(Tok::Slash), 1, 0, Check::None);
            }
            b'"' => {
                if let Some(n) = match_string(s, p) {
                    push(rule::STRING, Some(Tok::String), n, 0, Check::Utf8);
                }
            }
            b'#' | b'^' => {
                let n = s[p + 1..].iter().take_while(|&&c| is_tag_char(c)).count();
                if n > 0 {
                    let (rule, tok) = if b == b'#' {
                        (rule::TAG, Tok::Tag)
                    } else {
                        (rule::LINK, Tok::Link)
                    };
                    push(rule, Some(tok), 1 + n, 0, Check::None);
                }
                if b == b'#' {
                    push(rule::PUNCT, Some(Tok::Hash), 1, 0, Check::None);
                }
            }
            b'@' => {
                if s.get(p + 1) == Some(&b'@') {
                    push(rule::AT, Some(Tok::Atat), 2, 0, Check::None);
                }
                push(rule::AT, Some(Tok::At), 1, 0, Check::None);
            }
            b'{' | b'}' => {
                let (one, two) = if b == b'{' {
                    (Tok::Lcurl, Tok::Lcurlcurl)
                } else {
                    (Tok::Rcurl, Tok::Rcurlcurl)
                };
                if s.get(p + 1) == Some(&b) {
                    push(rule::BRACES, Some(two), 2, 0, Check::None);
                }
                push(rule::BRACES, Some(one), 1, 0, Check::None);
            }
            b',' | b'~' | b'+' | b'-' | b'(' | b')' | b'|' | b'*' | b':' => {
                let tok = match b {
                    b',' => Tok::Comma,
                    b'~' => Tok::Tilde,
                    b'+' => Tok::Plus,
                    b'-' => Tok::Minus,
                    b'(' => Tok::Lparen,
                    b')' => Tok::Rparen,
                    b'|' => Tok::Pipe,
                    b'*' => Tok::Asterisk,
                    _ => Tok::Colon,
                };
                push(rule::PUNCT, Some(tok), 1, 0, Check::None);
            }
            b'!' | b'&' | b'?' | b'%' => push(rule::FLAG, Some(Tok::Flag), 1, 0, Check::None),
            _ => {}
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Lexeme;

    fn next(&mut self) -> Option<Lexeme> {
        loop {
            let p = self.pos;
            let b = *self.src.get(p)?;
            let mut best = Best::default();
            self.candidates(p, b, &mut best);
            let (tok, len, may_span_lines) = if let Some(c) = best.0 {
                let text = &self.src[p..p + c.len];
                let multi = matches!(c.tok, Some(Tok::String | Tok::Eol));
                match c.tok {
                    None => (None, c.len, false),
                    Some(t) if run_check(c.check, text) => (Some(t), c.len, multi),
                    Some(_) => (Some(Tok::Error), c.len, multi),
                }
            } else {
                // An invalid run: up to the next space, tab, CR or LF.
                let n = self.src[p..]
                    .iter()
                    .position(|&c| matches!(c, b' ' | b'\t' | b'\r' | b'\n'))
                    .unwrap_or(self.src.len() - p);
                (Some(Tok::Error), n.max(1), false)
            };
            let end = p + len;
            // Only an end of line or a string can hold a `\n`.
            if may_span_lines {
                let newlines = self.src[p..end].split(|&c| c == b'\n').count() - 1;
                self.line = self
                    .line
                    .saturating_add(u32::try_from(newlines).unwrap_or(u32::MAX));
            }
            self.pos = end;
            if let Some(tok) = tok {
                return Some(Lexeme {
                    tok,
                    start: u32::try_from(p).unwrap_or(u32::MAX),
                    end: u32::try_from(end).unwrap_or(u32::MAX),
                    line: self.line,
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(src: &str) -> Vec<(&'static str, u32, &str)> {
        Lexer::new(src.as_bytes())
            .map(|l| (l.tok.name(), l.line, &src[l.start as usize..l.end as usize]))
            .collect()
    }

    fn names(src: &str) -> Vec<&'static str> {
        lex(src).into_iter().map(|(n, _, _)| n).collect()
    }

    #[test]
    fn test_lexer_examples_from_lexical_md() {
        assert_eq!(names("USD$"), ["CURRENCY", "error"]);
        assert_eq!(names("x;y"), ["error"]);
        assert_eq!(names("x\"a b\""), ["error", "error"]);
        assert_eq!(names("opena"), ["OPEN", "error"]);
        assert_eq!(names("openA "), ["OPEN", "CAPITAL"]);
        assert_eq!(names("open: 1"), ["KEY", "COLON", "NUMBER"]);
        assert_eq!(names("TRUEX"), ["CURRENCY"]);
        assert_eq!(names("TRUE"), ["BOOL"]);
        assert_eq!(names("Foo:Bar"), ["ACCOUNT"]);
        assert_eq!(names("Assets:é Équity:A"), ["ACCOUNT", "ACCOUNT"]);
        assert_eq!(
            names("/ES /6J /A /6"),
            ["CURRENCY", "CURRENCY", "CURRENCY", "SLASH", "NUMBER"]
        );
        assert_eq!(names(".5"), ["error"]);
        assert_eq!(names("1."), ["NUMBER"]);
        assert_eq!(names("kk 1"), ["error", "NUMBER"]);
        assert_eq!(names("k: 1"), ["error", "NUMBER"]);
        assert_eq!(names("Kk: 1"), ["error", "NUMBER"]);
        assert_eq!(names("P,"), ["error"]);
        assert_eq!(names("P\r"), ["error"]);
        assert_eq!(names("P"), ["error"]);
        assert_eq!(names("P "), ["CAPITAL"]);
        assert_eq!(names("\u{feff}2024-01-01 open"), ["error", "OPEN"]);
    }

    #[test]
    fn test_lexer_numbers_and_dates() {
        assert_eq!(names("1,,000"), ["NUMBER"]);
        for bad in [
            "11,,000",
            "1,000,,000",
            "1,0",
            "1,00,000",
            "1,0000",
            "1111,111",
        ] {
            assert_eq!(names(bad), ["error"], "{bad}");
        }
        assert_eq!(names("1,000,000.25"), ["NUMBER"]);
        assert_eq!(names(&"9".repeat(256)), ["error"]);
        assert_eq!(names(&"9".repeat(255)), ["NUMBER"]);
        assert_eq!(names("2024-01/01 02024-001-01"), ["DATE", "DATE"]);
        for bad in ["2024-02-30", "2024-00-10", "0000-01-01", "12345-01-01"] {
            assert_eq!(names(bad), ["error"], "{bad}");
        }
        assert_eq!(names("2024-02-29"), ["DATE"]);
        assert_eq!(names("2023-02-29"), ["error"]);
        assert_eq!(
            names("999-01-01"),
            ["NUMBER", "MINUS", "NUMBER", "MINUS", "NUMBER"]
        );
    }

    #[test]
    fn test_lexer_line_starts_and_lines() {
        assert_eq!(names("  ;c\n"), ["INDENT", "EOL"]);
        assert_eq!(names("   \n"), ["EOL"]);
        assert_eq!(names("\r  x"), ["error"]);
        assert_eq!(names("* heading\n*\n!"), ["EOL", "ASTERISK", "EOL", "FLAG"]);
        assert_eq!(
            names("#tag\n# x\n#\n"),
            ["TAG", "EOL", "EOL", "HASH", "EOL"]
        );
        assert_eq!(names("a #x"), ["error", "TAG"]);
        let toks = lex("\"a\nb\" x\n2024-01-01");
        assert_eq!(toks[0], ("STRING", 2, "\"a\nb\""));
        assert_eq!(toks[2], ("EOL", 3, "\n"));
        assert_eq!(toks[3].1, 3);
        assert_eq!(names("\"a\\\nb\""), ["error", "EOL", "error"]);
        assert_eq!(names("\"a\\\"b\""), ["STRING"]);
    }
}
