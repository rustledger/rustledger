//! bison's error recovery in beancount's parser, modeled token by token
//! (#2993, #2979, #2872).
//!
//! beancount's grammar (`grammar.y`, 3.2.3) has one error rule,
//! `declarations: declarations error`. When its parser fails, bison sets its
//! error status to three, pops its stack back to a `declarations`, and shifts
//! the `error` token there. From then on:
//!
//! * a token the state cannot take is an error that is NOT reported while the
//!   status is above zero. At status three it is discarded; below three the
//!   status goes back to three and the token is tried again from a
//!   `declarations`, where it is shifted if it can start one, discarded if not;
//! * a token the state takes is shifted, and each shift lowers the status by
//!   one, so reporting resumes once three tokens have been shifted;
//! * an invalid token is the lexer's own error, always reported by the lexer
//!   (`Invalid token: ...`, an invalid date, a malformed number): the lexer
//!   returns `YYerror` for it, which puts bison straight into recovery at
//!   status three, with no syntax error of its own.
//!
//! So after a failed statement only the lexer's errors are reported until
//! bison has shifted three tokens: a posting under a failed header, a second
//! bad posting under a bad one, an unreadable line after an unreadable line,
//! a blank line counting one shift, an indented line starting the count over.
//!
//! [`quiet_bison_recovery`] runs this machine over beancount's own tokens
//! ([`BcLexer`], a port of `lexer.l`), from each error rledger reports while
//! bison is not recovering, and drops the errors rledger reports where bison
//! is quiet. On such a line beancount reports exactly its lexer errors, so the
//! line keeps as many of rledger's errors as beancount's lexer finds there
//! (rledger's invalid-token and invalid-date errors first): a line error that
//! stands for an invalid token is kept, one that stands for the grammar's
//! failure is dropped.
//!
//! Where bison's recovery shifts the start of a dated entry in the middle of a
//! line (`2024-01-02 2024-01-03 * "n"`, `$ 2024-01-02 * "y"`) or on an indented
//! line, beancount BUILDS that entry, and the indented lines after it are its
//! body (#2979). That entry is a recovery artifact, so it is not emitted here
//! (rledger's Python compatibility policy: a beancount bug that can be fixed
//! locally is not copied). But the errors beancount reports there are the
//! ones the entry's own parse gives, so that text is parsed on its own and its
//! errors replace rledger's on those lines. An undated declaration shifted
//! that way (`$ pushtag #a`) changes beancount's state, which is not modeled:
//! from there rledger's errors are kept as they are. Where such an entry's
//! own line holds an invalid token (`$ 2024-01-02 * "y" $`), that token's
//! `YYerror` drops the entry and starts the recovery over: the line gets the
//! errors it has parsed on its own, and the window goes on from its end.
//!
//! An invalid account (P0006) is rledger's line error for a line it cannot
//! read, named for the account on it; beancount's lexer reads that account
//! into an `ACCOUNT` (or, glued to more, an invalid token), so it starts the
//! recovery as any other line error does.
//!
//! An undated declaration bison's recovery starts mid-line (`popmeta pushmeta
//! kk: @`) and that then fails past its first three tokens builds nothing:
//! bison reports that failure and starts its recovery over at it, so the
//! window goes on from there, with an error added where rledger has none.
//!
//! A BOM diagnostic starts the recovery where beancount's lexer reads that
//! BOM into an invalid token (`<BOM>g`, a BOM alone after an indent), as the
//! `$` it then stands for would. Inside the window, a lexer error rledger has
//! no error for is added where this parser reads the text as something else:
//! a lone capital glued to a `\r` (an invalid token) or a misgrouped number
//! (`1,50`, `InvalidNumber`).

use std::ops::Range;

/// A beancount token class: what `lexer.l` returns, as far as the recovery
/// needs to tell tokens apart.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Bc {
    Eol,
    Eof,
    Indent,
    Date,
    Kw(Kw),
    Txn,
    Flag,
    Asterisk,
    Hash,
    Capital,
    Str,
    Account,
    Currency,
    Number,
    Tag,
    Link,
    Key,
    Colon,
    Pipe,
    Other,
    /// `YYerror`: an invalid token, date or number, which the lexer reports.
    Error,
}

/// A beancount keyword.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Kw {
    Balance,
    Open,
    Close,
    Commodity,
    Pad,
    Event,
    Price,
    Note,
    Document,
    Query,
    Custom,
    Pushtag,
    Poptag,
    Pushmeta,
    Popmeta,
    Option,
    Plugin,
    Include,
}

const KEYWORDS: [(&str, Bc); 19] = [
    ("txn", Bc::Txn),
    ("balance", Bc::Kw(Kw::Balance)),
    ("open", Bc::Kw(Kw::Open)),
    ("close", Bc::Kw(Kw::Close)),
    ("commodity", Bc::Kw(Kw::Commodity)),
    ("pad", Bc::Kw(Kw::Pad)),
    ("event", Bc::Kw(Kw::Event)),
    ("query", Bc::Kw(Kw::Query)),
    ("custom", Bc::Kw(Kw::Custom)),
    ("price", Bc::Kw(Kw::Price)),
    ("note", Bc::Kw(Kw::Note)),
    ("document", Bc::Kw(Kw::Document)),
    ("pushtag", Bc::Kw(Kw::Pushtag)),
    ("poptag", Bc::Kw(Kw::Poptag)),
    ("pushmeta", Bc::Kw(Kw::Pushmeta)),
    ("popmeta", Bc::Kw(Kw::Popmeta)),
    ("option", Bc::Kw(Kw::Option)),
    ("plugin", Bc::Kw(Kw::Plugin)),
    ("include", Bc::Kw(Kw::Include)),
];

/// Whether `run`, a run of digits and commas that a `NUMBER` token starts
/// and that ends in a digit, is a number beancount's lexer rejects: one whose
/// commas are not thousands separators (`1,50`, `1234,567`; `ValueError:
/// Invalid number format`). The integer part is one to three digits, then
/// groups of three; one more form passes beancount's validator, a single
/// digit, a doubled comma, then groups of three (`1,,000`; #2976).
pub(super) fn is_misgrouped_number_run(run: &str) -> bool {
    if !run.contains(',') {
        return false;
    }
    let mut groups = run.split(',').peekable();
    let first = groups.next().map_or(0, str::len);
    if first == 1 && groups.peek().is_some_and(|g| g.is_empty()) {
        groups.next();
    }
    let mut any = false;
    let rest_ok = groups.all(|g| {
        any = true;
        g.len() == 3
    });
    !((1..=3).contains(&first) && any && rest_ok)
}

/// beancount 3.2.3's lexer (`lexer.l`), over `src` from a line start: the
/// same rules in the same order, flex's longest match (trailing context
/// counted in a match's length, as flex counts it), the earlier rule on a
/// tie. Whitespace, comments and the lines its `IGNORE` state skips yield no
/// token. Each token is produced in time linear in its length.
pub(super) struct BcLexer<'a> {
    src: &'a str,
    pos: usize,
    /// At the start of a line (flex's `^`).
    bol: bool,
    done: bool,
}

impl<'a> BcLexer<'a> {
    /// A lexer at `pos`, which must be the start of a line outside any
    /// string.
    pub(super) const fn at_line_start(src: &'a str, pos: usize) -> Self {
        Self {
            src,
            pos,
            bol: true,
            done: false,
        }
    }

    /// A lexer at `pos`, which must be where a token ends on a line, outside
    /// any string (flex's `^` does not hold there).
    const fn mid_line(src: &'a str, pos: usize) -> Self {
        Self {
            src,
            pos,
            bol: false,
            done: false,
        }
    }

    pub(super) const fn pos(&self) -> usize {
        self.pos
    }
}

const fn is_upper(b: u8) -> bool {
    b.is_ascii_uppercase()
}

/// `[A-Za-z0-9\-]|{UTF-8-ONLY}`, the rest of an account component.
const fn account_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '-' || !c.is_ascii()
}

const fn currency_body(b: u8) -> bool {
    b.is_ascii_uppercase() || b.is_ascii_digit() || matches!(b, b'\'' | b'.' | b'_' | b'-')
}

const fn tag_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'/' | b'.')
}

impl BcLexer<'_> {
    /// The length of the longest `ACCOUNT` match at `p`, or 0.
    fn account_len(&self, p: usize) -> usize {
        let s = &self.src[p..];
        let mut chars = s.char_indices();
        let Some((_, c0)) = chars.next() else {
            return 0;
        };
        if !c0.is_ascii_uppercase() && c0.is_ascii() {
            return 0;
        }
        let mut end = c0.len_utf8();
        for (i, c) in chars.by_ref() {
            if account_char(c) {
                end = i + c.len_utf8();
            } else {
                break;
            }
        }
        let mut matched = 0;
        loop {
            let rest = &s[end..];
            let mut it = rest.chars();
            if it.next() != Some(':') {
                break;
            }
            let Some(c1) = it.next() else { break };
            if !(c1.is_ascii_uppercase() || c1.is_ascii_digit() || !c1.is_ascii()) {
                break;
            }
            end += 1 + c1.len_utf8();
            for c in it {
                if account_char(c) {
                    end += c.len_utf8();
                } else {
                    break;
                }
            }
            matched = end;
        }
        matched
    }

    fn lex(&mut self) -> (Bc, Range<usize>) {
        let src = self.src;
        let b = src.as_bytes();
        loop {
            let p = self.pos;
            if p >= b.len() {
                self.done = true;
                return (Bc::Eof, p..p);
            }
            let c = b[p];
            if c == b'\n' {
                self.pos = p + 1;
                self.bol = true;
                return (Bc::Eol, p..p + 1);
            }
            if c == b' ' || c == b'\t' || c == b'\r' {
                let ws = b[p..]
                    .iter()
                    .take_while(|&&x| x == b' ' || x == b'\t')
                    .count();
                let after = b.get(p + ws).copied();
                if self.bol
                    && ws > 0
                    && after.is_some_and(|x| !matches!(x, b' ' | b'\t' | b'\r' | b'\n'))
                {
                    self.pos = p + ws;
                    self.bol = false;
                    return (Bc::Indent, p..p + ws);
                }
                let run = b[p..]
                    .iter()
                    .take_while(|&&x| matches!(x, b' ' | b'\t' | b'\r'))
                    .count();
                self.pos = p + run;
                self.bol = false;
                continue;
            }
            if c == b';' {
                self.pos = src[p..].find('\n').map_or(b.len(), |i| p + i);
                self.bol = false;
                continue;
            }
            let next = b.get(p + 1).copied();
            let tag_len = |q: usize| b[q + 1..].iter().take_while(|&&x| tag_char(x)).count();
            // `^[\*\:\#]/.` and `^{FLAGS}/.`: the rest of the line is skipped.
            // A tag at the line start is the same length and an earlier rule.
            if self.bol
                && matches!(c, b'*' | b':' | b'#' | b'!' | b'&' | b'?' | b'%')
                && next.is_some_and(|x| x != b'\n')
                && !(c == b'#' && tag_len(p) >= 1)
            {
                self.pos = src[p..].find('\n').map_or(b.len(), |i| p + i);
                self.bol = false;
                continue;
            }
            self.bol = false;
            // Candidates as (matched length, consumed length, token), in rule
            // order; the longest match wins, the first on a tie.
            let mut best: (usize, usize, Bc) = (0, 0, Bc::Error);
            let mut offer = |len: usize, consumed: usize, tok: Bc| {
                if len > best.0 {
                    best = (len, consumed, tok);
                }
            };
            let rest = &src[p..];
            for (word, tok) in [
                ("TRUE", Bc::Other),
                ("FALSE", Bc::Other),
                ("NULL", Bc::Other),
            ] {
                if rest.starts_with(word) {
                    offer(word.len(), word.len(), tok);
                }
            }
            if is_upper(c) {
                let run = b[p + 1..].iter().take_while(|&&x| currency_body(x)).count();
                let last = (0..run)
                    .rev()
                    .find(|&i| b[p + 1 + i].is_ascii_uppercase() || b[p + 1 + i].is_ascii_digit());
                if let Some(i) = last {
                    offer(i + 2, i + 2, Bc::Currency);
                }
            }
            if c == b'/' {
                let run = b[p + 1..].iter().take_while(|&&x| currency_body(x)).count();
                let body = &b[p + 1..p + 1 + run];
                if let Some(first_alpha) = body.iter().position(u8::is_ascii_uppercase) {
                    let last = (first_alpha..run)
                        .rev()
                        .find(|&i| body[i].is_ascii_uppercase() || body[i].is_ascii_digit())
                        .unwrap_or(first_alpha);
                    offer(last + 2, last + 2, Bc::Currency);
                }
            }
            let punct = match c {
                b'|' => Some((1, Bc::Pipe)),
                b',' | b'~' | b'+' | b'-' | b'/' | b'(' | b')' => Some((1, Bc::Other)),
                b'@' if next == Some(b'@') => Some((2, Bc::Other)),
                b'{' if next == Some(b'{') => Some((2, Bc::Other)),
                b'}' if next == Some(b'}') => Some((2, Bc::Other)),
                b'@' | b'{' | b'}' => Some((1, Bc::Other)),
                b'#' => Some((1, Bc::Hash)),
                b'*' => Some((1, Bc::Asterisk)),
                b':' => Some((1, Bc::Colon)),
                b'!' | b'&' | b'?' | b'%' => Some((1, Bc::Flag)),
                _ => None,
            };
            if let Some((n, tok)) = punct {
                offer(n, n, tok);
            }
            if is_upper(c) && next.is_some_and(|x| matches!(x, b' ' | b'\t' | b'\n')) {
                offer(2, 1, Bc::Capital);
            }
            for (word, tok) in KEYWORDS {
                if rest.starts_with(word) {
                    offer(word.len(), word.len(), tok);
                }
            }
            if c.is_ascii_digit() {
                let digits = |q: usize| b[q..].iter().take_while(|x| x.is_ascii_digit()).count();
                let year = digits(p);
                let mut date = 0;
                if year >= 4 && matches!(b.get(p + year), Some(b'-' | b'/')) {
                    let month = digits(p + year + 1);
                    let q = p + year + 1 + month;
                    if month > 0 && matches!(b.get(q), Some(b'-' | b'/')) {
                        let day = digits(q + 1);
                        if day > 0 {
                            date = q + 1 + day - p;
                        }
                    }
                }
                if date > 0 {
                    let ok = super::convert::parse_date_token(&src[p..p + date]).is_some();
                    offer(date, date, if ok { Bc::Date } else { Bc::Error });
                }
            }
            let account = self.account_len(p);
            if account > 0 {
                offer(account, account, Bc::Account);
            }
            if c == b'"' {
                let mut q = p + 1;
                let mut closed = None;
                while q < b.len() {
                    match b[q] {
                        // `\\.`: `.` takes no line end, so a backslash before
                        // one ends no string.
                        b'\\' if matches!(b.get(q + 1), None | Some(b'\n')) => break,
                        b'\\' => q += 1 + src[q + 1..].chars().next().map_or(1, char::len_utf8),
                        b'"' => {
                            closed = Some(q + 1);
                            break;
                        }
                        _ => q += 1,
                    }
                }
                if let Some(end) = closed {
                    offer(end - p, end - p, Bc::Str);
                }
            }
            if c.is_ascii_digit() {
                let run = b[p..]
                    .iter()
                    .take_while(|x| x.is_ascii_digit() || **x == b',')
                    .count();
                let plain = b[p..].iter().take_while(|x| x.is_ascii_digit()).count();
                let grouped = (0..run)
                    .rev()
                    .find(|&i| b[p + i].is_ascii_digit())
                    .map_or(0, |i| i + 1);
                let int = if grouped >= 3 {
                    grouped.max(plain)
                } else {
                    plain
                };
                let mut end = p + int;
                if b.get(end) == Some(&b'.') {
                    end += 1 + b[end + 1..]
                        .iter()
                        .take_while(|x| x.is_ascii_digit())
                        .count();
                }
                let bad = is_misgrouped_number_run(&src[p..p + int]);
                offer(end - p, end - p, if bad { Bc::Error } else { Bc::Number });
            }
            if c == b'#' || c == b'^' {
                let n = tag_len(p);
                if n > 0 {
                    offer(n + 1, n + 1, if c == b'#' { Bc::Tag } else { Bc::Link });
                }
            }
            if c.is_ascii_lowercase() {
                let n = b[p + 1..]
                    .iter()
                    .take_while(|x| x.is_ascii_alphanumeric() || matches!(x, b'-' | b'_'))
                    .count();
                if n > 0 && b.get(p + 1 + n) == Some(&b':') {
                    offer(n + 2, n + 1, Bc::Key);
                }
            }
            if best.0 == 0 {
                // The default rule: an invalid token, to the next blank.
                let n = b[p..]
                    .iter()
                    .take_while(|x| !matches!(x, b' ' | b'\t' | b'\n' | b'\r'))
                    .count();
                self.pos = p + n;
                return (Bc::Error, p..p + n);
            }
            self.pos = p + best.1;
            return (best.2, p..p + best.1);
        }
    }
}

impl Iterator for BcLexer<'_> {
    type Item = (Bc, Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        #[cfg(test)]
        let from = self.pos;
        let token = self.lex();
        #[cfg(test)]
        crate::logos_lexer::test_counters::RECOVERY_SHIFT_SCANNED_BYTES
            .with(|c| c.set(c.get() + (self.pos - from)));
        Some(token)
    }
}

/// Whether bison, with `prefix` shifted since its last `declarations`, takes
/// `t` next (the first three tokens of every statement; the recovery never
/// needs more, as reporting resumes at the third shift).
pub(super) fn accepts(prefix: &[Bc], t: Bc) -> bool {
    use Bc as B;
    let eol = matches!(t, B::Eol | B::Eof);
    let txn_flag = |x: Bc| matches!(x, B::Txn | B::Flag | B::Asterisk | B::Hash | B::Capital);
    match prefix {
        [] => matches!(
            t,
            B::Eol
                | B::Date
                | B::Kw(
                    Kw::Pushtag
                        | Kw::Poptag
                        | Kw::Pushmeta
                        | Kw::Popmeta
                        | Kw::Option
                        | Kw::Include
                        | Kw::Plugin
                )
        ),
        [B::Date] => {
            txn_flag(t)
                || matches!(
                    t,
                    B::Kw(
                        Kw::Open
                            | Kw::Close
                            | Kw::Commodity
                            | Kw::Pad
                            | Kw::Balance
                            | Kw::Price
                            | Kw::Event
                            | Kw::Query
                            | Kw::Note
                            | Kw::Document
                            | Kw::Custom
                    )
                )
        }
        [B::Date, f] if txn_flag(*f) => eol || matches!(t, B::Str | B::Pipe | B::Tag | B::Link),
        [
            B::Date,
            B::Kw(Kw::Open | Kw::Close | Kw::Pad | Kw::Balance | Kw::Note | Kw::Document),
        ] => t == B::Account,
        [B::Date, B::Kw(Kw::Commodity | Kw::Price)] => matches!(t, B::Currency | B::Capital),
        [B::Date, B::Kw(Kw::Event | Kw::Query | Kw::Custom)] => t == B::Str,
        [B::Kw(Kw::Pushtag | Kw::Poptag)] => t == B::Tag,
        [B::Kw(Kw::Pushmeta | Kw::Popmeta)] => t == B::Key,
        [B::Kw(Kw::Option | Kw::Include | Kw::Plugin)] => t == B::Str,
        [B::Kw(Kw::Pushtag | Kw::Poptag), B::Tag] | [B::Kw(Kw::Include), B::Str] => eol,
        [B::Kw(Kw::Pushmeta | Kw::Popmeta), B::Key] => t == B::Colon,
        [B::Kw(Kw::Option), B::Str] => t == B::Str,
        [B::Kw(Kw::Plugin), B::Str] => eol || t == B::Str,
        _ => false,
    }
}

thread_local! {
    /// How deep [`quiet_bison_recovery`] has nested the parse of an entry
    /// bison's recovery builds: one level at most, so the work stays linear.
    static PHANTOM_DEPTH: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    /// Set by a nested pass that met a declaration bison shifts mid-line,
    /// whose effect it does not model: the entry around it keeps rledger's
    /// errors.
    static UNMODELED_PHANTOM: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether `e` is rledger's report of one of beancount's lexer errors: an
/// invalid date, a BOM diagnostic, an unclosed string or bad escape, or any
/// error that starts inside an invalid token.
fn is_lexer_kind(e: &crate::ParseError, start: usize, invalid: &[Range<usize>]) -> bool {
    use crate::ParseErrorKind as K;
    matches!(
        e.kind,
        K::InvalidDateValue(_)
            | K::InvalidDate(_)
            | K::BomInDirectiveBody
            | K::UnclosedString
            | K::InvalidEscape(_)
    ) || {
        let i = invalid.partition_point(|r| r.start <= start);
        i.checked_sub(1).is_some_and(|i| start < invalid[i].end)
    }
}

/// Whether `e` is an error beancount's grammar raises, or what it builds
/// raises, so one bison's recovery keeps quiet: not an unclosed or unmatched
/// push (the state after the file), and not one of rledger's own notes.
const fn is_droppable(e: &crate::ParseError) -> bool {
    use crate::ParseErrorKind as K;
    matches!(
        e.kind,
        K::SyntaxError(_)
            | K::InvalidAccount(_)
            | K::InvalidAccountFormat(_)
            | K::InvalidBookingMethod(_)
            | K::Expected(_)
            | K::UnexpectedChar(_)
            | K::UnexpectedEof
            | K::MissingField(_)
            | K::MissingAccount
            | K::MissingAmount
            | K::MissingCurrency
            | K::MissingDirective
            | K::IndentationError
            | K::MissingNewline
            | K::BomInDirectiveBody
            | K::InvalidDateValue(_)
            | K::InvalidDate(_)
            | K::UnclosedString
            | K::InvalidEscape(_)
    )
}

/// Whether `e` starts bison's recovery where rledger reports it: an error at
/// which beancount's grammar or lexer fails the statement
/// (`convert::fails_the_header`). A BOM diagnostic is decided by the token
/// beancount reads the BOM into ([`bom_is_invalid_token`]).
fn starts_recovery(e: &crate::ParseError) -> bool {
    !matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody)
        && super::convert::fails_the_header(e)
}

/// Whether beancount's lexer reads the BOM at `bom` into an invalid token
/// (`Invalid token: '<BOM>...'`, a `YYerror`), not into an account, a string
/// or a comment. `probe` is a lexer kept from the last call with the token it
/// is at: it reads on from there while that token starts at or before `bom`,
/// and restarts at `bom`'s line (`line_start`, outside any string) only when
/// it is past it, so over the ascending positions the errors give it, it
/// lexes each byte about once.
fn bom_is_invalid_token<'a>(
    probe: &mut Option<(BcLexer<'a>, (Bc, Range<usize>))>,
    src: &'a str,
    bom: usize,
    line_start: &dyn Fn(usize) -> usize,
) -> bool {
    let eof = || (Bc::Eof, src.len()..src.len());
    if probe.as_ref().is_none_or(|(_, (_, r))| r.start > bom) {
        let mut l = BcLexer::at_line_start(src, line_start(bom));
        let first = l.next().unwrap_or_else(eof);
        *probe = Some((l, first));
    }
    let Some((lexer, tok)) = probe.as_mut() else {
        return false;
    };
    while tok.1.end <= bom && tok.0 != Bc::Eof {
        *tok = lexer.next().unwrap_or_else(eof);
    }
    tok.0 == Bc::Error && tok.1.start <= bom
}

/// Drop the errors rledger reports where bison's recovery keeps beancount
/// quiet, and give the entry bison builds mid-line its own errors; see the
/// module docs. `errors` is sorted by start and stays so. Lexes the input
/// with [`BcLexer`] once, from the first error's line, and only when there is
/// an error.
pub(super) fn quiet_bison_recovery(
    errors: &mut Vec<crate::ParseError>,
    root: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    grammar_failures: &[(usize, usize, usize)],
) {
    use crate::SyntaxKind as K;
    use rowan::Language as _;
    if errors.is_empty() {
        return;
    }
    let off = bom_offset as usize;
    // Every invalid token, and every string that runs over a line end.
    let mut invalid: Vec<Range<usize>> = Vec::new();
    let mut multiline: Vec<Range<usize>> = Vec::new();
    let mut stack = vec![(root.green(), 0usize)];
    while let Some((node, start)) = stack.pop() {
        let mut pos = start;
        for el in node.children() {
            let len = usize::from(el.text_len());
            match el {
                rowan::NodeOrToken::Node(n) => stack.push((n, pos)),
                rowan::NodeOrToken::Token(t) => {
                    match crate::BeancountLanguage::kind_from_raw(t.kind()) {
                        K::ERROR_TOKEN => invalid.push(pos..pos + len),
                        K::STRING if t.text().contains('\n') => multiline.push(pos..pos + len),
                        _ => {}
                    }
                }
            }
            pos += len;
        }
    }
    invalid.sort_unstable_by_key(|r| r.start);
    // Where each top-level item's first content token starts, in order: an
    // indented line that starts one is no continuation of an entry, so
    // beancount fails at its indent there.
    let mut item_starts: Vec<usize> = Vec::new();
    let mut at_child = 0usize;
    for child in root.green().children() {
        let len = usize::from(child.text_len());
        if let rowan::NodeOrToken::Node(node) = child {
            let mut pos = at_child;
            for el in node.children() {
                if let rowan::NodeOrToken::Token(t) = el
                    && !super::convert::is_trivia_kind(crate::BeancountLanguage::kind_from_raw(
                        t.kind(),
                    ))
                {
                    item_starts.push(pos);
                    break;
                }
                pos += usize::from(el.text_len());
            }
        }
        at_child += len;
    }
    multiline.sort_unstable_by_key(|r| r.start);
    // The start of the line holding `at`, moved back past any multi-line
    // string that runs over it, so lexing starts outside a string.
    let line_start = |mut at: usize| loop {
        let ls = stripped[..at].rfind('\n').map_or(0, |i| i + 1);
        let i = multiline.partition_point(|r| r.start < ls);
        match i.checked_sub(1).map(|i| &multiline[i]) {
            Some(r) if r.end > ls => at = r.start,
            _ => return ls,
        }
    };
    // Each line that ends or starts what beancount's grammar continues with
    // an indented line, in order: `(line start, whether it is a dated
    // entry's header)`. A blank line (blanks only), and any line that starts
    // at column 0 outside a string: a dated line starts an entry whose
    // indented lines are its body; anything else (an undated directive, a
    // column-0 comment, a line beancount's lexer skips) takes none. One pass
    // over the input, only when there is an error.
    let mut blocks: Vec<(usize, bool)> = Vec::new();
    {
        let mut at = 0;
        while at < stripped.len() {
            let le = stripped[at..]
                .find('\n')
                .map_or(stripped.len(), |i| at + i + 1);
            let i = multiline.partition_point(|r| r.start < at);
            let in_string = i.checked_sub(1).is_some_and(|i| multiline[i].end > at);
            let line = &stripped[at..le];
            if in_string {
                at = le;
                continue;
            }
            if line.trim_matches([' ', '\t', '\r', '\n']).is_empty() {
                blocks.push((at, false));
            } else if !line.starts_with([' ', '\t']) {
                blocks.push((at, line.starts_with(|c: char| c.is_ascii_digit())));
            }
            at = le;
        }
        #[cfg(test)]
        crate::logos_lexer::test_counters::RECOVERY_SHIFT_SCANNED_BYTES
            .with(|c| c.set(c.get() + stripped.len()));
    }
    // Whether the indented line at `ls` continues a dated entry's body.
    let in_dated_entry = |ls: usize| {
        let i = blocks.partition_point(|&(start, _)| start < ls);
        i.checked_sub(1).is_some_and(|i| blocks[i].1)
    };
    // `(start, end, lexer errors there)`: stretches of the input where bison
    // is quiet.
    let mut segments: Vec<(usize, usize, usize)> = Vec::new();
    // Where each lexer error inside a quiet stretch starts, in order.
    let mut lexer_errors: Vec<(usize, usize)> = Vec::new();
    // Where each line starts whose grammar failure is its indent (an orphan
    // indented line bison fails at while not recovering), in order.
    let mut indent_failures: Vec<usize> = Vec::new();
    // Where bison is back at a `declarations` at a line start inside a dated
    // entry's body: after a statement it built there whole (an indented
    // `option "a" "b"`), so the indented line after it fails at its indent.
    let mut declarations_at: Option<usize> = None;
    // The line the last recovery window started at.
    let mut window_line: Option<usize> = None;
    // Where each error is that started no window (a BOM beancount does not
    // read into an invalid token, an invalid account on a line holding a
    // stray `\r`, a builder's error), in order.
    let mut unstarted: Vec<usize> = Vec::new();
    // Where each grammar failure counted in `lexer_errors` is that is known
    // to be bison's own (a column-0 statement failing among its first three
    // tokens, a body line failing at its first), not one only rledger's
    // grammar has.
    let mut certain_failures: Vec<usize> = Vec::new();
    // The last dated header looked up, and the token after its date (a
    // keyword, or a transaction's flag).
    let mut header_kind: Option<(usize, Option<Bc>)> = None;
    // The last indented line bison fails at, back at a `declarations` after
    // a statement it built whole in an entry's body, that rledger reads as
    // part of the entry and does not report.
    let mut unreported_indent: Option<usize> = None;
    // `(first, end, errors)`: an entry bison builds mid-line, whose errors
    // replace rledger's after the error that failed its line (`order[first..]`)
    // up to the end of its body.
    let mut phantoms: Vec<(usize, usize, usize, Vec<crate::ParseError>)> = Vec::new();
    // The failures bison reports where rledger has no error
    // (`undated_declaration_failure`).
    let mut synthetic: Vec<crate::ParseError> = Vec::new();
    let mut lexer: Option<BcLexer<'_>> = None;
    let mut peeked: Option<(Bc, Range<usize>)> = None;
    let mut resume = 0usize;
    let depth = PHANTOM_DEPTH.with(std::cell::Cell::get);
    // Where each error is, past the blank and comment lines a directive's
    // node (and so its whole-node error) takes in before its header: such an
    // error is about the header's line. Sorted like `errors` but for those.
    let effective: Vec<usize> = errors
        .iter()
        .map(|e| {
            let Some(mut at) = e.span.start.checked_sub(off) else {
                return 0;
            };
            // A dropped directive's whole-node error: where its header's
            // grammar fails, when that is known.
            let i = grammar_failures.partition_point(|g| g.0 < e.span.start);
            if let Some(&(_, _, failed)) = grammar_failures.get(i).filter(|g| g.0 == e.span.start)
                && failed != usize::MAX
                && failed >= off
            {
                return failed - off;
            }
            let end = e.span.end.saturating_sub(off).min(stripped.len());
            while at < end && (at == 0 || stripped.as_bytes()[at - 1] == b'\n') {
                let line_end = stripped[at..].find('\n').map_or(stripped.len(), |i| at + i);
                let line = &stripped[at..line_end];
                // A blank line, or a comment at the line's start; an
                // indented comment is an INDENT to beancount.
                // (Not one holding a stray `\r`, which this parser may read
                // as more than a comment, #2980.)
                let skipped = (line.trim_matches([' ', '\t', '\r']).is_empty()
                    || line.starts_with(';'))
                    && !super::convert::holds_a_stray_cr(
                        &stripped[at..(line_end + 1).min(stripped.len())],
                    );
                if !skipped || line_end >= end {
                    break;
                }
                at = line_end + 1;
            }
            // One at a string that runs over line ends is reported on the line
            // the string ends (`report_at_multi_line_string_ends`, after this
            // pass), as beancount reports it.
            let i = multiline.partition_point(|r| r.start < at);
            if let Some(r) = multiline.get(i).filter(|r| r.start == at) {
                return stripped[..r.end].rfind('\n').map_or(at, |n| n + 1);
            }
            at
        })
        .collect();
    let mut order: Vec<usize> = (0..errors.len()).collect();
    order.sort_by_key(|&i| effective[i]);
    // A lexer of its own, run forward only, to read the token a BOM
    // diagnostic is at (`bom_is_invalid_token`).
    let mut probe: Option<(BcLexer<'_>, (Bc, Range<usize>))> = None;
    for (oi, &k) in order.iter().enumerate() {
        let e = &errors[k];
        if e.span.start < off {
            continue;
        }
        let at = effective[k];
        if at < resume || at > stripped.len() {
            continue;
        }
        // A BOM diagnostic stands for beancount's `Invalid token` error when
        // beancount's lexer reads that BOM into an invalid token, whose
        // `YYerror` starts bison's recovery as any lexer error does (`\t<BOM>`
        // is read as `\t$` is). Not when the BOM is read into an account, a
        // string or a comment, nor on a line holding a stray `\r` (below),
        // where the line's other errors decide, as before.
        let starts = if matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody) {
            let end = e.span.end.saturating_sub(off).min(stripped.len());
            let ls = stripped[..at].rfind('\n').map_or(0, |i| i + 1);
            let le = stripped[at..]
                .find('\n')
                .map_or(stripped.len(), |i| at + i + 1);
            !super::convert::holds_a_stray_cr(&stripped[ls..le])
                && stripped
                    .get(at..end)
                    .and_then(|s| s.find(crate::bom::BOM_CHAR))
                    .is_some_and(|i| {
                        bom_is_invalid_token(&mut probe, stripped, at + i, &line_start)
                    })
        } else if matches!(e.kind, crate::ParseErrorKind::InvalidAccount(_)) {
            // An invalid account is rledger's line error for a line it cannot
            // read, named for the account on it: bison fails on that line as
            // on any other (where its lexer reads the account into an
            // `ACCOUNT`, the grammar fails there or later; where into an
            // invalid token, its `YYerror` starts the recovery). Not on a line
            // holding a stray `\r` (#2980), where no recovery is modeled and
            // the lines after keep their errors, as before.
            let ls = stripped[..at].rfind('\n').map_or(0, |i| i + 1);
            let le = stripped[at..]
                .find('\n')
                .map_or(stripped.len(), |i| at + i + 1);
            !super::convert::holds_a_stray_cr(&stripped[ls..le])
        } else {
            starts_recovery(e)
        };
        if !starts {
            unstarted.push(at);
            continue;
        }
        // The lexer restarts at the error's line unless it is still before
        // it: a statement a window ended at is read again from its start.
        let start_of_line = line_start(at);
        let behind = lexer.as_ref().is_none_or(|l| {
            let pos = peeked.as_ref().map_or(l.pos(), |(_, r)| r.start);
            pos > start_of_line
        });
        if behind {
            lexer = Some(BcLexer::at_line_start(stripped, start_of_line));
            peeked = None;
        }
        let Some(lx) = lexer.as_mut() else { continue };
        let mut next = |peeked: &mut Option<(Bc, Range<usize>)>| {
            peeked
                .take()
                .or_else(|| lx.next())
                .unwrap_or((Bc::Eof, stripped.len()..stripped.len()))
        };
        // A line holding a stray `\r` is read differently here and in
        // beancount (#2980): an error there may be none to beancount, so no
        // recovery is started from it.
        let ls = stripped[..at].rfind('\n').map_or(0, |i| i + 1);
        let le = stripped[at..]
            .find('\n')
            .map_or(stripped.len(), |i| at + i + 1);
        if super::convert::holds_a_stray_cr(&stripped[ls..le]) {
            // Nor from one on the next line with content, which beancount
            // may still be recovering from such a line on.
            let mut next_end = le;
            while next_end < stripped.len() {
                let e2 = stripped[next_end..]
                    .find('\n')
                    .map_or(stripped.len(), |i| next_end + i + 1);
                let blank = stripped[next_end..e2]
                    .trim_matches([' ', '\t', '\r', '\n'])
                    .is_empty();
                next_end = e2;
                if !blank {
                    break;
                }
            }
            resume = resume.max(next_end);
            continue;
        }
        // The token bison fails at: the indent of an indented line that
        // starts a top-level item where the error is at its content (a
        // `declarations` takes no `INDENT`), else the token at the error.
        let content =
            ls + (stripped[ls..].len() - stripped[ls..].trim_start_matches([' ', '\t']).len());
        // An error in a line's indentation is about its first token.
        let error_at = at;
        let at = at.max(content.min(le));
        // An indented line rledger reads as an item of its own: beancount
        // fails at its indent, unless the line before is a dated header,
        // whose entry takes it (`2024-01-01 open Assets:A` then `  Z`).
        let after_dated_header = ls > 0 && {
            let ps = stripped[..ls - 1].rfind('\n').map_or(0, |i| i + 1);
            stripped[ps..].starts_with(|c: char| c.is_ascii_digit())
        };
        // So does one bison meets back at a `declarations`, after a statement
        // it built whole in an entry's body, though rledger reads that line as
        // part of the entry (`  option "a" "b"` then `  $x`).
        let after_declarations = declarations_at == Some(ls);
        let orphan_indent = content > ls
            && at == content
            && (after_declarations
                || item_starts.binary_search(&content).is_ok() && !after_dated_header);
        // Whether bison reports that indent: not in a dated entry's body
        // past its header's line either (after a metadata line or an
        // indented comment there), unless a statement it built in the body
        // left it at a `declarations`.
        let indent_reported = orphan_indent && (!in_dated_entry(ls) || declarations_at == Some(ls));
        // Unless beancount is still recovering from the indent of an
        // indented comment rledger accepts on purpose, just before
        // (`before_orphan_indent`): bison is quiet at this indent, and the
        // line has its lexer errors only. After a line with a stray `\r` or a
        // BOM, where no recovery is modeled, rledger's errors decide, as
        // before.
        //
        // An indented line in a dated entry's body (`2024-01-01 open
        // Assets:A` then `  open $`): after the indent, bison takes a key or a
        // line end there, and in a transaction's body also a tag, a link, a
        // flag or an account, and fails at anything else.
        let body_of = if !orphan_indent && content > ls && in_dated_entry(ls) {
            let i = blocks.partition_point(|&(start, _)| start < ls);
            let header = i.checked_sub(1).map_or(0, |i| blocks[i].0);
            match header_kind {
                Some((looked_up, kind)) if looked_up == header => kind,
                _ => {
                    let mut l = BcLexer::at_line_start(stripped, header);
                    let kind = if l.next().is_some_and(|(t, _)| t == Bc::Date) {
                        l.next().map(|(t, _)| t)
                    } else {
                        None
                    };
                    header_kind = Some((header, kind));
                    kind
                }
            }
        } else {
            None
        };
        let body_takes = |t: Bc| match body_of {
            Some(Bc::Kw(_)) => t == Bc::Key,
            Some(Bc::Txn | Bc::Flag | Bc::Asterisk | Bc::Hash | Bc::Capital) => matches!(
                t,
                Bc::Key
                    | Bc::Tag
                    | Bc::Link
                    | Bc::Account
                    | Bc::Flag
                    | Bc::Asterisk
                    | Bc::Hash
                    | Bc::Capital
            ),
            _ => true,
        };
        // (Read for a column-0 line and a body line too, whose failure
        // counts as bison's own only where bison is reporting there.)
        let before_line = if orphan_indent || content == ls || body_of.is_some() {
            before_orphan_indent(stripped, ls, window_line, unreported_indent, &unstarted)
        } else {
            Before::Reporting
        };
        let before_indent = if orphan_indent {
            before_line
        } else {
            Before::Reporting
        };
        window_line = Some(ls);
        let shadowed = matches!(before_indent, Before::AcceptedComment | Before::Unreported);
        // The tokens on the line before it.
        let mut before: Vec<(Bc, Range<usize>)> = Vec::new();
        let mut tok = loop {
            let t = next(&mut peeked);
            if orphan_indent && t.0 == Bc::Indent && t.1.start == ls {
                break t;
            }
            if t.1.end > at || t.0 == Bc::Eof {
                break t;
            }
            if t.1.start >= ls {
                before.push(t);
            }
        };
        // A column-0 statement whose error rledger puts at a token bison
        // still takes (a whole-line error at its date): bison fails at the
        // first token among its first three that is invalid or that it does
        // not take (`2024-01-02 2024-13-45 "n"` fails at the invalid date).
        if content == ls {
            let mut kinds: Vec<Bc> = before.iter().map(|&(t, _)| t).collect();
            let mut reads = kinds
                .iter()
                .enumerate()
                .all(|(i, &t)| accepts(&kinds[..i], t));
            while reads
                && kinds.len() < 3
                && !matches!(tok.0, Bc::Error | Bc::Eol | Bc::Eof)
                && accepts(&kinds, tok.0)
            {
                kinds.push(tok.0);
                before.push(tok);
                tok = next(&mut peeked);
                reads = true;
            }
        }
        if indent_reported && before_indent == Before::Reporting && tok.0 == Bc::Indent {
            indent_failures.push(ls);
        }
        let mut status = 3u8;
        let mut prefix: Vec<(Bc, usize)> = Vec::new();
        // The rest of the failed line, from the error, is quiet too but for
        // the error itself: a grammar failure counts as one error there.
        let from = tok.1.start.min(error_at);
        // A grammar failure counts once more, unless the line's first token
        // is the invalid one it fails at: rledger's error may start past the
        // grammar's real failure point (`Assets:A ! 1 USD x`).
        let reads_up_to_it = if content > ls {
            posting_prefix_reads(&before, stripped)
        } else {
            // A column-0 statement: its first three tokens, as far as the
            // recovery's grammar knows them; past those it is taken to read.
            let mut kinds: Vec<Bc> = Vec::new();
            before.iter().take(3).all(|&(t, _)| {
                let ok = accepts(&kinds, t);
                kinds.push(t);
                ok
            })
        };
        if !(tok.0 == Bc::Error && reads_up_to_it || shadowed) {
            // On the line bison reports it: where the error is (a string that
            // runs over line ends is reported where it ends).
            lexer_errors.push((at, at));
            // Known to be bison's own failure: a column-0 statement that fails
            // at a token among its first three, which the recovery's grammar
            // knows whole, where nothing before keeps bison recovering.
            if content == ls
                && before_line == Before::Reporting
                && before.len() < 3
                && !matches!(tok.0, Bc::Error | Bc::Eol | Bc::Eof)
            {
                let kinds: Vec<Bc> = before.iter().map(|&(t, _)| t).collect();
                if (0..kinds.len()).all(|i| accepts(&kinds[..i], kinds[i]))
                    && !accepts(&kinds, tok.0)
                {
                    certain_failures.push(at);
                }
            }
            // So is a body line's that fails at its first token.
            if body_of.is_some()
                && before_line == Before::Reporting
                && matches!(before.as_slice(), [(Bc::Indent, _)])
                && !matches!(tok.0, Bc::Error | Bc::Eol | Bc::Eof)
                && !body_takes(tok.0)
            {
                certain_failures.push(at);
            }
        }
        let mut segment: Option<(usize, usize)> = Some((from, k));
        let mut first = true;
        let mut resumed_at: Option<(usize, usize)> = None;
        let mut on_failure_line = true;
        // Whether the last stretch pushed ends inside an entry bison starts
        // mid-line: dropped again where that entry is not modeled.
        let mut partial = false;
        loop {
            let (t, r) = tok.clone();
            // Whether this line end closed a stretch: the line an entry bison
            // starts mid-line ends here when its third token is this `EOL`.
            let mut closed_here = false;
            if t == Bc::Eol {
                if let Some((s, n)) = segment.take()
                    && r.start > s
                {
                    segments.push((s, r.start, n));
                    closed_here = true;
                }
                segment = Some((r.end, usize::MAX));
                on_failure_line = false;
            }
            if t == Bc::Eof {
                let kinds: Vec<Bc> = prefix.iter().map(|&(k, _)| k).collect();
                // The end of the input as the `eol` that completes a pop
                // bison started mid-line (`| poptag #t` at the end): beancount
                // reports the pop of a tag never pushed there, which is not
                // modeled, so its line keeps its errors.
                let completes_unaligned = status == 1
                    && !first
                    && accepts(&kinds, t)
                    && prefix.first().is_some_and(|&(k, st)| {
                        matches!(k, Bc::Kw(Kw::Poptag | Kw::Popmeta))
                            && st != 0
                            && stripped.as_bytes()[st - 1] != b'\n'
                    });
                if let Some((s, n)) = segment.take()
                    && stripped.len() > s
                    && !completes_unaligned
                {
                    segments.push((s, stripped.len(), n));
                }
                break;
            }
            let kinds: Vec<Bc> = prefix.iter().map(|&(k, _)| k).collect();
            let shift = if t == Bc::Error {
                if segment.is_some() {
                    lexer_errors.push((r.start, r.end));
                }
                status = 3;
                prefix.clear();
                false
            } else if !first && accepts(&kinds, t) {
                true
            } else if first || (status == 3 && prefix.is_empty()) {
                prefix.clear();
                status = 3;
                accepts(&[], t)
            } else {
                status = 3;
                prefix.clear();
                accepts(&[], t)
            };
            first = false;
            if shift {
                if !(t == Bc::Eol && prefix.is_empty()) {
                    prefix.push((t, r.start));
                }
                status -= 1;
                if status == 0 {
                    let stmt = prefix.first().map_or(r.start, |&(_, s)| s);
                    resumed_at = Some((r.end, stmt));
                    // A statement that starts a line is the one rledger
                    // parses there, so its errors are where it fails after
                    // these three tokens: reported. An entry bison starts
                    // mid-line is quiet up to its third token.
                    let aligned = stmt == 0 || stripped.as_bytes()[stmt - 1] == b'\n';
                    // An undated declaration bison starts mid-line that fails
                    // past these three tokens (`popmeta pushmeta kk: @`): it
                    // builds nothing, so changes no state; bison reports that
                    // failure (an invalid token there is its lexer's error
                    // only) and starts its recovery over at it, at status
                    // three. The failure is rledger's next error on the line
                    // if it has one there, else one is added.
                    let kinds: Vec<Bc> = prefix.iter().map(|&(k, _)| k).collect();
                    if !aligned
                        && depth == 0
                        && let Some((failed, at_token)) =
                            undated_declaration_failure(stripped, &kinds, r.end)
                    {
                        if let Some((s, n)) = segment.take()
                            && r.end > s
                        {
                            segments.push((s, r.end, n));
                        }
                        tok = loop {
                            let t = next(&mut peeked);
                            if t.1.start >= at_token.start || matches!(t.0, Bc::Eol | Bc::Eof) {
                                break t;
                            }
                        };
                        let mut trigger = usize::MAX;
                        if failed != Bc::Error {
                            // (One of rledger's at that very token, not one
                            // standing for a later invalid token or date.)
                            let j = order.partition_point(|&j| effective[j] < at_token.start);
                            if let Some(&j) = order.get(j).filter(|&&j| {
                                effective[j] < at_token.end
                                    && is_droppable(&errors[j])
                                    && !is_lexer_kind(&errors[j], effective[j], &invalid)
                            }) {
                                trigger = j;
                                lexer_errors.push((at_token.start, at_token.start));
                            } else {
                                synthetic.push(undated_failure_error(
                                    stripped,
                                    kinds[0],
                                    at_token.clone(),
                                    off,
                                ));
                            }
                        }
                        segment = Some((at_token.start, trigger));
                        status = 3;
                        prefix.clear();
                        resumed_at = None;
                        first = true;
                        continue;
                    }
                    // An entry bison starts mid-line whose own line holds an
                    // invalid token after these three (`<BOM>g 2024-01-02 *
                    // "n" $x`): that token's `YYerror` drops the entry, after
                    // any grammar failure before it, reported, and starts the
                    // recovery over. So the line has the errors the entry's
                    // line parsed on its own has (#2979), and the window goes
                    // on from the line's end, past the entry's indented lines.
                    let line_end = stripped[r.end..]
                        .find('\n')
                        .map_or(stripped.len(), |i| r.end + i + 1);
                    let invalid_on_line = !aligned
                        && depth == 0
                        && t != Bc::Eol
                        && prefix.first().is_some_and(|&(k, _)| k == Bc::Date)
                        && line_holds_an_invalid_token(stripped, r.end)
                        && !super::convert::holds_a_stray_cr(&stripped[stmt..line_end]);
                    if let Some(errs) = invalid_on_line
                        .then(|| phantom_errors(stripped, stmt..line_end, off, depth))
                        .flatten()
                    {
                        if let Some((s, n)) = segment.take()
                            && r.end > s
                        {
                            segments.push((s, r.end, n));
                        }
                        let first = if on_failure_line {
                            oi + 1
                        } else {
                            order.partition_point(|&j| effective[j] < r.end)
                        };
                        phantoms.push((first, r.end, line_end, errs));
                        status = 3;
                        prefix.clear();
                        resumed_at = None;
                        tok = loop {
                            let t = next(&mut peeked);
                            if matches!(t.0, Bc::Eol | Bc::Eof) {
                                break t;
                            }
                        };
                        continue;
                    }
                    let quiet_to = if aligned { stmt } else { r.end };
                    partial = !aligned && closed_here;
                    if let Some((s, n)) = segment.take()
                        && quiet_to > s
                    {
                        segments.push((s, quiet_to, n));
                        partial = !aligned;
                    }
                    break;
                }
            }
            tok = next(&mut peeked);
        }
        // Still recovering at the end of the input: nothing after is reported.
        let Some((end, stmt)) = resumed_at else {
            break;
        };
        resume = end;
        let aligned = stmt == 0 || stripped.as_bytes()[stmt - 1] == b'\n';
        if aligned {
            // The statement is the one rledger parses there: its own errors,
            // its whole-node one included, are where it fails.
            resume = stmt;
            continue;
        }
        let dated = prefix.first().map(|&(k, _)| k) == Some(Bc::Date);
        // An `option`, `include` or `plugin` bison builds on a later line of
        // the window: it changes no state rledger reports on, so when its line
        // ends right after it, that line is quiet to its end and bison reads
        // on from a `declarations`, as rledger does after the line.
        // Only one bison has read whole: `option` with its two strings,
        // `include` or `plugin` with their string.
        let kinds: Vec<Bc> = prefix
            .iter()
            .map(|&(k, _)| k)
            .filter(|&k| k != Bc::Eol)
            .collect();
        let stateless = matches!(
            kinds.as_slice(),
            [Bc::Kw(Kw::Option | Kw::Plugin), Bc::Str, Bc::Str]
                | [Bc::Kw(Kw::Include | Kw::Plugin), Bc::Str]
        );
        // Not when an indented line follows: bison, back at a `declarations`,
        // reports its indent, where rledger may read a posting.
        if stateless && partial {
            let at_eol = prefix.last().is_some_and(|&(k, _)| k == Bc::Eol);
            let t = if at_eol {
                (Bc::Eol, end..end)
            } else {
                next(&mut peeked)
            };
            if matches!(t.0, Bc::Eol | Bc::Eof) {
                let after = if t.0 == Bc::Eof {
                    (Bc::Eof, t.1.clone())
                } else {
                    next(&mut peeked)
                };
                // ... unless rledger reports that line too, which then stands
                // for bison's error at its indent. Not inside an entry parsed
                // on its own here, where that line is a posting of rledger's.
                let indented_next = after.0 == Bc::Indent
                    && (depth > 0 || {
                        let next_end = stripped[after.1.start..]
                            .find('\n')
                            .map_or(stripped.len(), |i| after.1.start + i);
                        let i = order.partition_point(|&j| effective[j] < after.1.start);
                        order.get(i).is_none_or(|&j| effective[j] > next_end)
                    });
                if indented_next && after.0 == Bc::Indent {
                    unreported_indent = Some(after.1.start);
                }
                peeked = Some(after);
                if !indented_next {
                    if !at_eol && let Some(last) = segments.last_mut() {
                        last.1 = t.1.start;
                    }
                    resume = t.1.end;
                    declarations_at = Some(resume);
                    continue;
                }
            } else {
                peeked = Some(t);
            }
        }
        if depth > 0 || !dated {
            // A declaration bison shifts mid-line inside an entry already
            // built that way, or an undated one (`$ pushtag #a`, whose state
            // change is not modeled): rledger's errors stay from its line on.
            UNMODELED_PHANTOM.with(|u| u.set(true));
            if partial {
                segments.pop();
            }
        }
        if !dated {
            continue;
        }
        // An entry bison builds mid-line or on an indented line (#2979): its
        // body is the indented lines right after its line.
        let mut body_end = end;
        let mut line_done = prefix.last().is_some_and(|&(k, _)| k == Bc::Eol);
        // An invalid token on the entry's own line, where that line was not
        // parsed on its own above (nested, or holding a stray `\r`, or a
        // declaration bison shifts in it): the entry is not modeled.
        let mut header_invalid = false;
        loop {
            let t = next(&mut peeked);
            if t.0 == Bc::Error && !line_done && body_end == end {
                header_invalid = true;
            }
            match t.0 {
                Bc::Eof => {
                    body_end = stripped.len();
                    break;
                }
                Bc::Eol => {
                    body_end = t.1.end;
                    line_done = true;
                }
                Bc::Indent if line_done => line_done = false,
                _ if line_done => {
                    peeked = Some(t);
                    break;
                }
                _ => {}
            }
        }
        // Nested, or holding a stray `\r`, which this parser reads
        // differently from beancount (#2980): rledger's errors stay there.
        if depth > 0
            || header_invalid
            || super::convert::holds_a_stray_cr(&stripped[stmt..body_end])
        {
            if partial {
                segments.pop();
            }
            resume = body_end;
            continue;
        }
        let Some(errs) = phantom_errors(stripped, stmt..body_end, off, depth) else {
            if partial {
                segments.pop();
            }
            resume = body_end;
            continue;
        };
        // On the line that failed, rledger's errors after the failing one
        // are about the entry; on a later line, the quiet stretch before the
        // entry's third token is already counted (`segments`).
        let first = if on_failure_line {
            oi + 1
        } else {
            order.partition_point(|&j| effective[j] < end)
        };
        phantoms.push((first, end, body_end, errs));
        resume = body_end;
    }
    if segments.is_empty() && phantoms.is_empty() {
        return;
    }
    let mut dropped = vec![false; errors.len()];
    // Line by line (beancount reports a lexer error on the line its token
    // is on), each quiet line keeps as many of rledger's errors as beancount's
    // lexer finds there, its invalid-token errors first.
    lexer_errors.sort_unstable();
    certain_failures.sort_unstable();
    let mut added = synthetic;
    let mut next_error = 0;
    for &(seg_start, seg_end, trigger) in &segments {
        let mut line_from = seg_start;
        while line_from < seg_end {
            let line_to = stripped[line_from..seg_end]
                .find('\n')
                .map_or(seg_end, |nl| line_from + nl + 1);
            while next_error < order.len() && effective[order[next_error]] < line_from {
                next_error += 1;
            }
            let mut scan = next_error;
            let mut candidates = Vec::new();
            while scan < order.len() && effective[order[scan]] < line_to {
                if is_droppable(&errors[order[scan]]) {
                    candidates.push(order[scan]);
                }
                scan += 1;
            }
            next_error = scan;
            let (la, lb) = (
                lexer_errors.partition_point(|&(tok_start, _)| tok_start < line_from),
                lexer_errors.partition_point(|&(tok_start, _)| tok_start < line_to),
            );
            let mut keep = lb - la;
            // The error that failed the line first, then rledger's
            // invalid-token errors, then the rest.
            for pass in 0..3 {
                for &cand in &candidates {
                    let rank = if cand == trigger {
                        0
                    } else if is_lexer_kind(&errors[cand], effective[cand], &invalid) {
                        1
                    } else {
                        2
                    };
                    if rank != pass {
                        continue;
                    }
                    if keep > 0 {
                        keep -= 1;
                    } else {
                        dropped[cand] = true;
                    }
                }
            }
            // Fewer errors than beancount's lexer finds: an invalid token this
            // parser reads as something else (a lone capital glued to a `\r`
            // or to the end of the input, #3028), or a number beancount's lexer
            // rejects (`1,50`, `ValueError: Invalid number format`), which
            // this parser reads as a number and a comma, is reported as
            // beancount does. Only beyond the line's real invalid tokens: the
            // grammar error counted for its failure may stand where rledger
            // has none. And only on a line with a few invalid tokens and no
            // BOM: on a long run of them (a fuzz-corpus line of thirty), or
            // with a BOM whose diagnostic this parser counts its own way
            // (#2956), the two lexers' runs part, and the count with them.
            // But for the BOM run whose diagnostic failed the line (the
            // window's own start), and a BOM beancount reads as an invalid
            // token of its own: each is one token on both sides.
            let real_errors = || {
                lexer_errors[la..lb]
                    .iter()
                    .filter(|&&(tok_start, tok_end)| tok_end > tok_start)
            };
            let real = real_errors().count();
            let bom_trigger = trigger != usize::MAX
                && matches!(
                    errors[trigger].kind,
                    crate::ParseErrorKind::BomInDirectiveBody
                );
            let trigger_run = real_errors().next().filter(|_| bom_trigger);
            let simple = real <= 4
                && stripped[line_from..line_to]
                    .match_indices(crate::bom::BOM_CHAR)
                    .all(|(i, _)| {
                        let at = line_from + i;
                        trigger_run.is_some_and(|&(s, e)| (s..e).contains(&at))
                            || real_errors().any(|&(s, e)| s == at && e == at + crate::bom::BOM_LEN)
                    });
            // An orphan indented line that failed at its indent
            // (`syntax error, unexpected INDENT`), whose error here stands
            // for that failure: beancount's lexer errors on it are each one
            // more error (`  $x` is two), where rledger's line error stands
            // for the line's first invalid token too. Each one rledger has no
            // error of its own for is added, as named as the line's later
            // ones are, so the line reports which token is invalid.
            let indent_line = trigger != usize::MAX
                && candidates.contains(&trigger)
                && indent_failures.binary_search(&line_from).is_ok();
            let mut keep = if !simple {
                0
            } else if indent_line {
                keep
            } else {
                // Each of rledger's errors there stands for one of those
                // tokens, but for the one that failed the line, when it is
                // counted for the line's grammar failure.
                let failure_counted = trigger != usize::MAX
                    && candidates.contains(&trigger)
                    && lexer_errors[la..lb]
                        .iter()
                        .any(|&(s, e)| s == e && certain_failures.binary_search(&s).is_ok());
                keep.min(real.saturating_sub(candidates.len() - usize::from(failure_counted)))
            };
            // Where the error that failed the line is rledger's own report of
            // the line's first invalid token (a line it reads as part of the
            // entry before, `  option "a" "b"` then `  $x`), that token is
            // named already: what is missing is the indent's error.
            let trigger_names_a_token = indent_line && names_an_invalid_token(&errors[trigger]);
            if trigger_names_a_token && keep > 0 {
                let indent = stripped[line_from..line_to].len()
                    - stripped[line_from..line_to]
                        .trim_start_matches([' ', '\t'])
                        .len();
                added.push(crate::ParseError::new(
                    crate::ParseErrorKind::SyntaxError(
                        "unexpected indent: no entry continues on this line".to_string(),
                    ),
                    crate::Span::new(line_from + off, line_from + indent + off),
                ));
                keep -= 1;
            }
            for &(tok_start, tok_end) in &lexer_errors[la..lb] {
                if keep == 0 {
                    break;
                }
                let at_or_after = order.partition_point(|&scan| effective[scan] < tok_start);
                // (A zero-width one is the failure of the line, no token.)
                let text = &stripped[tok_start..tok_end];
                let Some(&first) = text.as_bytes().first() else {
                    continue;
                };
                let lone_capital = text.len() == 1 && first.is_ascii_uppercase();
                // A lexer error that starts with a digit is an invalid date or
                // a misgrouped number; only the date has a `-` or a `/`.
                let misgrouped_number = first.is_ascii_digit()
                    && text
                        .bytes()
                        .all(|b| b.is_ascii_digit() || matches!(b, b',' | b'.'));
                // Not one rledger already reads into an invalid token of its
                // own, or reports an error at.
                // On an indent line the line error is the indent's, and covers
                // no token (nor does an invalid token rledger merged into it);
                // a BOM's own diagnostic already names it.
                let covered = if indent_line {
                    text.contains(crate::bom::BOM_CHAR)
                        || order[at_or_after..]
                            .iter()
                            .take_while(|&&scan| effective[scan] < tok_end)
                            .any(|&scan| scan != trigger || trigger_names_a_token)
                } else {
                    order
                        .get(at_or_after)
                        .is_some_and(|&scan| effective[scan] < tok_end)
                        || {
                            let next_error = invalid.partition_point(|run| run.start <= tok_start);
                            next_error
                                .checked_sub(1)
                                .is_some_and(|next_error| invalid[next_error].end > tok_start)
                        }
                };
                if covered {
                    continue;
                }
                let kind = if lone_capital {
                    crate::ParseErrorKind::SyntaxError(format!(
                        "unexpected input: invalid token '{}'",
                        super::convert::invalid_token_name(text)
                    ))
                } else if misgrouped_number {
                    crate::ParseErrorKind::InvalidNumber(text.to_string())
                } else if indent_line && !first.is_ascii_digit() {
                    // (One that starts with a digit is an invalid date, which
                    // rledger reports wherever it stands.)
                    crate::ParseErrorKind::SyntaxError(format!(
                        "unexpected input: invalid token '{}'",
                        super::convert::invalid_token_name(text)
                    ))
                } else {
                    continue;
                };
                added.push(crate::ParseError::new(
                    kind,
                    crate::Span::new(tok_start + off, tok_end + off),
                ));
                keep -= 1;
            }
            line_from = line_to;
        }
    }
    for (s, quiet_to, e, errs) in phantoms {
        let from = s;
        let to = order.partition_point(|&k| effective[k] < e).max(from);
        // The errors replaced, by span: one the entry's own parse reports
        // over the same span is rledger's own (an invalid token, named as
        // the whole file's parse names it), kept instead.
        let mut replaced: std::collections::HashMap<(usize, usize), Vec<usize>> =
            std::collections::HashMap::new();
        for &k in &order[from..to] {
            // Before the entry's third token bison is still recovering: its
            // lexer's errors there are reported.
            let lexer_error =
                effective[k] < quiet_to && is_lexer_kind(&errors[k], effective[k], &invalid);
            // Every error but the file's push/pop state: the entry's own parse
            // reports them (a deprecated pipe included).
            if errors[k].span.start >= off && !is_push_pop_state(&errors[k]) && !lexer_error {
                if !dropped[k] {
                    replaced
                        .entry((errors[k].span.start, errors[k].span.end))
                        .or_default()
                        .push(k);
                }
                dropped[k] = true;
            }
        }
        for x in errs {
            match replaced
                .get_mut(&(x.span.start, x.span.end))
                .and_then(Vec::pop)
            {
                Some(k) => dropped[k] = false,
                None => added.push(x),
            }
        }
    }
    let mut index = 0;
    errors.retain(|_| {
        let keep = !dropped[index];
        index += 1;
        keep
    });
    if !added.is_empty() {
        errors.extend(added);
        errors.sort_by_key(|x| x.span.start);
    }
}

/// Whether `e` is a line error renamed for the line's first invalid token
/// (`unexpected input: invalid token '$x'`, by
/// `convert::drop_errors_inside_a_line_error`), so it names that token.
fn names_an_invalid_token(e: &crate::ParseError) -> bool {
    matches!(&e.kind, crate::ParseErrorKind::SyntaxError(m) if m.starts_with("unexpected input: invalid token '"))
}

/// What the lines before an orphan indented line say about bison's state at
/// its indent ([`before_orphan_indent`]).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Before {
    /// Nothing that keeps bison recovering: it reports the indent.
    Reporting,
    /// A run of indented `;` comments after a gap, which rledger accepts on
    /// purpose: bison failed at its indent and is still recovering.
    AcceptedComment,
    /// An indented line bison fails at, which rledger reads as part of the
    /// entry before it (after an `option "a" "b"` bison built there): bison
    /// is still recovering from that line's indent.
    Unreported,
    /// A line holding a stray `\r` or a BOM, which this parser reads
    /// differently from beancount (#2980, #2956), or an error from which no
    /// recovery is modeled: unknown.
    Unmodeled,
}

/// Whether bison may still be recovering at the indent of the orphan
/// indented line starting at `ls` (or at the start of the column-0 line
/// there), read back from it over the lines after
/// `floor`, the line the last recovery window started at (from there on the
/// window decided).
///
/// An indented line's indent is an error to bison (one it reports only when
/// it is not recovering), and its line end one shift; a gap line (a blank
/// line, a line beancount's lexer skips at column 0) is a shift. So from the
/// last indented line before `ls`, two gap lines end a recovery, and an
/// indented line in between starts the count over, unless bison shifts three
/// tokens on it (`recovery_ends_on_line`: a statement that starts there),
/// which ends the recovery. Read
/// back that way, the run of lines `ls` is in starts at:
///
/// - an indented `;` comment after a gap or at the top of the file, which
///   rledger accepts on purpose, where beancount fails at its indent
///   (`syntax error, unexpected INDENT`, which the parity harness drops,
///   `is_indented_comment_indent_error`): bison is still recovering at `ls`,
///   so its indent is discarded in silence (`  ; c` then `  $x` is one error
///   on the `$x` line; with two blank lines between, two);
/// - `unreported`, an indented line bison fails at that rledger does not
///   report: the same;
/// - anything else (a column-0 statement, an indented line that ends the
///   recovery, two gap lines, the top of the file, `floor`), where rledger's
///   own errors decide, as before.
///
/// Unless one of the four lines before `ls` holds a stray `\r`, a BOM or an
/// error of rledger's that started no window (`unstarted`), whose own
/// failure may still keep bison recovering at `ls`, unmodeled.
///
/// Calls come in ascending order, each with the last one's line as its
/// `floor`, so each line is read about once.
fn before_orphan_indent(
    src: &str,
    ls: usize,
    floor: Option<usize>,
    unreported: Option<usize>,
    unstarted: &[usize],
) -> Before {
    let line_before = |end: usize| {
        let ps = src[..end - 1].rfind('\n').map_or(0, |i| i + 1);
        (ps, &src[ps..end])
    };
    let indented_comment = |line: &str| {
        let rest = line.trim_start_matches([' ', '\t']);
        rest.len() < line.len() && rest.starts_with(';')
    };
    // A blank line, a `;` comment at column 0, or a line beancount's lexer
    // skips there: `*`, `:`, `#` or a flag character with more after it (not
    // a `#` starting a tag).
    let gap = |line: &str| {
        let b = line.as_bytes();
        line.trim_matches([' ', '\t', '\r', '\n']).is_empty()
            || line.starts_with(';')
            || (b.len() >= 2
                && b"*:#!&?%".contains(&b[0])
                && !matches!(b[1], b'\r' | b'\n')
                && !(b[0] == b'#' && (b[1].is_ascii_alphanumeric() || b"-_/.".contains(&b[1]))))
    };
    let mut end = ls;
    for _ in 0..4 {
        if end == 0 {
            break;
        }
        let (ps, line) = line_before(end);
        if floor == Some(ps) {
            break;
        }
        if super::convert::holds_a_stray_cr(line) || line.contains(crate::bom::BOM_CHAR) {
            return Before::Unmodeled;
        }
        end = ps;
    }
    let i = unstarted.partition_point(|&at| at < end);
    if unstarted.get(i).is_some_and(|&at| at < ls) {
        return Before::Unmodeled;
    }
    let mut end = ls;
    let mut gaps = 0;
    loop {
        if end == 0 {
            return Before::Reporting;
        }
        let (ps, line) = line_before(end);
        if floor == Some(ps) {
            return Before::Reporting;
        }
        #[cfg(test)]
        crate::logos_lexer::test_counters::RECOVERY_SHIFT_SCANNED_BYTES
            .with(|c| c.set(c.get() + line.len()));
        if gap(line) {
            gaps += 1;
            if gaps == 2 {
                return Before::Reporting;
            }
        } else if unreported == Some(ps) {
            return Before::Unreported;
        } else if indented_comment(line) {
            if ps == 0 || gap(line_before(ps).1) {
                return Before::AcceptedComment;
            }
            gaps = 0;
        } else if line.starts_with([' ', '\t']) && !recovery_ends_on_line(src, ps, end) {
            // An indented line on which bison's recovery shifts no three
            // tokens: inside a recovery, its indent starts the count over too.
            gaps = 0;
        } else {
            return Before::Reporting;
        }
        end = ps;
    }
}

/// Whether bison, recovering at the indent of the indented line
/// `src[ls..end]`, shifts three tokens on it and so reports again: a
/// statement that starts there (`  2024-01-02 open Assets:A`), not a date
/// or a keyword that starts none (`  date: 2024-01-02`, whose `DATE` is
/// shifted and whose line end is not, so the count is back at three). The
/// recovery machine of [`quiet_bison_recovery`], over the line's tokens.
fn recovery_ends_on_line(src: &str, ls: usize, end: usize) -> bool {
    let mut status = 3u8;
    let mut prefix: Vec<Bc> = Vec::new();
    for (t, r) in BcLexer::at_line_start(src, ls) {
        if r.start >= end || t == Bc::Eof {
            break;
        }
        let shift = if t == Bc::Error || t == Bc::Indent {
            false
        } else if accepts(&prefix, t) {
            true
        } else {
            // Not taken: the count starts over, and the token is tried again
            // from a `declarations`.
            status = 3;
            prefix.clear();
            accepts(&[], t)
        };
        if !shift {
            status = 3;
            prefix.clear();
            continue;
        }
        if !(t == Bc::Eol && prefix.is_empty()) {
            prefix.push(t);
        }
        status -= 1;
        if status == 0 {
            return true;
        }
        if t == Bc::Eol {
            break;
        }
    }
    false
}

/// Where an undated declaration bison has shifted three tokens of, mid-line
/// (`kinds`, ending at `pos`), fails: the token it does not take and that
/// token's class, or `None` where it ends its line (it is built) or where its
/// rest is not modeled (a metadata value that is a number or an expression, a
/// string that runs over line ends).
/// `option` and `plugin` with two strings and `popmeta` with its key take
/// only the line end; `pushmeta` with its key takes a value first.
fn undated_declaration_failure(src: &str, kinds: &[Bc], pos: usize) -> Option<(Bc, Range<usize>)> {
    let mut lexer = BcLexer::mid_line(src, pos);
    let mut next = || lexer.next().unwrap_or((Bc::Eof, src.len()..src.len()));
    let t = next();
    let t = match kinds {
        [Bc::Kw(Kw::Option | Kw::Plugin), Bc::Str, Bc::Str]
        | [Bc::Kw(Kw::Popmeta), Bc::Key, Bc::Colon] => t,
        [Bc::Kw(Kw::Pushmeta), Bc::Key, Bc::Colon] => {
            let text = &src[t.1.clone()];
            match t.0 {
                Bc::Number => return None,
                Bc::Other if matches!(text, "(" | "-" | "+") => return None,
                Bc::Str | Bc::Account | Bc::Date | Bc::Currency | Bc::Capital | Bc::Tag => next(),
                Bc::Other if matches!(text, "TRUE" | "FALSE" | "NULL") => next(),
                _ => t,
            }
        }
        _ => return None,
    };
    // (A string that runs over line ends is reported where it ends: not
    // modeled.)
    (!matches!(t.0, Bc::Eol | Bc::Eof) && !src[t.1.clone()].contains('\n')).then_some(t)
}

/// The error for the token `at` that an undated declaration bison started
/// mid-line fails at ([`undated_declaration_failure`]), in the input's frame.
fn undated_failure_error(
    src: &str,
    keyword: Bc,
    at: Range<usize>,
    off: usize,
) -> crate::ParseError {
    let name = match keyword {
        Bc::Kw(Kw::Option) => "option",
        Bc::Kw(Kw::Plugin) => "plugin",
        Bc::Kw(Kw::Popmeta) => "popmeta",
        _ => "pushmeta",
    };
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError(format!(
            "unexpected {:?} in the {name} directive: expected the end of the line",
            &src[at.clone()]
        )),
        crate::Span::new(at.start + off, at.end + off),
    )
}

/// Whether the rest of the line from `pos` (a token's end, outside any
/// string) holds an invalid token and no token that runs over its end (a
/// string), which would leave the line no whole statement to parse alone.
fn line_holds_an_invalid_token(src: &str, pos: usize) -> bool {
    let mut invalid = false;
    for (k, r) in BcLexer::mid_line(src, pos) {
        match k {
            Bc::Eol | Bc::Eof => break,
            _ if src[r].contains('\n') => return false,
            Bc::Error => invalid = true,
            _ => {}
        }
    }
    invalid
}

/// The errors of the entry bison builds at `stripped[text]` (#2979), parsed
/// on its own, in the input's frame (`off`, the stripped BOM): `None` where
/// that parse meets a declaration bison shifts mid-line, whose state change
/// is not modeled. Never nested more than once (`PHANTOM_DEPTH`).
fn phantom_errors(
    stripped: &str,
    text: Range<usize>,
    off: usize,
    depth: u8,
) -> Option<Vec<crate::ParseError>> {
    PHANTOM_DEPTH.with(|d| d.set(depth + 1));
    UNMODELED_PHANTOM.with(|u| u.set(false));
    let shift = text.start + off;
    let sub = super::convert::parse_via_cst(&stripped[text]);
    PHANTOM_DEPTH.with(|d| d.set(depth));
    if UNMODELED_PHANTOM.with(|u| u.replace(false)) {
        return None;
    }
    Some(
        sub.errors
            .into_iter()
            .filter(|x| !is_push_pop_state(x))
            .map(|mut x| {
                x.span = crate::Span::new(x.span.start + shift, x.span.end + shift);
                x
            })
            .collect(),
    )
}

/// Whether `e` is about the push/pop state of the whole file, which an entry
/// parsed on its own does not have.
const fn is_push_pop_state(e: &crate::ParseError) -> bool {
    use crate::ParseErrorKind as K;
    matches!(
        e.kind,
        K::UnclosedPushtag(_) | K::UnclosedPushmeta(_) | K::InvalidPoptag(_) | K::InvalidPopmeta(_)
    )
}

/// Whether beancount's grammar reads `tokens`, the start of an indented line
/// before an invalid token, without failing: nothing, or a posting's start
/// (an optional flag, an account, then its amount, cost and price tokens), a
/// metadata key and its value, or tags and links. Coarse on purpose: a
/// `false` only makes the caller count one more error there, so beancount's
/// own count of the line is never undercut.
fn posting_prefix_reads(tokens: &[(Bc, Range<usize>)], src: &str) -> bool {
    use Bc as B;
    let mut it = tokens.iter().filter(|(t, _)| *t != B::Indent).peekable();
    let Some((first, _)) = it.peek().copied() else {
        return true;
    };
    match first {
        B::Key => {
            it.next();
            matches!(it.next(), None | Some((B::Colon, _)))
                && it.all(|(t, _)| {
                    matches!(
                        t,
                        B::Str
                            | B::Account
                            | B::Date
                            | B::Currency
                            | B::Capital
                            | B::Tag
                            | B::Number
                            | B::Other
                    )
                })
        }
        B::Tag | B::Link => it.all(|(t, _)| matches!(t, B::Tag | B::Link)),
        _ => {
            if matches!(first, B::Flag | B::Asterisk | B::Hash | B::Capital) {
                it.next();
            }
            if !matches!(it.next(), None | Some((B::Account, _))) {
                return false;
            }
            let mut depth = 0i32;
            let mut prev = B::Account;
            for (t, r) in it {
                let text = &src[r.clone()];
                let ok = match t {
                    B::Number | B::Currency | B::Capital => true,
                    B::Other if text.starts_with('{') => {
                        depth += 1;
                        true
                    }
                    B::Other if text.starts_with('}') => {
                        depth -= 1;
                        depth >= 0
                    }
                    B::Other => true,
                    B::Asterisk => depth > 0 || matches!(prev, B::Number),
                    B::Date | B::Str | B::Hash => depth > 0,
                    _ => false,
                };
                if !ok {
                    return false;
                }
                prev = *t;
            }
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Bc, BcLexer, Kw, accepts};

    fn kinds(src: &str) -> Vec<Bc> {
        BcLexer::at_line_start(src, 0).map(|(t, _)| t).collect()
    }

    /// The port reads `lexer.l`'s rules: the indent before a token, lines it
    /// skips, the longest match, trailing context, and the lexer's own errors.
    #[test]
    fn test_bc_lexer_reads_beancount_tokens() {
        use Bc as B;
        assert_eq!(
            kinds("2024-01-02 * \"n\" #t ^l\n"),
            [
                B::Date,
                B::Asterisk,
                B::Str,
                B::Tag,
                B::Link,
                B::Eol,
                B::Eof
            ]
        );
        assert_eq!(
            kinds("  Assets:A -1 USD\n"),
            [
                B::Indent,
                B::Account,
                B::Other,
                B::Number,
                B::Currency,
                B::Eol,
                B::Eof
            ]
        );
        // A comment line and an IGNORE line are their line ends; an indented
        // comment is an indent; a blank-only line is a line end.
        assert_eq!(
            kinds(";c\n* x\n  ;c\n  \n"),
            [B::Eol, B::Eol, B::Indent, B::Eol, B::Eol, B::Eof]
        );
        // `kk:` is a key (trailing context), `k:` an invalid token; `open:`
        // a key, longer than the keyword.
        assert_eq!(
            kinds("kk: k: open:"),
            [B::Key, B::Colon, B::Error, B::Key, B::Colon, B::Eof]
        );
        // An invalid date, a malformed number: the lexer's errors.
        assert_eq!(
            kinds("2024-02-30 1,50 1,000"),
            [B::Error, B::Error, B::Number, B::Eof]
        );
        // A lone capital is a `CAPITAL` only before a blank or a `\n`.
        assert_eq!(
            kinds("Z \nZ\r\nZ"),
            [B::Capital, B::Eol, B::Error, B::Eol, B::Error, B::Eof]
        );
        // A string runs over line ends, but not past a backslash before one.
        assert_eq!(
            kinds("\"a\nb\" \"c\\\nd\""),
            [B::Str, B::Error, B::Eol, B::Error, B::Eof]
        );
        assert_eq!(kinds("pushtag"), [B::Kw(Kw::Pushtag), B::Eof]);
    }

    /// A BOM is an invalid token unless beancount's lexer reads it into an
    /// account, a string or a comment; the probe reads on over ascending
    /// positions and restarts at a line start when asked about one behind it.
    #[test]
    fn test_bom_is_invalid_token_reads_beancount_tokens() {
        let src = "\u{FEFF}g \u{FEFF}Assets:A \"\u{FEFF}\" ;\u{FEFF}\n\t\u{FEFF}\n";
        let line_start = |at: usize| src[..at].rfind('\n').map_or(0, |i| i + 1);
        let boms: Vec<usize> = src.match_indices('\u{FEFF}').map(|(i, _)| i).collect();
        let expected = [true, false, false, false, true];
        let mut probe = None;
        for (&at, &invalid) in boms.iter().zip(&expected) {
            assert_eq!(
                super::bom_is_invalid_token(&mut probe, src, at, &line_start),
                invalid,
                "BOM at {at}"
            );
        }
        // Asked again about the first one, behind the probe.
        assert!(super::bom_is_invalid_token(
            &mut probe,
            src,
            boms[0],
            &line_start
        ));
    }

    /// The first three tokens of a statement, as `grammar.y` takes them.
    #[test]
    fn test_accepts_reads_statement_starts() {
        use Bc as B;
        assert!(accepts(&[], B::Date) && accepts(&[], B::Eol) && accepts(&[], B::Kw(Kw::Option)));
        assert!(
            !accepts(&[], B::Indent) && !accepts(&[], B::Str) && !accepts(&[], B::Kw(Kw::Open))
        );
        assert!(accepts(&[B::Date], B::Capital) && accepts(&[B::Date], B::Kw(Kw::Open)));
        assert!(!accepts(&[B::Date], B::Date) && !accepts(&[B::Date], B::Str));
        assert!(accepts(&[B::Date, B::Flag], B::Eol) && accepts(&[B::Date, B::Asterisk], B::Pipe));
        assert!(accepts(&[B::Date, B::Kw(Kw::Open)], B::Account));
        assert!(!accepts(&[B::Date, B::Kw(Kw::Open)], B::Eol));
        assert!(accepts(&[B::Kw(Kw::Pushmeta), B::Key], B::Colon));
        assert!(accepts(&[B::Kw(Kw::Plugin), B::Str], B::Eof));
        assert!(!accepts(&[B::Kw(Kw::Option), B::Str], B::Eol));
    }

    /// The model lexes each byte a bounded number of times, and parses each
    /// entry bison builds mid-line once, however many failed lines, quiet
    /// lines and such entries the input holds.
    #[test]
    fn test_quiet_bison_recovery_scans_linear_bytes() {
        use crate::logos_lexer::test_counters::RECOVERY_SHIFT_SCANNED_BYTES;
        const N: usize = 20_000;
        for (label, src) in [
            (
                "failed headers and blanks",
                "pushtag #a $\n\n  2024-02-30 5\n".repeat(N),
            ),
            (
                "bad postings",
                "2024-01-02 * \"n\"\n".to_string() + &"  Assets:A 1 USD 5\n".repeat(N),
            ),
            (
                "second-date entries",
                "2024-01-02 2024-01-03 * \"n\"\n  Assets:A 1 USD\n".repeat(N),
            ),
            (
                "entries on one line",
                "$ 2024-01-02 * \"y\" ".repeat(N) + "\n",
            ),
            (
                "nested entries",
                "$\n".to_string() + &"  2024-01-02 * \"n\"\n".repeat(N),
            ),
            ("statements after windows", "$\n2024-01-30 open\n".repeat(N)),
            (
                "lone capitals",
                "2024-01-02 * \"n\"\r\n".to_string() + &"  h1 Z\r\n".repeat(N),
            ),
            ("BOM-led lines", "\u{FEFF}g \u{FEFF}Assets:A\n".repeat(N)),
            ("BOMs alone on indented lines", "\t\u{FEFF}\n".repeat(N)),
            (
                "BOMs on one line",
                "$ ".to_string() + &"\u{FEFF}Assets:A \u{FEFF}x ".repeat(N) + "\n",
            ),
            (
                "entries with an invalid token",
                "$ 2024-01-02 * \"y\" $\n  Assets:A 1 USD\n".repeat(N),
            ),
            ("misgrouped numbers", "$\n  x 1,50\n".repeat(N)),
            ("orphan indented lines", "  $x\n\n\n".repeat(N)),
            (
                "orphan lines after indented comments",
                "\n".to_string() + &"  ; c\n  ; d\n\n  $x\n\n\n".repeat(N),
            ),
            (
                "invalid accounts",
                "    Assets:Café 1 BRL\n    Assets:B\n\n".repeat(N),
            ),
            (
                "lines after options in a body",
                "2024-01-02 * \"n\"\n".to_string()
                    + &"  option \"title\" \"x\"\n  $x\n  Assets:B 1 USD\n".repeat(N),
            ),
            (
                "undated declarations failing mid-line",
                "~ popmeta kk: @ x\n~ pushmeta kk: \"v\" @\n".repeat(N),
            ),
            (
                "date lines in a recovery",
                "2024-01-02 * \"n\"\n  option \"title\" \"x\"\n".to_string()
                    + &"    date: 2024-01-02\n".repeat(N)
                    + "\n  Assets:a 1 USD\n",
            ),
            (
                "orphan lines in a long body",
                "2024-01-01 open Assets:A\n".to_string()
                    + &"  $x\n  kk: \"v\"\n  kk: \"v\"\n  kk: \"v\"\n".repeat(N),
            ),
        ] {
            RECOVERY_SHIFT_SCANNED_BYTES.with(|c| c.set(0));
            let _ = crate::parse(&src);
            let bytes = RECOVERY_SHIFT_SCANNED_BYTES.with(std::cell::Cell::get);
            assert!(
                bytes <= 8 * src.len(),
                "{label}: scanned {bytes} bytes of a {}-byte input",
                src.len()
            );
        }
    }
}
