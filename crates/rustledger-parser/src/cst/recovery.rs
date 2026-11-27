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
//! Where a line of such an entry's body fails and bison is still recovering
//! at the body's end, the window goes on past it, at the status the entry's
//! own pass ended at. An entry bison builds inside such an entry's body is
//! parsed on its own in turn, [`MAX_PHANTOM_DEPTH`] levels deep at most, so
//! the work stays within a bounded number of parses of the input.
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
//!
//! A stray `\r` (one not part of a CRLF line end) is a blank to beancount's
//! lexer. This parser reports one before a token that lexes, or at a line
//! start, as an error of its own, on purpose (#2980), and reads the line
//! around it in its own way, so the machine above cannot start from such a
//! line. Instead the input is parsed once more as beancount reads it
//! ([`stray_cr_analog`]: each stray `\r` a space, a line whose leading
//! blanks hold one moved to column 0), and from the first line holding a
//! stray `\r` on, every line has that parse's errors, but a line where this
//! parser reports a stray `\r` itself, which keeps its own
//! ([`model_stray_cr_lines`]).

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

thread_local! {
    /// How deep [`quiet_bison_recovery`] has nested the parse of an entry
    /// bison's recovery builds: [`MAX_PHANTOM_DEPTH`] levels at most, so the
    /// work stays linear.
    static PHANTOM_DEPTH: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    /// Left by a nested pass for [`phantom_errors`]: bison's error status at
    /// the end of the entry's text where it is still recovering there (a
    /// line of the entry's body failed, and fewer than three tokens were
    /// shifted after it), so the window goes on past the entry.
    static PHANTOM_TAIL: std::cell::Cell<Option<u8>> = const { std::cell::Cell::new(None) };
    /// Set by a nested pass that met a declaration bison shifts mid-line,
    /// whose effect it does not model: the entry around it keeps rledger's
    /// errors.
    static UNMODELED_PHANTOM: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// A line of the input rewritten by [`stray_cr_analog`] whose text moved: a
/// line whose leading blanks hold a stray `\r` (no `INDENT` to beancount),
/// whose content now starts at its line start, `lead` bytes earlier, with
/// `lead` blanks after it (`content` bytes long), so the lines after keep
/// their offsets.
#[derive(Clone, Copy, Debug)]
pub(super) struct MovedLine {
    start: usize,
    lead: usize,
    content: usize,
}

/// The input as beancount reads it, where it holds a stray `\r` (a `\r` not
/// part of a CRLF line end, #2980): every stray `\r` is a blank to
/// beancount's lexer (`[ \t\r]+`), so it is replaced by a space, of the same
/// length, so every other byte keeps its offset. Two of `lexer.l`'s rules
/// tell a `\r` from a space, and are kept:
///
/// * `^[ \t]+/[^ \t\r\n]`, the indent: a line whose leading blanks run into a
///   stray `\r` has none, so its content is read as a column-0 statement.
///   Its content is moved to the line start, and the blanks put after it
///   (`MovedLine`). Not where the content starts with a character beancount's
///   lexer skips a line at at column 0 (`*`, `:`, a flag, a `#` that starts no
///   tag), nor a BOM at the start of the input, which no line start reads as
///   beancount reads it after a `\r`: such a line is left as it is;
/// * `[A-Z]/[ \t\n]`, a lone capital, which a `\r` after it makes an invalid
///   token: a line with one is left as it is.
///
/// A `\r` inside a string is a space too (its text is no structure). Lines
/// are found with beancount's own lexer ([`BcLexer`]), so a line start inside
/// a string that runs over line ends is no line start. `None` where nothing
/// is rewritten. One pass over the input.
pub(super) fn stray_cr_analog(src: &str) -> Option<(String, Vec<MovedLine>)> {
    let b = src.as_bytes();
    let is_stray = |i: usize| b[i] == b'\r' && b.get(i + 1) != Some(&b'\n');
    if !(0..b.len()).any(is_stray) {
        return None;
    }
    // Strings that run over a line end, and where each lone capital
    // beancount's lexer reads as an invalid token ends, in order.
    let mut multiline: Vec<Range<usize>> = Vec::new();
    let mut after_capital: Vec<usize> = Vec::new();
    for (t, r) in BcLexer::at_line_start(src, 0) {
        match t {
            Bc::Str if src[r.clone()].contains('\n') => multiline.push(r),
            Bc::Error if r.len() == 1 && b[r.start].is_ascii_uppercase() => {
                after_capital.push(r.end);
            }
            _ => {}
        }
    }
    let in_string = |at: usize| {
        let i = multiline.partition_point(|r| r.start < at);
        i.checked_sub(1).is_some_and(|i| multiline[i].end > at)
    };
    let mut out = String::with_capacity(src.len());
    let mut moved = Vec::new();
    let mut ls = 0;
    while ls < b.len() {
        let nl = src[ls..].find('\n').map_or(b.len(), |i| ls + i);
        let next = (nl + 1).min(b.len());
        let line = &src[ls..nl];
        // The line's end, before the `\r` of a CRLF.
        let body_end = if nl < b.len() && nl > ls && b[nl - 1] == b'\r' {
            nl - 1
        } else {
            nl
        };
        if !(ls..body_end).any(is_stray) {
            out.push_str(&src[ls..next]);
            ls = next;
            continue;
        }
        let blank_run = line.len() - line.trim_start_matches([' ', '\t']).len();
        let lead = if !in_string(ls) && ls + blank_run < body_end && is_stray(ls + blank_run) {
            let run = src[ls..body_end].len()
                - src[ls..body_end]
                    .trim_start_matches([' ', '\t', '\r'])
                    .len();
            Some(run)
        } else {
            None
        };
        let content_start = ls + lead.unwrap_or(0);
        let content = &src[content_start..body_end];
        let skipped_at_column_0 = |s: &str| {
            let cb = s.as_bytes();
            match cb.first() {
                Some(b'*' | b':' | b'!' | b'&' | b'?' | b'%') => true,
                Some(b'#') => !cb.get(1).is_some_and(|&c| {
                    c.is_ascii_alphanumeric() || matches!(c, b'-' | b'_' | b'/' | b'.')
                }),
                _ => false,
            }
        };
        let kept = lead.is_some_and(|_| {
            !content.is_empty()
                && (skipped_at_column_0(content)
                    || ls == 0 && content.starts_with(crate::bom::BOM_CHAR))
        }) || (content_start..body_end).any(|i| is_stray(i) && after_capital.binary_search(&i).is_ok())
            // (A lone capital the moved content ends with, an invalid token
            // before the line end, would be one before a blank.)
            || lead.is_some() && after_capital.binary_search(&body_end).is_ok();
        if kept {
            out.push_str(&src[ls..next]);
            ls = next;
            continue;
        }
        let blanked = |s: &str, at: usize| -> String {
            s.char_indices()
                .map(|(i, c)| {
                    if c == '\r' && is_stray(at + i) {
                        ' '
                    } else {
                        c
                    }
                })
                .collect()
        };
        match lead {
            Some(n) if !content.is_empty() => {
                out.push_str(&blanked(content, content_start));
                out.extend(std::iter::repeat_n(' ', n));
                moved.push(MovedLine {
                    start: ls,
                    lead: n,
                    content: content.len(),
                });
            }
            _ => out.push_str(&blanked(&src[ls..body_end], ls)),
        }
        out.push_str(&src[body_end..next]);
        ls = next;
    }
    #[cfg(test)]
    crate::logos_lexer::test_counters::RECOVERY_SHIFT_SCANNED_BYTES
        .with(|c| c.set(c.get() + src.len()));
    (out != src).then_some((out, moved))
}

thread_local! {
    /// Set while the input's stray-`\r` analog is parsed
    /// ([`model_stray_cr_lines`]), so that parse does not start another.
    static IN_STRAY_CR_ANALOG: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Where a position of the analog ([`stray_cr_analog`]) is in the input.
fn analog_to_input(at: usize, moved: &[MovedLine]) -> usize {
    let i = moved.partition_point(|m| m.start <= at);
    match i.checked_sub(1).map(|i| moved[i]) {
        Some(m) if at < m.start + m.content => at + m.lead,
        Some(m) if at < m.start + m.content + m.lead => m.start + m.content + m.lead,
        _ => at,
    }
}

/// bison's recovery through a line holding a stray `\r` (#2980). rledger
/// reports a stray `\r` before a token that lexes as an error, on purpose
/// (`test_parse_cr_with_more_of_the_line_after_it_stays_an_error`), where
/// beancount's lexer reads a blank; from such a line on, rledger's errors and
/// beancount's recovery part. So the input is parsed once more as beancount
/// reads it ([`stray_cr_analog`]), and from the first line holding a stray `\r`
/// on, each line has that parse's errors, but a line where rledger reports a
/// stray `\r` itself, which keeps its own. One more parse, only for an input
/// with an error and a stray `\r`, never nested.
pub(super) fn model_stray_cr_lines(
    errors: &mut Vec<crate::ParseError>,
    root: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
    use_green: bool,
) {
    use rowan::Language as _;
    if errors.is_empty()
        || PHANTOM_DEPTH.with(std::cell::Cell::get) > 0
        || IN_STRAY_CR_ANALOG.with(std::cell::Cell::get)
    {
        return;
    }
    let Some((analog, moved)) = stray_cr_analog(stripped) else {
        return;
    };
    // (A BOM at its start would be stripped, and every offset move.)
    if analog.starts_with(crate::bom::BOM_CHAR) {
        return;
    }
    let off = bom_offset as usize;
    let b = stripped.as_bytes();
    let is_stray = |i: usize| b.get(i) == Some(&b'\r') && b.get(i + 1) != Some(&b'\n');
    let line_ends: Vec<usize> = stripped.match_indices('\n').map(|(i, _)| i).collect();
    let line_of = |at: usize| line_ends.partition_point(|&nl| nl < at);
    let Some(first) = (0..b.len()).find(|&i| is_stray(i)) else {
        return;
    };
    let first_line = line_of(first);
    // The lines where rledger reads a stray `\r` as an invalid token of its
    // own, whose errors stand for it.
    let mut own: Vec<usize> = Vec::new();
    let mut stack = vec![(root.green(), 0usize)];
    while let Some((node, start)) = stack.pop() {
        let mut pos = start;
        for el in node.children() {
            let len = usize::from(el.text_len());
            match el {
                rowan::NodeOrToken::Node(n) => stack.push((n, pos)),
                rowan::NodeOrToken::Token(t)
                    if crate::BeancountLanguage::kind_from_raw(t.kind())
                        == crate::SyntaxKind::ERROR_TOKEN =>
                {
                    if let Some(i) = (pos..pos + len).find(|&i| is_stray(i)) {
                        own.push(line_of(i));
                    }
                }
                rowan::NodeOrToken::Token(_) => {}
            }
            pos += len;
        }
    }
    own.sort_unstable();
    own.dedup();
    IN_STRAY_CR_ANALOG.with(|f| f.set(true));
    let sub = super::convert::parse_analog_errors(&analog, use_green);
    IN_STRAY_CR_ANALOG.with(|f| f.set(false));
    let keeps_its_own = |line: usize| line < first_line || own.binary_search(&line).is_ok();
    // A push left open at the end of the input is about the state of the
    // whole file, which is this parser's, where a line it reports a stray
    // `\r` on adds no push and no pop: from this parse, wherever its push is.
    let unclosed = |e: &crate::ParseError| {
        matches!(
            e.kind,
            crate::ParseErrorKind::UnclosedPushtag(_) | crate::ParseErrorKind::UnclosedPushmeta(_)
        )
    };
    errors.retain(|e| unclosed(e) || keeps_its_own(line_of(e.span.start.saturating_sub(off))));
    for mut e in sub {
        let start = analog_to_input(e.span.start, &moved);
        if keeps_its_own(line_of(start)) || unclosed(&e) {
            continue;
        }
        let end = analog_to_input(e.span.end, &moved).max(start);
        e.span = crate::Span::new(start + off, end + off);
        errors.push(e);
    }
    errors.sort_by_key(|e| e.span.start);
}

#[cfg(test)]
mod tests {
    use super::{Bc, BcLexer, Kw};

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

    /// The input as beancount reads it: a stray `\r` is a blank, a line whose
    /// leading blanks hold one has no indent (its content moves to the line
    /// start, the blanks after it), and every other byte keeps its offset.
    /// Kept as written: a line whose content beancount would skip at column
    /// 0, or with a lone capital before a `\r` (an invalid token there).
    #[test]
    fn test_stray_cr_analog_reads_a_stray_cr_as_a_blank() {
        let analog = |src: &str| super::stray_cr_analog(src).map(|(text, _)| text);
        assert_eq!(analog("a\r\nb\n"), None);
        assert_eq!(analog("pushtag #a\r$\n").as_deref(), Some("pushtag #a $\n"));
        assert_eq!(analog("\r  $x\r\nb\n").as_deref(), Some("$x   \r\nb\n"));
        assert_eq!(analog(" \r\n").as_deref(), None);
        assert_eq!(analog(" \r \n").as_deref(), Some("   \n"));
        assert_eq!(
            analog("\"a\r\n\r  b\"\n").as_deref(),
            Some("\"a\r\n   b\"\n")
        );
        assert_eq!(analog("\r* x\n"), None);
        assert_eq!(analog("x P\r$\n"), None);
        assert_eq!(analog(" \rT\r\n"), None);
        let (text, moved) = super::stray_cr_analog("x\n \r$x y\n").expect("rewritten");
        assert_eq!(text, "x\n$x y  \n");
        assert_eq!(super::analog_to_input(2, &moved), 4);
        assert_eq!(super::analog_to_input(7, &moved), 8);
        assert_eq!(super::analog_to_input(9, &moved), 9);
        assert_eq!(super::analog_to_input(0, &moved), 0);
    }
}
