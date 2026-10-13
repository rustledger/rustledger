//! A regular expression from a plugin's config, read as Python's `re` reads
//! it (#2601).
//!
//! The upstream plugins compile their config's patterns with Python's `re`;
//! rledger matches with the `regex` crate, whose syntax overlaps Python's but
//! is not the same language. Passing a config pattern to `regex` unchanged
//! failed on constructs Python has and `regex` lacks (lookaround,
//! backreferences), and, worse, silently matched differently where the same
//! text means different things: in a character class `[[:alpha:]]` is a POSIX
//! class to `regex` and a `[`, `:`, ... set followed by `]` to Python, `&&`,
//! `--` and `~~` are set operations to `regex` and literal characters to
//! Python, and `\<` is a word boundary to `regex` and a literal `<` to Python.
//!
//! [`translate`] parses a pattern with Python's grammar (as `sre_parse` does)
//! and writes the same pattern in `regex` syntax, every literal escaped, so a
//! pattern means what it means in Python or is refused:
//!
//! - a construct Python has and `regex` cannot express is
//!   [`PyRegexError::Unsupported`], naming it (lookahead, lookbehind,
//!   backreferences, conditionals, atomic groups, possessive quantifiers,
//!   `\N{...}`, the ASCII flag, `\b`/`\B`);
//! - a pattern Python itself rejects is [`PyRegexError::Invalid`].
//!
//! Two exceptions, reported as unsupported rather than invalid: a lookbehind
//! Python rejects for not being fixed-width (`(?<=a+)b`), since its width is
//! not computed here, and a `\N{...}` escape naming no character, since
//! character names are not looked up. Either way the pattern is refused.
//!
//! `\d`, `\s` and `\w` are written as the classes Python means by them
//! (`\w` is `str.isalnum()` or `_`, `\s` is `str.isspace()`), not `regex`'s,
//! which differ on some non-ASCII characters. `\b` and `\B` are refused
//! rather than approximated: a word boundary is defined by `\w`, and `regex`
//! cannot be given Python's definition of it.
//!
//! Deliberate divergences, both on non-ASCII input only: with `(?i)`, the
//! case folding is `regex`'s Unicode simple case folding, which differs from
//! Python's for a few characters (Python matches `i` with the dotless `ı`,
//! `regex` does not); and `$` matches only at the end, where Python's also
//! matches before a final newline. The patterns here match account names and
//! currencies, which cannot contain a newline, so the second never applies.

use std::fmt::{self, Write as _};

/// Why a config pattern cannot be used.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PyRegexError {
    /// Python accepts the construct, and rledger's regex engine cannot
    /// express it; the string names the construct.
    Unsupported(String),
    /// Python's `re` rejects the pattern too; the string says why.
    Invalid(String),
}

impl fmt::Display for PyRegexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(what) => write!(
                f,
                "it uses {what}, which Python's `re` supports and rledger does not"
            ),
            Self::Invalid(why) => write!(f, "it is not a valid regular expression: {why}"),
        }
    }
}

fn unsupported<T>(what: &str) -> Result<T, PyRegexError> {
    Err(PyRegexError::Unsupported(what.to_string()))
}

fn invalid<T>(why: impl Into<String>) -> Result<T, PyRegexError> {
    Err(PyRegexError::Invalid(why.into()))
}

/// Python's `\d`: Unicode decimal digits.
const DIGIT: &str = r"\p{Nd}";
/// Python's `\s` for a `str` pattern: `str.isspace()`, which adds the
/// information separators U+001C..U+001F to Unicode `White_Space`.
const SPACE: &str = r"\s\x1C-\x1F";
/// Python's `\w` for a `str` pattern: `str.isalnum()` (letters and numbers)
/// or `_`.
const WORD: &str = r"\p{L}\p{N}_";

/// `pattern`, a Python regular expression, written in `regex` syntax with the
/// same meaning.
///
/// # Errors
///
/// [`PyRegexError::Unsupported`] when the pattern uses a construct rledger's
/// regex engine cannot express, [`PyRegexError::Invalid`] when Python's `re`
/// would reject it too.
pub fn translate(pattern: &str) -> Result<String, PyRegexError> {
    Ok(parse(pattern)?.out)
}

fn parse(pattern: &str) -> Result<Parser, PyRegexError> {
    let mut parser = Parser {
        chars: pattern.chars().collect(),
        pos: 0,
        out: String::new(),
        groups: Vec::new(),
        deferred: None,
        loops: Vec::new(),
        max_condition_ref: 0,
        lookbehind: None,
    };
    parser.global_flags()?;
    parser.alternation(0, false)?;
    if parser.pos < parser.chars.len() {
        // `alternation` at depth 0 stops only at an unmatched `)`.
        return invalid(format!("unbalanced parenthesis at position {}", parser.pos));
    }
    if parser.max_condition_ref > parser.groups.len() {
        return invalid(format!(
            "invalid group reference {}",
            parser.max_condition_ref
        ));
    }
    if let Some(what) = parser.deferred {
        return Err(PyRegexError::Unsupported(what));
    }
    Ok(parser)
}

/// A pattern compiled for Python's `re.sub`, with what a replacement
/// template needs to know about its groups.
#[derive(Debug)]
pub struct SubPattern {
    /// The compiled pattern.
    pub regex: regex::Regex,
    /// Capturing groups, by number (1-based), as Python numbers them: a
    /// group inside a `{0}` repetition still counts.
    groups: Vec<GroupInfo>,
}

/// Compile `pattern` for Python's `re.sub`.
///
/// Refuses, as [`PyRegexError::Unsupported`], a pattern that can match the
/// empty string: `re.sub` replaces empty matches differently from
/// `regex::Regex::replace_all` (it also takes an empty match right after a
/// non-empty one, so `re.sub('x*', '-', 'abxd')` is `-a-b--d-`, where
/// `replace_all` gives `-a-b-d-`).
///
/// # Errors
///
/// As [`compile_match`], and the empty-match case above.
pub fn compile_sub(pattern: &str) -> Result<SubPattern, PyRegexError> {
    let parser = parse(pattern)?;
    let regex = compile(&parser.out)?;
    // With lookaround and word boundaries refused, every assertion left
    // (`^`, `$`, `\A`, `\z`) holds in the empty string, so a pattern that
    // can match empty anywhere matches the empty string itself.
    if regex.is_match("") {
        return unsupported(
            "a pattern that can match an empty string (Python's `re.sub` replaces empty matches differently)",
        );
    }
    // A repetition whose body can match empty: when an iteration's
    // preferred path is empty, Python's engine ends the loop there, where
    // `regex` drops the empty iteration and takes a branch that consumes
    // text (`b(?:a?|c)*` on `bac` stops after `a` in Python and runs to the end here), and a
    // group in it keeps a different last value.
    for &(start, end) in &parser.loops {
        let body = &parser.out[start..end];
        if compile(&format!("^(?:{body})$"))?.is_match("") {
            return unsupported(
                "a repetition whose body can match an empty string (Python's engine ends such a loop where rledger's goes on)",
            );
        }
    }
    Ok(SubPattern {
        regex,
        groups: parser.groups,
    })
}

/// Compile `pattern` for Python's `re.match`: anchored at the start, need not
/// reach the end.
///
/// # Errors
///
/// As [`translate`], or [`PyRegexError::Unsupported`] when the translation is
/// too large for rledger's regex engine.
pub fn compile_match(pattern: &str) -> Result<regex::Regex, PyRegexError> {
    compile(&format!("^(?:{})", translate(pattern)?))
}

/// Compile `pattern` for Python's `re.search` / `re.sub`: matches anywhere.
///
/// # Errors
///
/// As [`compile_match`].
pub fn compile_search(pattern: &str) -> Result<regex::Regex, PyRegexError> {
    compile(&translate(pattern)?)
}

fn compile(translated: &str) -> Result<regex::Regex, PyRegexError> {
    regex::Regex::new(translated).map_err(|e| {
        // The translation is well-formed by construction; what is left is a
        // limit (a huge repetition count, say), which Python does not have.
        PyRegexError::Unsupported(format!("a pattern too large for rledger ({e})"))
    })
}

/// `template`, a Python `re.sub` replacement for `regex`, in `regex`'s
/// replacement syntax.
///
/// `\1`, `\g<1>` and `\g<name>` become group references, the escapes
/// Python resolves are resolved, and a literal `$` is escaped.
///
/// # Errors
///
/// [`PyRegexError::Invalid`] when Python would reject the template: a
/// reference to a group `regex` does not have, or an unknown escape of an
/// ASCII letter.
pub fn translate_replacement(template: &str, pattern: &SubPattern) -> Result<String, PyRegexError> {
    let chars: Vec<char> = template.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    // A group `regex` dropped (inside `{0}`) has no value there, so its
    // `${n}` is empty, as Python substitutes ''.
    let push_group = |out: &mut String, index: usize| -> Result<(), PyRegexError> {
        if index > pattern.groups.len() {
            return invalid(format!("invalid group reference {index}"));
        }
        write!(out, "${{{index}}}").expect("writing to a String cannot fail");
        Ok(())
    };
    while i < chars.len() {
        let c = chars[i];
        i += 1;
        match c {
            '$' => out.push_str("$$"),
            '\\' => {
                let Some(&next) = chars.get(i) else {
                    return invalid("bad escape (end of pattern)");
                };
                i += 1;
                match next {
                    'g' => {
                        if chars.get(i) != Some(&'<') {
                            return invalid("missing <");
                        }
                        let close = chars[i + 1..]
                            .iter()
                            .position(|&c| c == '>')
                            .ok_or(PyRegexError::Invalid("missing >, unterminated name".into()))?;
                        let name: String = chars[i + 1..i + 1 + close].iter().collect();
                        i += close + 2;
                        if name.is_empty() {
                            return invalid("missing group name");
                        }
                        if name.chars().all(|c| c.is_ascii_digit()) {
                            let index = name.parse::<usize>().map_err(|_| {
                                PyRegexError::Invalid("invalid group reference".into())
                            })?;
                            push_group(&mut out, index)?;
                        } else if let Some(index) = pattern
                            .groups
                            .iter()
                            .position(|g| g.name.as_deref() == Some(name.as_str()))
                        {
                            push_group(&mut out, index + 1)?;
                        } else if is_identifier(&name) {
                            return invalid(format!("unknown group name '{name}'"));
                        } else {
                            return invalid(format!("bad character in group name '{name}'"));
                        }
                    }
                    '0' => {
                        // Octal: `\0` and up to two more octal digits.
                        let mut code = 0u32;
                        for _ in 0..2 {
                            match chars.get(i).and_then(|c| c.to_digit(8)) {
                                Some(d) => {
                                    code = code * 8 + d;
                                    i += 1;
                                }
                                None => break,
                            }
                        }
                        push_literal_replacement(&mut out, code)?;
                    }
                    '1'..='9' => {
                        // Three octal digits are an octal escape; otherwise
                        // one or two digits are a group reference.
                        let octal = [Some(next), chars.get(i).copied(), chars.get(i + 1).copied()];
                        if let [Some(a), Some(b), Some(c)] = octal
                            && let (Some(a), Some(b), Some(c)) =
                                (a.to_digit(8), b.to_digit(8), c.to_digit(8))
                        {
                            let code = a * 64 + b * 8 + c;
                            if code > 0o377 {
                                return invalid("octal escape value outside of range 0-0o377");
                            }
                            i += 2;
                            push_literal_replacement(&mut out, code)?;
                        } else {
                            let mut index = next.to_digit(10).expect("a digit") as usize;
                            if let Some(d) = chars.get(i).and_then(|c| c.to_digit(10)) {
                                index = index * 10 + d as usize;
                                i += 1;
                            }
                            push_group(&mut out, index)?;
                        }
                    }
                    'a' => out.push('\x07'),
                    'b' => out.push('\x08'),
                    'f' => out.push('\x0c'),
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    'v' => out.push('\x0b'),
                    '\\' => out.push('\\'),
                    c if c.is_ascii_alphanumeric() => {
                        return invalid(format!("bad escape \\{c}"));
                    }
                    // Any other escape keeps its backslash, as Python's does.
                    c => {
                        out.push('\\');
                        if c == '$' {
                            out.push_str("$$");
                        } else {
                            out.push(c);
                        }
                    }
                }
            }
            c => out.push(c),
        }
    }
    Ok(out)
}

/// Whether `name` is a Python identifier, roughly (`str.isidentifier`):
/// a letter or `_`, then letters, digits or `_`.
fn is_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c == '_' || c.is_alphabetic())
        && chars.all(|c| c == '_' || c.is_alphanumeric())
}

fn push_literal_replacement(out: &mut String, code: u32) -> Result<(), PyRegexError> {
    match char::from_u32(code) {
        Some('$') => out.push_str("$$"),
        Some(c) => out.push(c),
        None => return invalid("invalid escape"),
    }
    Ok(())
}

struct Parser {
    chars: Vec<char>,
    pos: usize,
    out: String,
    /// Capturing groups opened so far, by number.
    groups: Vec<GroupInfo>,
    /// The first construct Python has and rledger cannot express. Parsing
    /// goes on past it, so a pattern Python rejects anyway is reported as
    /// invalid rather than as unsupported.
    deferred: Option<String>,
    /// The translated text of every group a repetition can run more than
    /// once, as ranges of `out`.
    loops: Vec<(usize, usize)>,
    /// The highest group number a conditional names.
    max_condition_ref: usize,
    /// Inside a lookbehind: the number of groups opened before it.
    lookbehind: Option<usize>,
}

/// What the parser learned about one capturing group.
#[derive(Debug, Clone, Default)]
struct GroupInfo {
    name: Option<String>,
    /// Its `)` has been read: Python refuses a reference to an open group.
    closed: bool,
}

/// What the last item written can take: a quantifier needs something to
/// repeat, and Python refuses to repeat a quantifier or an assertion.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Last {
    /// Nothing yet in this branch, or an assertion (`^`, `$`, `\A`, `\Z`).
    Nothing,
    /// A repeatable item.
    Item,
    /// A group, written as `out[.0...1]`: a repetition of it repeats it.
    Group(usize, usize),
    /// A quantifier (repeating it again is "multiple repeat").
    Repeat,
}

impl Parser {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.chars.get(self.pos + offset).copied()
    }

    fn starts_with(&self, s: &str) -> bool {
        s.chars()
            .enumerate()
            .all(|(i, c)| self.peek_at(i) == Some(c))
    }

    fn push_literal(&mut self, c: char) {
        self.out
            .push_str(&regex::escape(c.encode_utf8(&mut [0; 4])));
    }

    /// Global inline flags, `(?i)` and the like, which Python accepts only at
    /// the start of the pattern.
    fn global_flags(&mut self) -> Result<(), PyRegexError> {
        while self.starts_with("(?") {
            if self.starts_with("(?#") {
                // A comment before the flags: Python skips it.
                self.comment()?;
                continue;
            }
            let mut end = self.pos + 2;
            while end < self.chars.len() && self.chars[end].is_ascii_alphabetic() {
                end += 1;
            }
            if end == self.pos + 2 || self.chars.get(end) != Some(&')') {
                return Ok(());
            }
            let flags: String = self.chars[self.pos + 2..end].iter().collect();
            let rust = self.flags(&flags)?;
            if !rust.is_empty() {
                write!(self.out, "(?{rust})").expect("writing to a String cannot fail");
            }
            self.pos = end + 1;
        }
        Ok(())
    }

    /// Python flag letters as `regex` flags, or why they cannot be.
    fn flags(&mut self, letters: &str) -> Result<String, PyRegexError> {
        if letters.contains('a') && letters.contains('u') {
            return invalid("bad inline flags: flags 'a', 'u' and 'L' are incompatible");
        }
        let mut rust = String::new();
        for c in letters.chars() {
            match c {
                // A repeated letter is accepted, as Python accepts `(?ii)`.
                'i' | 'm' | 's' if rust.contains(c) => {}
                'i' | 'm' | 's' => rust.push(c),
                // Unicode matching is already the default for `str` patterns.
                'u' => {}
                'a' => self.defer("the ASCII flag `(?a)`"),
                'x' => return unsupported("the verbose flag `(?x)`"),
                'L' => return invalid("bad inline flags: cannot use 'L' flag with a str pattern"),
                c => return invalid(format!("unknown flag '{c}'")),
            }
        }
        Ok(rust)
    }

    /// Branches separated by `|`, up to the `)` that closes this group (or
    /// the end of the pattern at depth 0).
    /// Returns the number of branches.
    fn alternation(&mut self, depth: usize, in_group: bool) -> Result<usize, PyRegexError> {
        let mut last = Last::Nothing;
        let mut branches = 1;
        while let Some(c) = self.peek() {
            match c {
                '|' => {
                    self.pos += 1;
                    self.out.push('|');
                    last = Last::Nothing;
                    branches += 1;
                }
                ')' => {
                    if in_group {
                        return Ok(branches);
                    }
                    return invalid(format!("unbalanced parenthesis at position {}", self.pos));
                }
                '*' | '+' | '?' => {
                    self.pos += 1;
                    self.repeat(last, &c.to_string(), c != '?')?;
                    last = Last::Repeat;
                }
                '{' => {
                    if let Some((quantifier, many)) = self.braces()? {
                        self.repeat(last, &quantifier, many)?;
                        last = Last::Repeat;
                    } else {
                        self.pos += 1;
                        self.push_literal('{');
                        last = Last::Item;
                    }
                }
                '(' if self.starts_with("(?#") => {
                    // A comment is dropped, and what follows it repeats or
                    // fails to repeat as if it were not there.
                    self.comment()?;
                }
                '(' => {
                    let text = self.out.len();
                    last = self.group(depth)?;
                    if last == Last::Item {
                        last = Last::Group(text, self.out.len());
                    }
                }
                '[' => {
                    self.class()?;
                    last = Last::Item;
                }
                '\\' => {
                    last = self.escape()?;
                }
                '.' => {
                    self.pos += 1;
                    self.out.push('.');
                    last = Last::Item;
                }
                '^' | '$' => {
                    self.pos += 1;
                    self.out.push(c);
                    last = Last::Nothing;
                }
                c => {
                    self.pos += 1;
                    self.push_literal(c);
                    last = Last::Item;
                }
            }
        }
        if in_group {
            return invalid("missing ), unterminated subpattern");
        }
        Ok(branches)
    }

    /// A quantifier `quantifier` after `last`, with its lazy `?` if present.
    /// `many` says whether the repetition can run more than once.
    fn repeat(&mut self, last: Last, quantifier: &str, many: bool) -> Result<(), PyRegexError> {
        match last {
            Last::Nothing => return invalid("nothing to repeat"),
            Last::Repeat => return invalid("multiple repeat"),
            Last::Item => {}
            Last::Group(text_start, text_end) => {
                if many {
                    self.loops.push((text_start, text_end));
                }
            }
        }
        self.out.push_str(quantifier);
        match self.peek() {
            Some('?') => {
                self.pos += 1;
                self.out.push('?');
            }
            Some('+') => {
                self.pos += 1;
                self.defer("a possessive quantifier (`*+`, `++`, `?+`, `{m,n}+`)");
            }
            _ => {}
        }
        Ok(())
    }

    /// `{m}`, `{m,}`, `{,n}`, `{m,n}` as a `regex` quantifier, consumed; or
    /// `None`, nothing consumed, when the brace is a literal `{`, as Python
    /// reads one that does not form a quantifier.
    /// The `bool` says whether the repetition can run more than once.
    fn braces(&mut self) -> Result<Option<(String, bool)>, PyRegexError> {
        let start = self.pos;
        let mut i = start + 1;
        let digits = |i: &mut usize, chars: &[char]| -> String {
            let begin = *i;
            while *i < chars.len() && chars[*i].is_ascii_digit() {
                *i += 1;
            }
            chars[begin..*i].iter().collect()
        };
        let lo = digits(&mut i, &self.chars);
        let (hi, comma) = if self.chars.get(i) == Some(&',') {
            i += 1;
            (digits(&mut i, &self.chars), true)
        } else {
            (String::new(), false)
        };
        if self.chars.get(i) != Some(&'}') || (lo.is_empty() && !comma) {
            return Ok(None);
        }
        self.pos = i + 1;
        let parse = |s: &str| -> Result<u64, PyRegexError> {
            s.parse::<u64>()
                .map_err(|_| PyRegexError::Invalid("the repetition number is too large".into()))
        };
        let lo_n = if lo.is_empty() { 0 } else { parse(&lo)? };
        if !comma {
            return Ok(Some((format!("{{{lo_n}}}"), lo_n > 1)));
        }
        if hi.is_empty() {
            return Ok(Some((format!("{{{lo_n},}}"), true)));
        }
        let hi_n = parse(&hi)?;
        if hi_n < lo_n {
            return invalid("min repeat greater than max repeat");
        }
        Ok(Some((format!("{{{lo_n},{hi_n}}}"), hi_n > 1)))
    }

    /// A group, `(` through its `)`, and what it leaves for a quantifier.
    fn group(&mut self, depth: usize) -> Result<Last, PyRegexError> {
        self.group_inner(depth)?;
        Ok(Last::Item)
    }

    fn group_inner(&mut self, depth: usize) -> Result<(), PyRegexError> {
        self.pos += 1; // `(`
        if self.peek() != Some('?') {
            return self.capturing(None, "(", depth);
        }
        self.pos += 1; // `?`
        match self.peek() {
            Some(':') => {
                self.pos += 1;
                self.out.push_str("(?:");
                self.group_body(depth).map(|_| ())
            }
            Some('P') => match self.peek_at(1) {
                Some('<') => {
                    self.pos += 2;
                    let name = self.name('>')?;
                    if self
                        .groups
                        .iter()
                        .any(|g| g.name.as_deref() == Some(name.as_str()))
                    {
                        return invalid(format!("redefinition of group name '{name}'"));
                    }
                    let open = format!("(?P<{name}>");
                    self.capturing(Some(name), &open, depth)
                }
                Some('=') => {
                    self.pos += 2;
                    let name = self.name(')')?;
                    match self
                        .groups
                        .iter()
                        .position(|g| g.name.as_deref() == Some(name.as_str()))
                    {
                        None => return invalid(format!("unknown group name '{name}'")),
                        Some(i) if !self.groups[i].closed => {
                            return invalid("cannot refer to an open group");
                        }
                        Some(i) => self.check_ref(i + 1)?,
                    }
                    self.defer("a named backreference `(?P=name)`");
                    Ok(())
                }
                _ => invalid("unknown extension ?P"),
            },
            // Lookaround and atomic groups: parsed as groups, so the rest of
            // the pattern is still checked.
            Some('=') => self
                .deferred_group(1, "a lookahead `(?=...)`", depth)
                .map(|_| ()),
            Some('!') => self
                .deferred_group(1, "a negative lookahead `(?!...)`", depth)
                .map(|_| ()),
            Some('<') => match self.peek_at(1) {
                Some('=') => self.lookbehind_group("a lookbehind `(?<=...)`", depth),
                Some('!') => self.lookbehind_group("a negative lookbehind `(?<!...)`", depth),
                _ => invalid("unknown extension ?<"),
            },
            Some('(') => {
                self.pos += 1;
                let id = self.name(')').or_else(|_| invalid("bad group name"))?;
                // A number may name a group defined later: Python checks it
                // once the whole pattern is read. A name must exist already.
                let index = if id.chars().all(|c| c.is_ascii_digit()) {
                    match id.parse::<usize>() {
                        Ok(n) if n >= 1 => {
                            self.max_condition_ref = self.max_condition_ref.max(n);
                            Some(n)
                        }
                        _ => None,
                    }
                } else {
                    self.groups
                        .iter()
                        .position(|g| g.name.as_deref() == Some(id.as_str()))
                        .map(|i| i + 1)
                };
                let Some(index) = index else {
                    if id.chars().all(|c| c.is_ascii_digit()) {
                        return invalid(format!("invalid group reference {id}"));
                    }
                    return invalid(format!("unknown group name '{id}'"));
                };
                self.check_ref(index)?;
                if self.deferred_group(0, "a conditional group `(?(...)...)`", depth)? > 2 {
                    return invalid("conditional backref with more than two branches");
                }
                Ok(())
            }
            Some('>') => self
                .deferred_group(1, "an atomic group `(?>...)`", depth)
                .map(|_| ()),
            Some(c) if c.is_ascii_alphabetic() || c == '-' => self.scoped_flags(depth),
            _ => invalid("unknown extension"),
        }
    }

    /// A lookbehind: deferred like the others, and while inside it a group
    /// reference follows Python's lookbehind rule (see [`Self::check_ref`]).
    fn lookbehind_group(&mut self, what: &str, depth: usize) -> Result<(), PyRegexError> {
        let outer = self.lookbehind;
        if outer.is_none() {
            self.lookbehind = Some(self.groups.len());
        }
        let result = self.deferred_group(2, what, depth).map(|_| ());
        self.lookbehind = outer;
        result
    }

    /// Inside a lookbehind, a reference to group `index` (1-based) must be
    /// to a closed group defined before the lookbehind, as Python's
    /// `checklookbehindgroup` requires.
    fn check_ref(&self, index: usize) -> Result<(), PyRegexError> {
        if let Some(before) = self.lookbehind {
            if !self.groups.get(index - 1).is_some_and(|g| g.closed) {
                return invalid("cannot refer to an open group");
            }
            if index > before {
                return invalid("cannot refer to group defined in the same lookbehind subpattern");
            }
        }
        Ok(())
    }

    /// Record `what` as the first construct rledger cannot express, if none
    /// is recorded yet, and go on parsing.
    fn defer(&mut self, what: &str) {
        if self.deferred.is_none() {
            self.deferred = Some(what.to_string());
        }
    }

    /// A group rledger cannot express, after `skip` more characters of its
    /// opening: parsed (and written) as a non-capturing group, so the rest of
    /// the pattern is checked, and recorded with [`Self::defer`].
    fn deferred_group(
        &mut self,
        skip: usize,
        what: &str,
        depth: usize,
    ) -> Result<usize, PyRegexError> {
        self.pos += skip;
        self.defer(what);
        self.out.push_str("(?:");
        self.group_body(depth)
    }

    /// A capturing group, its opening `open` already consumed from the
    /// pattern: numbered, written out, and its translated text recorded.
    fn capturing(
        &mut self,
        name: Option<String>,
        open: &str,
        depth: usize,
    ) -> Result<(), PyRegexError> {
        let index = self.groups.len();
        self.groups.push(GroupInfo {
            name,
            closed: false,
        });
        self.out.push_str(open);
        self.group_body(depth)?;
        self.groups[index].closed = true;
        Ok(())
    }

    /// A comment `(?#...)`, which Python drops.
    fn comment(&mut self) -> Result<(), PyRegexError> {
        self.pos += 3; // `(?#`
        while let Some(c) = self.peek() {
            self.pos += 1;
            if c == ')' {
                return Ok(());
            }
        }
        invalid("missing ), unterminated comment")
    }

    /// `(?flags:...)` or `(?flags-flags:...)`; a bare `(?flags)` here is not
    /// at the start of the pattern, which Python refuses.
    fn scoped_flags(&mut self, depth: usize) -> Result<(), PyRegexError> {
        let mut on = String::new();
        while let Some(c) = self.peek().filter(char::is_ascii_alphabetic) {
            on.push(c);
            self.pos += 1;
        }
        let mut off = String::new();
        if self.peek() == Some('-') {
            self.pos += 1;
            while let Some(c) = self.peek().filter(char::is_ascii_alphabetic) {
                off.push(c);
                self.pos += 1;
            }
            if off.is_empty() {
                return invalid("missing flag");
            }
        }
        match self.peek() {
            Some(':') => self.pos += 1,
            Some(')') => return invalid("global flags not at the start of the expression"),
            _ => return invalid("missing :"),
        }
        if off.chars().any(|c| matches!(c, 'a' | 'u' | 'L')) {
            return invalid("bad inline flags: cannot turn off flags 'a', 'u' and 'L'");
        }
        if on.chars().any(|c| off.contains(c)) {
            return invalid("bad inline flags: flag turned on and off");
        }
        // Turning verbose mode off is a no-op here.
        let off: String = off.chars().filter(|&c| c != 'x').collect();
        let on = self.flags(&on)?;
        let off = self.flags(&off)?;
        if off.is_empty() {
            write!(self.out, "(?{on}:").expect("writing to a String cannot fail");
        } else {
            write!(self.out, "(?{on}-{off}:").expect("writing to a String cannot fail");
        }
        self.group_body(depth).map(|_| ())
    }

    /// The body of a group through its `)`; returns its branch count.
    fn group_body(&mut self, depth: usize) -> Result<usize, PyRegexError> {
        if depth >= 100 {
            return unsupported("groups nested more than 100 deep");
        }
        let branches = self.alternation(depth + 1, true)?;
        self.pos += 1; // `)`
        self.out.push(')');
        Ok(branches)
    }

    /// A group name up to `close`, which Python requires to be an identifier.
    fn name(&mut self, close: char) -> Result<String, PyRegexError> {
        let mut name = String::new();
        loop {
            match self.peek() {
                Some(c) if c == close => {
                    self.pos += 1;
                    break;
                }
                Some(c) => {
                    name.push(c);
                    self.pos += 1;
                }
                None => return invalid("missing >, unterminated name"),
            }
        }
        if close == ')' && name.chars().all(|c| c.is_ascii_digit()) && !name.is_empty() {
            // A conditional's group number.
            return Ok(name);
        }
        let mut chars = name.chars();
        let valid = chars
            .next()
            .is_some_and(|c| c == '_' || c.is_ascii_alphabetic())
            && chars.all(|c| c == '_' || c.is_ascii_alphanumeric());
        if name.is_empty() {
            return invalid("missing group name");
        }
        if !is_identifier(&name) {
            return invalid(format!("bad character in group name '{name}'"));
        }
        if !valid {
            // Python also takes non-ASCII identifiers; `regex` group names
            // differ, so only ASCII ones are taken here.
            self.defer(&format!("the group name '{name}'"));
        }
        Ok(name)
    }

    /// An escape outside a class, written out; returns what it can take.
    fn escape(&mut self) -> Result<Last, PyRegexError> {
        self.pos += 1; // `\`
        let Some(c) = self.peek() else {
            return invalid("bad escape (end of pattern)");
        };
        self.pos += 1;
        match c {
            'A' => {
                self.out.push_str(r"\A");
                return Ok(Last::Nothing);
            }
            'Z' => {
                self.out.push_str(r"\z");
                return Ok(Last::Nothing);
            }
            'b' | 'B' => {
                self.defer(&format!(
                    "a word boundary `\\{c}` (Python defines words by its `\\w`, which rledger's engine cannot use for boundaries)"
                ));
                return Ok(Last::Nothing);
            }
            'd' => write!(self.out, "[{DIGIT}]"),
            'D' => write!(self.out, "[^{DIGIT}]"),
            's' => write!(self.out, "[{SPACE}]"),
            'S' => write!(self.out, "[^{SPACE}]"),
            'w' => write!(self.out, "[{WORD}]"),
            'W' => write!(self.out, "[^{WORD}]"),
            '1'..='9' => {
                // Three octal digits are an octal escape; anything else is a
                // group reference.
                if let (Some(b), Some(d)) = (self.peek(), self.peek_at(1))
                    && c <= '7'
                    && ('0'..='7').contains(&b)
                    && ('0'..='7').contains(&d)
                {
                    let code = (c as u32 - 48) * 64 + (b as u32 - 48) * 8 + (d as u32 - 48);
                    if code > 0o377 {
                        return invalid("octal escape value outside of range 0-0o377");
                    }
                    self.pos += 2;
                    self.push_code(code)?;
                    return Ok(Last::Item);
                }
                // A group reference of one or two digits, to a group already
                // closed, as Python requires.
                let mut index = c.to_digit(10).expect("a digit") as usize;
                if let Some(d) = self.peek().and_then(|d| d.to_digit(10)) {
                    index = index * 10 + d as usize;
                    self.pos += 1;
                }
                if index > self.groups.len() {
                    return invalid(format!("invalid group reference {index}"));
                }
                if !self.groups[index - 1].closed {
                    return invalid("cannot refer to an open group");
                }
                self.check_ref(index)?;
                self.defer("a backreference (`\\1` and the like)");
                return Ok(Last::Item);
            }
            c => {
                let code = self.char_escape(c, false)?;
                self.push_code(code)?;
                return Ok(Last::Item);
            }
        }
        .expect("writing to a String cannot fail");
        Ok(Last::Item)
    }

    fn push_code(&mut self, code: u32) -> Result<(), PyRegexError> {
        let c = char::from_u32(code).ok_or(PyRegexError::Invalid("bad escape".into()))?;
        self.push_literal(c);
        Ok(())
    }

    /// The character an escape `\c` (backslash already consumed, `c` too)
    /// stands for, when it stands for one character: in a class (`in_class`)
    /// `\b` is a backspace.
    fn char_escape(&mut self, c: char, in_class: bool) -> Result<u32, PyRegexError> {
        Ok(match c {
            'a' => 7,
            'b' if in_class => 8,
            'f' => 12,
            'n' => 10,
            'r' => 13,
            't' => 9,
            'v' => 11,
            'x' => self.hex(2)?,
            'u' => self.hex(4)?,
            'U' => {
                let code = self.hex(8)?;
                if code > 0x0010_FFFF {
                    return invalid("bad escape \\U");
                }
                code
            }
            'N' => {
                if self.peek() != Some('{') {
                    return invalid("missing {");
                }
                if self.peek_at(1) == Some('}') {
                    return invalid("missing character name");
                }
                while let Some(c) = self.peek() {
                    self.pos += 1;
                    if c == '}' {
                        self.defer("a named character escape `\\N{...}`");
                        return Ok(u32::from('?'));
                    }
                }
                return invalid("missing }, unterminated name");
            }
            '0' => {
                let mut code = 0;
                for _ in 0..2 {
                    match self.peek().and_then(|c| c.to_digit(8)) {
                        Some(d) => {
                            code = code * 8 + d;
                            self.pos += 1;
                        }
                        None => break,
                    }
                }
                code
            }
            c if c.is_ascii_alphanumeric() => return invalid(format!("bad escape \\{c}")),
            // Any other escaped character is that character.
            c => c as u32,
        })
    }

    fn hex(&mut self, len: usize) -> Result<u32, PyRegexError> {
        let digits: String = (0..len).filter_map(|i| self.peek_at(i)).collect();
        if digits.chars().count() != len || !digits.chars().all(|c| c.is_ascii_hexdigit()) {
            return invalid("incomplete escape");
        }
        self.pos += len;
        Ok(u32::from_str_radix(&digits, 16).expect("hex digits"))
    }

    /// A character class, `[` through its `]`, with every member written
    /// out explicitly, so nothing in it reads as `regex`'s nested classes,
    /// POSIX classes or set operations.
    fn class(&mut self) -> Result<(), PyRegexError> {
        self.pos += 1; // `[`
        let mut out = String::from("[");
        if self.peek() == Some('^') {
            self.pos += 1;
            out.push('^');
        }
        let mut first = true;
        // At least one member is written: Python takes a `]` first as a member.
        loop {
            let Some(c) = self.peek() else {
                return invalid("unterminated character set");
            };
            if c == ']' && !first {
                self.pos += 1;
                break;
            }
            first = false;
            let lo = self.class_member()?;
            // A range `lo-hi`, unless the `-` is last.
            if self.peek() == Some('-') && self.peek_at(1).is_some_and(|c| c != ']') {
                self.pos += 1;
                let hi = self.class_member()?;
                match (lo, hi) {
                    (Member::Char(lo), Member::Char(hi)) => {
                        if hi < lo {
                            return invalid("bad character range");
                        }
                        out.push_str(&escape_class_char(lo));
                        out.push('-');
                        out.push_str(&escape_class_char(hi));
                    }
                    _ => return invalid("bad character range"),
                }
            } else {
                match lo {
                    Member::Char(c) => out.push_str(&escape_class_char(c)),
                    Member::Set(set) => out.push_str(set),
                    Member::NegatedSet(set) => {
                        write!(out, "[^{set}]").expect("writing to a String cannot fail");
                    }
                }
            }
        }
        out.push(']');
        self.out.push_str(&out);
        Ok(())
    }

    fn class_member(&mut self) -> Result<Member, PyRegexError> {
        let c = self
            .peek()
            .ok_or(PyRegexError::Invalid("unterminated character set".into()))?;
        self.pos += 1;
        if c != '\\' {
            return Ok(Member::Char(c));
        }
        let Some(e) = self.peek() else {
            return invalid("unterminated character set");
        };
        self.pos += 1;
        Ok(match e {
            'd' => Member::Set(DIGIT),
            'D' => Member::NegatedSet(DIGIT),
            's' => Member::Set(SPACE),
            'S' => Member::NegatedSet(SPACE),
            'w' => Member::Set(WORD),
            'W' => Member::NegatedSet(WORD),
            // In a class an octal digit starts an octal escape of up to three
            // digits; it is never a backreference.
            '0'..='7' => {
                let mut code = e as u32 - 48;
                for _ in 0..2 {
                    match self.peek().and_then(|c| c.to_digit(8)) {
                        Some(d) => {
                            code = code * 8 + d;
                            self.pos += 1;
                        }
                        None => break,
                    }
                }
                if code > 0o377 {
                    return invalid("octal escape value outside of range 0-0o377");
                }
                Member::Char(char::from_u32(code).expect("below 0o377"))
            }
            '8' | '9' => return invalid(format!("bad escape \\{e}")),
            'A' | 'Z' | 'B' => return invalid(format!("bad escape \\{e}")),
            e => {
                let code = self.char_escape(e, true)?;
                Member::Char(
                    char::from_u32(code).ok_or(PyRegexError::Invalid("bad escape".into()))?,
                )
            }
        })
    }
}

/// One member of a character class.
enum Member {
    Char(char),
    /// Python's `\d`, `\s`, `\w`, as class members.
    Set(&'static str),
    /// `\D`, `\S`, `\W`.
    NegatedSet(&'static str),
}

/// `c` as a `regex` class member, escaped when it is punctuation `regex`
/// treats specially in a class (`[`, `]`, `-`, `^`, `&`, `~`, `\`, ...).
fn escape_class_char(c: char) -> String {
    regex::escape(c.encode_utf8(&mut [0; 4]))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Whether `pattern` matches `text` at its start, as Python's
    /// `re.match(pattern, text)` is truthy.
    fn py_match(pattern: &str, text: &str) -> bool {
        compile_match(pattern)
            .unwrap_or_else(|e| panic!("{pattern:?}: {e}"))
            .is_match(text)
    }

    /// Each row's expected value is what Python 3.12's
    /// `bool(re.match(pattern, text))` gives.
    #[test]
    fn matches_as_python_re_match() {
        let cases: &[(&str, &str, bool)] = &[
            // Plain account patterns.
            ("Assets:.*", "Assets:Cash", true),
            ("Cash", "Assets:Cash", false),
            ("Assets:Cash", "Assets:Cash:Sub", true),
            ("Assets:Cash$", "Assets:Cash:Sub", false),
            // `[[:alpha:]]` is not a POSIX class in Python: it is the set
            // `[`, `:`, `a`, `l`, `p`, `h` followed by a literal `]`.
            ("[[:alpha:]]", "a", false),
            ("[[:alpha:]]", "a]", true),
            ("[[:alpha:]]", ":]", true),
            ("[[:alpha:]]+", "x", false),
            // `&&`, `--`, `~~` are literal characters in a Python class.
            ("[a&&b]", "&", true),
            ("[a&&b]", "b", true),
            (r"[\1]", "\x01", true),
            (r"[\18]", "8", true),
            ("[+--]", ",", true),
            ("[a~~b]", "~", true),
            // `\<` and `\>` are literal `<` and `>`.
            (r"\<x\>", "<x>", true),
            (r"\<x\>", "x", false),
            // A brace that is not a quantifier is a literal.
            ("a{", "a{", true),
            ("a{,2}b", "aab", true),
            ("a{,2}b", "aaab", false),
            ("a{1,}", "a", true),
            ("x{}", "x{}", true),
            ("x{a}", "x{a}", true),
            // `]` first in a class, and `-` at either end, are members.
            ("[]a]", "]", true),
            ("[^]a]", "]", false),
            ("[^]a]", "b", true),
            ("[-a]", "-", true),
            ("[a-]", "-", true),
            // Escapes.
            (r"\.", ".", true),
            (r"\.", "x", false),
            (r"\x41", "A", true),
            (r"\u0041", "A", true),
            (r"\101", "A", true),
            (r"\0", "\0", true),
            (r"[\b]", "\x08", true),
            (r"\Z", "", true),
            (r"a\Z", "ab", false),
            // Python's `\w`: `str.isalnum()` or `_`. `½` is numeric to
            // Python; a combining mark is not alphanumeric.
            (r"\w", "½", true),
            (r"\w", "\u{301}", false),
            (r"\w", "_", true),
            (r"\W", "-", true),
            // Python's `\s` includes the information separators.
            (r"\s", "\x1c", true),
            (r"\S", "\x1c", false),
            (r"[\s]", "\x1f", true),
            (r"\d", "٣", true),
            (r"[\d-]", "-", true),
            // Comments, flags, groups.
            ("a(?#comment)b", "ab", true),
            // A comment does not stop the flags after it being global, and
            // what follows it repeats the item before it.
            ("(?#c)(?i)a", "A", true),
            ("a(?#c)*b", "aab", true),
            ("(?i)assets", "ASSETS", true),
            ("(?i:a)A", "aA", true),
            ("(?i:a)A", "aa", false),
            ("(?P<x>a)b", "ab", true),
            ("(a|b)+c", "abac", true),
            ("a*?b", "aab", true),
        ];
        let wrong: Vec<_> = cases
            .iter()
            .filter(|(pattern, text, want)| py_match(pattern, text) != *want)
            .collect();
        assert!(wrong.is_empty(), "differ from Python: {wrong:?}");
    }

    #[test]
    fn constructs_python_has_and_rledger_lacks_are_named() {
        for (pattern, construct) in [
            ("Assets:(?=Cash)", "lookahead"),
            ("Assets:(?!Cash)", "negative lookahead"),
            ("(?<=Assets:)Cash", "lookbehind"),
            ("(?<!Assets:)Cash", "negative lookbehind"),
            (r"(a)\1", "backreference"),
            ("(?P<x>a)(?P=x)", "named backreference"),
            ("(a)?(?(1)b|c)", "conditional"),
            // A conditional may name a group defined after it, as in Python.
            ("(?(1)a|b)(c)", "conditional"),
            ("(c)(?(2)a|b)(d)", "conditional"),
            ("(?(1)(a)|b)", "conditional"),
            // Inside a lookbehind, a group closed before it may be used.
            (r"(a)(?<=\1)b", "lookbehind"),
            ("(?>a)", "atomic group"),
            ("a*+", "possessive"),
            ("a{1,2}+", "possessive"),
            (r"\N{DIGIT ONE}", "named character escape"),
            ("(?a)x", "ASCII flag"),
            ("(?x)x", "verbose flag"),
            (r"\bx", "word boundary"),
            (r"\Bx", "word boundary"),
        ] {
            match translate(pattern) {
                Err(PyRegexError::Unsupported(what)) => {
                    assert!(what.contains(construct), "{pattern:?}: {what}");
                }
                other => panic!("{pattern:?} must be unsupported: {other:?}"),
            }
        }
    }

    /// Patterns Python's `re.compile` rejects are rejected, not guessed at.
    #[test]
    fn patterns_python_rejects_are_invalid() {
        for pattern in [
            "(",
            ")",
            "a)",
            "[a",
            "*a",
            "a**",
            "^*",
            r"\p{L}",
            r"\z",
            r"\e",
            "(?<n>a)",
            "a(?i)b",
            "(?L)a",
            "(?Q)a",
            "[z-a]",
            "[a--z]",
            r"[a-\d]",
            r"\x4",
            r"[\8]",
            r"[\A]",
            "a{2,1}",
            "(?P<a>x)(?P<a>y)",
            r"\",
            r"\A(?#c){,2}",
            // Python rejects these for reasons of their own, which win over
            // the unsupported construct in them.
            "(?=A",
            r"(a\1)",
            "(?P<x>a(?P=x))",
            "(x)(?(1)a|b|c)",
            "(?P<1a>x)",
            "(?P<a-b>x)",
            "(?au:a)",
            r"\N{}",
            "(?(3)a|b)(c)",
            r"(?<=(a)\1)",
            "(?<=(?P<n>a)(?P=n))",
            "(?<=(c)(?(1)b))",
            "(?<=a(?(1)b))(c)",
            r"\b(",
            r"\1",
            "(?P=x)",
            "(?(1)a|b)",
            r"\b{2}",
            r"\N{DIGIT ONE",
        ] {
            assert!(
                matches!(translate(pattern), Err(PyRegexError::Invalid(_))),
                "{pattern:?} must be invalid: {:?}",
                translate(pattern)
            );
        }
    }

    /// `re.sub` templates: Python 3.12's `re.sub(pattern, template, text)`.
    #[test]
    fn replacements_follow_python_re_sub() {
        for (pattern, template, text, want) in [
            (
                "Expenses:Food:(.*)",
                r"Expenses:Dining:\1",
                "Expenses:Food:Lunch",
                "Expenses:Dining:Lunch",
            ),
            (
                "Expenses:Food:(.*)",
                r"Expenses:Dining:\g<1>",
                "Expenses:Food:Lunch",
                "Expenses:Dining:Lunch",
            ),
            (
                "Expenses:Food:(?P<rest>.*)",
                r"X:\g<rest>",
                "Expenses:Food:Lunch",
                "X:Lunch",
            ),
            // `$1` is literal text to Python.
            (
                "Expenses:Food:(.*)",
                "Expenses:Dining:$1",
                "Expenses:Food:Lunch",
                "Expenses:Dining:$1",
            ),
            (
                "Food",
                "Dining",
                "Expenses:Food:Food",
                "Expenses:Dining:Dining",
            ),
            ("(a)", r"\\1", "a", r"\1"),
            ("(a)", r"\&", "a", r"\&"),
            ("(a)", r"\101", "a", "A"),
            ("(a)", r"\b", "a", "\x08"),
            // A group inside `{0}` still counts, and is empty.
            ("(a){0}b", r"[\1]", "xb", "x[]"),
            ("(?P<x>a){0}(?P<y>b)", r"[\g<x>\g<y>]", "xb", "x[b]"),
            // A repeated group that cannot match empty is fine.
            ("(a)+b", r"[\1]", "aab", "[a]"),
        ] {
            let re = compile_sub(pattern).unwrap();
            let rust = translate_replacement(template, &re).unwrap();
            assert_eq!(
                re.regex.replace_all(text, rust.as_str()),
                want,
                "{pattern:?} {template:?}"
            );
        }
        let re = compile_sub("(a)").unwrap();
        for template in [r"\2", r"\g<x>", r"\g<5>", r"\q", "\\", r"\g<+1>", r"\g< 1>"] {
            assert!(
                matches!(
                    translate_replacement(template, &re),
                    Err(PyRegexError::Invalid(_))
                ),
                "{template:?}"
            );
        }
    }

    /// Inline flags as Python reads them: a repeated letter is fine, a flag
    /// both on and off, or `u` turned off, is refused.
    #[test]
    fn inline_flags_follow_python() {
        assert!(py_match("(?ii)a", "A"));
        assert!(py_match("(?ii:a)", "A"));
        // Turning verbose mode off is a no-op.
        assert!(py_match("(?-x:a)", "a"));
        for pattern in ["(?i-i:a)", "(?im-m:a)", "(?-u:a)", "(?u-u:a)", "(?-a:a)"] {
            assert!(
                matches!(translate(pattern), Err(PyRegexError::Invalid(_))),
                "{pattern:?}: {:?}",
                translate(pattern)
            );
        }
    }

    /// What `re.sub` and `replace_all` do differently is refused, never
    /// substituted differently: a pattern that can match empty (Python's
    /// `re.sub('x*', '-', 'abxd')` is `-a-b--d-`, `replace_all` gives
    /// `-a-b-d-`), and a reference to a repeated group that can match empty
    /// (Python's `re.sub('(a*)+b', r'[\1]', 'aab')` is `[]`).
    #[test]
    fn substitutions_python_makes_differently_are_refused() {
        for pattern in ["x*", "(:Cash)?$", "|a", "^", "(a*)"] {
            assert!(
                matches!(compile_sub(pattern), Err(PyRegexError::Unsupported(ref w)) if w.contains("empty string")),
                "{pattern:?}"
            );
        }
        for pattern in [
            "(a*)+b",
            "b(?:a?|c)*",
            "b(?:a*|c)+",
            "Assets:(?:\\w*|:)+",
            "x(a|)+",
        ] {
            assert!(
                matches!(compile_sub(pattern), Err(PyRegexError::Unsupported(ref w)) if w.contains("repetition")),
                "{pattern:?}: {:?}",
                compile_sub(pattern).map(|_| ())
            );
        }
        // A repetition whose body cannot match empty is fine, and so is a
        // repeated group inside one that can (every iteration sets it).
        for pattern in ["(a)+b", "(?:(a*)b)+", "x(?:ab|a)*", "(\\w+):(\\w+)"] {
            assert!(compile_sub(pattern).is_ok(), "{pattern:?}");
        }
    }
}
