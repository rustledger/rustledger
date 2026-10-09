//! A Python literal, read the way `ast.literal_eval` reads a plugin's config
//! string.
//!
//! The upstream Python plugins take their config as a Python literal and call
//! `literal_eval` on it, so what they accept and reject is Python's grammar,
//! not a pattern. This reads the part of that grammar a config can use:
//! strings (single, double and triple quotes, the `r`, `u` and `b` prefixes,
//! the escapes, adjacent strings concatenated), numbers, `None`, `True`,
//! `False`, and dicts, lists, tuples and sets of those, with comments and
//! trailing commas. What `literal_eval` rejects, this rejects: names, calls,
//! f-strings, unbalanced brackets, a missing comma, trailing text.
//!
//! Not covered, and so rejected though `literal_eval` would accept them:
//! `\N{...}` escapes, complex numbers, and arithmetic between number literals.

/// A parsed Python literal.
#[derive(Debug, Clone, PartialEq)]
pub enum PyValue {
    /// `None`.
    None,
    /// `True` or `False`.
    Bool(bool),
    /// A number literal, kept as written; `zero` says whether it is falsy.
    Number {
        /// The literal's text.
        text: String,
        /// Whether its value is zero.
        zero: bool,
    },
    /// A `str`.
    Str(String),
    /// A `bytes` literal.
    Bytes(Vec<u8>),
    /// A list, tuple or set.
    Seq(Vec<Self>),
    /// A dict, its entries in source order, repeated keys included (the
    /// caller decides, as Python does, that the last value wins).
    Dict(Vec<(Self, Self)>),
}

impl PyValue {
    /// Python truthiness: `None`, `False`, zero, and empty strings and
    /// containers are falsy.
    pub fn is_truthy(&self) -> bool {
        match self {
            Self::None => false,
            Self::Bool(b) => *b,
            Self::Number { zero, .. } => !zero,
            Self::Str(s) => !s.is_empty(),
            Self::Bytes(b) => !b.is_empty(),
            Self::Seq(items) => !items.is_empty(),
            Self::Dict(entries) => !entries.is_empty(),
        }
    }
}

/// Parse `source` as one Python literal, as `ast.literal_eval` does.
///
/// # Errors
///
/// A message naming what was found where a literal, or the end of the text,
/// was expected.
pub fn parse(source: &str) -> Result<PyValue, String> {
    // Python reads `\r\n` and a lone `\r` as `\n`, inside strings too, so a
    // config written in a CRLF ledger parses the same as in an LF one.
    let mut parser = Parser {
        chars: source
            .replace("\r\n", "\n")
            .replace('\r', "\n")
            .chars()
            .collect(),
        pos: 0,
    };
    // `literal_eval` strips leading spaces and tabs, then parses in eval
    // mode, where every other line is indentation-checked: blank and
    // comment-only lines are skipped, and the line holding a token must not
    // be indented.
    while matches!(parser.peek(), Some(' ' | '\t')) {
        parser.pos += 1;
    }
    loop {
        match parser.line_start()? {
            Line::Token | Line::End => break,
            Line::Blank => {
                parser.skip_trivia(0);
                if parser.peek() == Some('\n') {
                    parser.pos += 1;
                }
            }
        }
    }
    let value = parser.value(0)?;
    // After it, only blank and comment lines. A backslash continuation with
    // nothing after it is a syntax error in Python.
    loop {
        parser.skip_trivia(0);
        match parser.peek() {
            None => return Ok(value),
            Some('\n') => {
                parser.pos += 1;
                match parser.line_start()? {
                    Line::End => return Ok(value),
                    Line::Blank => {}
                    Line::Token => {
                        let c = parser.peek().unwrap_or(' ');
                        return Err(format!("unexpected `{c}` after the literal"));
                    }
                }
            }
            Some(c) => return Err(format!("unexpected `{c}` after the literal")),
        }
    }
}

/// What a top-level physical line holds, after its indentation.
enum Line {
    /// A token: the literal, or text after it.
    Token,
    /// Nothing but a comment or the line break.
    Blank,
    /// The end of the text.
    End,
}

struct Parser {
    chars: Vec<char>,
    pos: usize,
}

impl Parser {
    /// Read a top-level line's indentation, as Python's tokenizer does:
    /// spaces and tabs count, a form feed resets the count, and a backslash
    /// continuation keeps counting on the next line. A token on an indented
    /// line is an error ("unexpected indent"), and so is an indented last
    /// line with nothing on it and no line break; blank and comment-only
    /// lines may be indented.
    fn line_start(&mut self) -> Result<Line, String> {
        let mut indent = 0usize;
        loop {
            match self.peek() {
                Some(' ' | '\t') => {
                    indent += 1;
                    self.pos += 1;
                }
                Some('\x0c') => {
                    indent = 0;
                    self.pos += 1;
                }
                Some('\\') if self.peek_at(1) == Some('\n') && self.pos + 2 < self.chars.len() => {
                    self.pos += 2;
                }
                _ => break,
            }
        }
        match self.peek() {
            None if indent > 0 => Err("unexpected indent at the end of the text".to_string()),
            None => Ok(Line::End),
            Some('\n' | '#') => Ok(Line::Blank),
            Some(_) if indent > 0 => Err("unexpected indent".to_string()),
            Some(_) => Ok(Line::Token),
        }
    }
}

/// How deep brackets may nest. Python's parser stops at 200 ("too many nested
/// parentheses"), and a limit keeps hostile input from exhausting the stack.
const MAX_DEPTH: usize = 200;

impl Parser {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.chars.get(self.pos + offset).copied()
    }

    /// Skip whitespace and comments. Line breaks only count as whitespace
    /// inside brackets (`depth > 0`), as in Python; at the top level a line
    /// break ends the expression unless a backslash continues the line.
    fn skip_trivia(&mut self, depth: usize) {
        loop {
            match self.peek() {
                Some(' ' | '\t' | '\x0c') => self.pos += 1,
                Some('\n' | '\r') if depth > 0 => self.pos += 1,
                // A continuation needs something after it, even only a line
                // break or a comment: Python rejects one at the very end.
                Some('\\')
                    if matches!(self.peek_at(1), Some('\n')) && self.pos + 2 < self.chars.len() =>
                {
                    self.pos += 2;
                }
                Some('#') => {
                    while !matches!(self.peek(), None | Some('\n')) {
                        self.pos += 1;
                    }
                }
                _ => return,
            }
        }
    }

    fn value(&mut self, depth: usize) -> Result<PyValue, String> {
        self.skip_trivia(depth);
        match self.peek() {
            None => Err("expected a literal, found the end of the text".to_string()),
            Some('{') => self.dict_or_set(depth),
            Some('[') => self.seq(']', depth),
            Some('(') => self.seq(')', depth),
            Some('-' | '+') => {
                // One sign, on a number literal: `literal_eval` takes `-1`
                // and `- 1`, not `--1` or `-True`.
                let sign = self.peek().unwrap_or('+');
                self.pos += 1;
                self.skip_trivia(depth);
                let starts_number = self.peek().is_some_and(|c| {
                    c.is_ascii_digit()
                        || (c == '.' && self.peek_at(1).is_some_and(|d| d.is_ascii_digit()))
                });
                if !starts_number {
                    return Err(format!("`{sign}` applies only to a number"));
                }
                match self.number()? {
                    PyValue::Number { text, zero } => Ok(PyValue::Number {
                        text: format!("{sign}{text}"),
                        zero,
                    }),
                    _ => Err(format!("`{sign}` applies only to a number")),
                }
            }
            Some(c)
                if c.is_ascii_digit()
                    || (c == '.' && self.peek_at(1).is_some_and(|d| d.is_ascii_digit())) =>
            {
                self.number()
            }
            Some(c) if c == '\'' || c == '"' || c.is_ascii_alphabetic() || c == '_' => {
                self.word_or_string(depth)
            }
            Some(c) => Err(format!("unexpected `{c}`")),
        }
    }

    fn dict_or_set(&mut self, depth: usize) -> Result<PyValue, String> {
        self.pos += 1; // `{`
        let depth = depth + 1;
        if depth > MAX_DEPTH {
            return Err("too many nested brackets".to_string());
        }
        let mut entries = Vec::new();
        let mut items = Vec::new();
        loop {
            self.skip_trivia(depth);
            if self.peek() == Some('}') {
                self.pos += 1;
                break;
            }
            let key = self.value(depth)?;
            self.skip_trivia(depth);
            if self.peek() == Some(':') {
                if !items.is_empty() {
                    return Err("a set cannot hold `key: value` entries".to_string());
                }
                self.pos += 1;
                let value = self.value(depth)?;
                entries.push((key, value));
            } else {
                if !entries.is_empty() {
                    return Err("expected `:` after a dict key".to_string());
                }
                items.push(key);
            }
            self.skip_trivia(depth);
            match self.peek() {
                Some(',') => self.pos += 1,
                Some('}') => {}
                Some(c) => return Err(format!("expected `,` or `}}`, found `{c}`")),
                None => return Err("unclosed `{`".to_string()),
            }
        }
        Ok(if items.is_empty() {
            PyValue::Dict(entries)
        } else {
            PyValue::Seq(items)
        })
    }

    fn seq(&mut self, close: char, depth: usize) -> Result<PyValue, String> {
        self.pos += 1; // `[` or `(`
        let depth = depth + 1;
        if depth > MAX_DEPTH {
            return Err("too many nested brackets".to_string());
        }
        let mut items = Vec::new();
        let mut saw_comma = false;
        loop {
            self.skip_trivia(depth);
            if self.peek() == Some(close) {
                self.pos += 1;
                break;
            }
            items.push(self.value(depth)?);
            self.skip_trivia(depth);
            match self.peek() {
                Some(',') => {
                    self.pos += 1;
                    saw_comma = true;
                }
                Some(c) if c == close => {}
                Some(c) => return Err(format!("expected `,` or `{close}`, found `{c}`")),
                None => return Err(format!("unclosed bracket, expected `{close}`")),
            }
        }
        // `(x)` is the value itself, not a tuple.
        if close == ')' && items.len() == 1 && !saw_comma {
            return Ok(items.pop().unwrap_or(PyValue::None));
        }
        Ok(PyValue::Seq(items))
    }

    fn number(&mut self) -> Result<PyValue, String> {
        let start = self.pos;
        while let Some(c) = self.peek() {
            let exponent_sign = matches!(c, '+' | '-')
                && matches!(self.chars.get(self.pos.wrapping_sub(1)), Some('e' | 'E'))
                && !self.chars[start..self.pos]
                    .iter()
                    .any(|c| matches!(c, 'x' | 'X'));
            if c.is_ascii_alphanumeric() || c == '.' || c == '_' || exponent_sign {
                self.pos += 1;
            } else {
                break;
            }
        }
        let text: String = self.chars[start..self.pos].iter().collect();
        // An underscore must sit between two digits (or right after a base
        // prefix, `0x_ff`): Python rejects `1__0`, `1_` and `1_.5`.
        let chars: Vec<char> = text.chars().collect();
        for (i, c) in chars.iter().enumerate() {
            if *c != '_' {
                continue;
            }
            let before = i.checked_sub(1).and_then(|j| chars.get(j)).copied();
            let after = chars.get(i + 1).copied();
            let after_prefix =
                i == 2 && chars[0] == '0' && matches!(chars[1], 'x' | 'X' | 'o' | 'O' | 'b' | 'B');
            if !(before.is_some_and(|b| b.is_ascii_hexdigit()) || after_prefix)
                || !after.is_some_and(|a| a.is_ascii_hexdigit())
            {
                return Err(format!("invalid number `{text}`"));
            }
        }
        let digits = text.replace('_', "");
        // An imaginary literal (`1j`) is a number too; only its truthiness
        // matters here.
        let stripped = digits
            .strip_suffix(['j', 'J'])
            .filter(|d| !d.to_ascii_lowercase().starts_with("0x"));
        let imaginary = stripped.is_some();
        let digits = stripped.unwrap_or(&digits).to_string();
        let lower = digits.to_ascii_lowercase();
        // A based integer of any length (Python's are unbounded): valid
        // digits, and zero when every digit is.
        let based = |digits: &str, radix: u32| -> Result<bool, String> {
            if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
                return Err(format!("invalid number `{text}`"));
            }
            Ok(digits.chars().all(|c| c == '0'))
        };
        let zero = if let Some(hex) = lower.strip_prefix("0x") {
            based(hex, 16)?
        } else if let Some(oct) = lower.strip_prefix("0o") {
            based(oct, 8)?
        } else if let Some(bin) = lower.strip_prefix("0b") {
            based(bin, 2)?
        } else {
            let value: f64 = lower
                .parse()
                .map_err(|_| format!("invalid number `{text}`"))?;
            let integer = !lower.contains(['.', 'e']) && !imaginary;
            // Python rejects a leading zero on a non-zero integer (`07`).
            if integer && lower.len() > 1 && lower.starts_with('0') && value != 0.0 {
                return Err(format!("invalid number `{text}`"));
            }
            // And a decimal integer of more than 4300 digits ("Exceeds the
            // limit (4300 digits) for integer string conversion"), unless it
            // is all zeros.
            if integer && lower.len() > 4300 && value != 0.0 {
                return Err(format!("`{text:.20}...` has more than 4300 digits"));
            }
            value == 0.0
        };
        Ok(PyValue::Number { text, zero })
    }

    fn word_or_string(&mut self, depth: usize) -> Result<PyValue, String> {
        let start = self.pos;
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            self.pos += 1;
        }
        let word: String = self.chars[start..self.pos].iter().collect();
        if matches!(self.peek(), Some('\'' | '"')) {
            // A string with this prefix, then any adjacent strings.
            self.pos = start;
            return self.strings(depth);
        }
        match word.as_str() {
            "None" => Ok(PyValue::None),
            "True" => Ok(PyValue::Bool(true)),
            "False" => Ok(PyValue::Bool(false)),
            _ => Err(format!("`{word}` is a name, not a literal")),
        }
    }

    /// One or more adjacent string literals, concatenated.
    fn strings(&mut self, depth: usize) -> Result<PyValue, String> {
        let mut text = String::new();
        let mut bytes: Option<Vec<u8>> = None;
        let mut any = false;
        loop {
            self.skip_trivia(depth);
            let start = self.pos;
            while self.peek().is_some_and(|c| c.is_ascii_alphabetic()) {
                self.pos += 1;
            }
            let prefix: String = self.chars[start..self.pos]
                .iter()
                .collect::<String>()
                .to_ascii_lowercase();
            if !matches!(self.peek(), Some('\'' | '"')) {
                self.pos = start;
                break;
            }
            let (raw, is_bytes) = match prefix.as_str() {
                "" | "u" => (false, false),
                "r" => (true, false),
                "b" => (false, true),
                "br" | "rb" => (true, true),
                "f" | "rf" | "fr" => return Err("an f-string is not a literal".to_string()),
                other => return Err(format!("`{other}` is not a string prefix")),
            };
            if any && is_bytes != bytes.is_some() {
                return Err("cannot mix bytes and str literals".to_string());
            }
            let part = self.string_body(raw, is_bytes)?;
            if is_bytes {
                let b = bytes.get_or_insert_with(Vec::new);
                for c in part.chars() {
                    let code = u32::from(c);
                    if code > 0xff {
                        return Err("bytes can only contain ASCII characters".to_string());
                    }
                    b.push(u8::try_from(code).unwrap_or(0));
                }
            } else {
                text.push_str(&part);
            }
            any = true;
        }
        Ok(match bytes {
            Some(b) => PyValue::Bytes(b),
            None => PyValue::Str(text),
        })
    }

    /// The quoted part of one string literal, escapes resolved unless `raw`.
    /// In a bytes literal (`is_bytes`) `\u`, `\U` and `\N` are not escapes
    /// and keep their backslash, as in Python.
    fn string_body(&mut self, raw: bool, is_bytes: bool) -> Result<String, String> {
        let quote = self.peek().unwrap_or('\'');
        let triple = self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote);
        self.pos += if triple { 3 } else { 1 };
        let mut out = String::new();
        loop {
            let Some(c) = self.peek() else {
                return Err("unterminated string".to_string());
            };
            if c == quote
                && (!triple || (self.peek_at(1) == Some(quote) && self.peek_at(2) == Some(quote)))
            {
                self.pos += if triple { 3 } else { 1 };
                return Ok(out);
            }
            if (c == '\n' || c == '\r') && !triple {
                return Err("unterminated string".to_string());
            }
            self.pos += 1;
            if c != '\\' {
                if is_bytes && !c.is_ascii() {
                    return Err("bytes can only contain ASCII literal characters".to_string());
                }
                out.push(c);
                continue;
            }
            let Some(next) = self.peek() else {
                return Err("unterminated string".to_string());
            };
            self.pos += 1;
            if raw {
                out.push('\\');
                out.push(next);
                continue;
            }
            match next {
                '\n' => {}
                '\\' => out.push('\\'),
                '\'' => out.push('\''),
                '"' => out.push('"'),
                'a' => out.push('\x07'),
                'b' => out.push('\x08'),
                'f' => out.push('\x0c'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'v' => out.push('\x0b'),
                '0'..='7' => {
                    let mut code = next.to_digit(8).unwrap_or(0);
                    for _ in 0..2 {
                        match self.peek().and_then(|d| d.to_digit(8)) {
                            Some(d) => {
                                code = code * 8 + d;
                                self.pos += 1;
                            }
                            None => break,
                        }
                    }
                    out.push(char::from_u32(code).ok_or("invalid octal escape")?);
                }
                'x' => out.push(self.hex_escape(2)?),
                'u' | 'U' | 'N' if is_bytes => {
                    out.push('\\');
                    out.push(next);
                }
                'u' => out.push(self.hex_escape(4)?),
                'U' => out.push(self.hex_escape(8)?),
                'N' => return Err("`\\N{...}` escapes are not supported".to_string()),
                // An unknown escape keeps its backslash, as Python does.
                other => {
                    out.push('\\');
                    out.push(other);
                }
            }
        }
    }

    fn hex_escape(&mut self, len: usize) -> Result<char, String> {
        let digits: String = self
            .chars
            .get(self.pos..self.pos + len)
            .map(|s| s.iter().collect())
            .unwrap_or_default();
        if digits.len() != len || !digits.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err("truncated `\\x`/`\\u` escape".to_string());
        }
        self.pos += len;
        let code = u32::from_str_radix(&digits, 16).map_err(|e| e.to_string())?;
        char::from_u32(code).ok_or_else(|| "invalid escape".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The value class `parse` gives, in the form the Python oracle printed:
    /// `str:<text>`, `bytes:<hex>`, `num:0` / `num:nz`, `seq<n>`, `dict<n>`,
    /// `True` / `False` / `None`, or `ERR`.
    fn class(source: &str) -> String {
        match parse(source) {
            Err(_) => "ERR".to_string(),
            Ok(PyValue::None) => "None".to_string(),
            Ok(PyValue::Bool(b)) => if b { "True" } else { "False" }.to_string(),
            Ok(PyValue::Number { zero, .. }) => if zero { "num:0" } else { "num:nz" }.to_string(),
            Ok(PyValue::Str(s)) => format!("str:{s}"),
            Ok(PyValue::Bytes(b)) => {
                use std::fmt::Write;
                b.iter().fold("bytes:".to_string(), |mut out, x| {
                    let _ = write!(out, "{x:02x}");
                    out
                })
            }
            Ok(PyValue::Seq(items)) => format!("seq{}", items.len()),
            Ok(PyValue::Dict(entries)) => format!("dict{}", entries.len()),
        }
    }

    /// Every expectation is Python 3.13's `ast.literal_eval` on the same
    /// text, except `\N{...}`, a documented gap rejected here.
    #[test]
    fn parses_as_literal_eval_parses() {
        let cases: Vec<(&str, &str)> = vec![
            ("r'\\x41'", "str:\\x41"),
            ("r'\\''", "str:\\'"),
            ("r'\\'", "ERR"),
            ("'\\x4'", "ERR"),
            ("'\\x41'", "str:A"),
            ("'\\u00e9'", "str:\u{e9}"),
            ("'\\U0001F600'", "str:\u{1f600}"),
            ("'\\U00110000'", "ERR"),
            ("'\\101'", "str:A"),
            ("'\\400'", "str:\u{100}"),
            ("'\\0'", "str:\u{0}"),
            ("'\\8'", "str:\\8"),
            ("'\\q'", "str:\\q"),
            ("'\\N{BULLET}'", "ERR"),
            ("b'\\u00e9'", "bytes:5c7530306539"),
            ("b'\u{e9}'", "ERR"),
            ("b'\\x41'", "bytes:41"),
            ("rb'\\x'", "bytes:5c78"),
            ("f'x'", "ERR"),
            ("'a' b'b'", "ERR"),
            ("'a' 'b'", "str:ab"),
            ("'''a'b'''", "str:a'b"),
            ("'a\\\nb'", "str:ab"),
            ("'a\nb'", "ERR"),
            ("\"\"\"x\"\"\"", "str:x"),
            ("1e5", "num:nz"),
            ("1E+5", "num:nz"),
            ("0b101", "num:nz"),
            ("0o17", "num:nz"),
            ("0xFF", "num:nz"),
            ("1_000", "num:nz"),
            ("1__0", "ERR"),
            ("0__0", "ERR"),
            ("1_", "ERR"),
            ("0x_ff", "num:nz"),
            ("_1", "ERR"),
            (".5", "num:nz"),
            ("5.", "num:nz"),
            ("1j", "num:nz"),
            ("-0.0", "num:0"),
            ("00", "num:0"),
            ("07", "ERR"),
            ("0_0", "num:0"),
            ("1e", "ERR"),
            ("0x", "ERR"),
            ("+1", "num:nz"),
            ("- 1", "num:nz"),
            ("--1", "ERR"),
            ("{ # c\n 'a': 1}", "dict1"),
            ("{'a': 1} # c", "dict1"),
            ("{'#': 1}", "dict1"),
            ("\\\n{}", "dict0"),
            ("{}\\\n", "ERR"),
            ("{'a':\\\n 1}", "dict1"),
            ("\u{c}{}", "dict0"),
            ("{}\u{0}", "ERR"),
            ("'\\\n'", "str:"),
            ("(1)", "num:nz"),
            ("(1,)", "seq1"),
            ("()", "seq0"),
            ("[1,]", "seq1"),
            ("{1,}", "seq1"),
            ("{,}", "ERR"),
            ("[,]", "ERR"),
            ("{'a':1,,}", "ERR"),
            ("{'a'}", "seq1"),
            ("{**{}}", "ERR"),
            ("True", "True"),
            ("None", "None"),
            ("none", "ERR"),
            ("-True", "ERR"),
            ("-'a'", "ERR"),
            ("{}\\\n\n", "dict0"),
            ("{}\\\n# c", "dict0"),
            ("{}\\\n ", "dict0"),
            ("{}\\\n\\\n", "ERR"),
            ("[1,\\\n", "ERR"),
            ("{\\\r\n}", "dict0"),
            ("{}\\\r\n\r\n", "dict0"),
            ("{\r\n'a': 1\r\n}", "dict1"),
            ("'a\\\r\nb'", "str:ab"),
            ("\r\n{}", "dict0"),
            ("{}\r", "dict0"),
            ("{\r}", "dict0"),
            ("'a\rb'", "ERR"),
            // Indentation, as Python checks it in eval mode.
            (" # c\n {}", "ERR"),
            ("\n {}", "ERR"),
            ("\n\t{}", "ERR"),
            ("\n  # c\n{}", "dict0"),
            ("  \n{}", "dict0"),
            (" \n {}", "ERR"),
            ("\\\n {}", "ERR"),
            ("# c\n{}", "dict0"),
            (" {}", "dict0"),
            ("\n\n {}", "ERR"),
            ("\r\n {}", "ERR"),
            ("\u{c}\n {}", "ERR"),
            ("\n\u{c}{}", "dict0"),
            ("\n \u{c}{}", "dict0"),
            ("# c\n\t# d\n{}", "dict0"),
            (" {}\n # c", "dict0"),
            ("{}\n  # c", "dict0"),
            ("{}\n  ", "ERR"),
            ("{}\n  \n", "dict0"),
            ("{}\n\t", "ERR"),
            ("{}  ", "dict0"),
            ("{} \n ", "ERR"),
            ("{}\n\n  ", "ERR"),
            ("{}\n \u{c}", "dict0"),
            ("{}\n\u{c}", "dict0"),
            ("{}\n \n ", "ERR"),
            ("{}\n # c\n ", "ERR"),
            ("{}\\\n ", "dict0"),
            ("{}\r\n ", "ERR"),
            ("\u{c} {}", "ERR"),
            ("\u{c}{}", "dict0"),
            ("\\\n{}", "dict0"),
            ("\\\n\t{}", "ERR"),
            ("\\\n\u{c}{}", "dict0"),
            ("{}\n\\\n", "ERR"),
            ("{}\n\\\n\n", "dict0"),
            ("\n \\\n{}", "ERR"),
            ("{}\n \\\n", "ERR"),
            ("{}\n\t# c", "dict0"),
            ("# c\n  \n\t\n{}", "dict0"),
            (" \t {}", "dict0"),
            ("{}\n\u{c} ", "ERR"),
            ("\n\u{c} {}", "ERR"),
        ];
        let mut wrong = Vec::new();
        for (source, want) in cases {
            let got = class(source);
            if got != want {
                wrong.push(format!("{source:?}: want {want:?}, got {got:?}"));
            }
        }
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    }

    /// Hostile nesting is an error, not a stack overflow: Python stops at 200
    /// levels ("too many nested parentheses").
    #[test]
    fn deep_nesting_is_rejected() {
        assert!(parse(&"[".repeat(100_000)).is_err());
        assert!(parse(&format!("{}{}", "{'a': ".repeat(100_000), "1")).is_err());
        let ok = format!("{}1{}", "[".repeat(150), "]".repeat(150));
        assert_eq!(class(&ok), "seq1");
    }

    /// Long and pathological inputs parse in time linear in their length:
    /// each of these is a couple of megabytes or a million repetitions, and
    /// none may take more than a few seconds even in a debug build. Also the
    /// number forms Python accepts at any length: based integers are
    /// unbounded, a decimal integer stops at 4300 digits unless it is zero.
    #[test]
    fn long_inputs_parse_in_linear_time() {
        use std::time::{Duration, Instant};
        let cases: Vec<(&str, String, &str)> = vec![
            (
                "continuations",
                format!("{{{}}}", "\\\n".repeat(200_000)),
                "dict0",
            ),
            ("long string", format!("'{}'", "a".repeat(2_000_000)), "str"),
            (
                "long comment",
                format!("{{ #{}\n}}", "c".repeat(2_000_000)),
                "dict0",
            ),
            (
                "many items",
                format!("[{}]", "1,".repeat(500_000)),
                "seq500000",
            ),
            ("concatenation", "'a' ".repeat(200_000), "str"),
            (
                "whitespace",
                format!("{{{}}}", " ".repeat(2_000_000)),
                "dict0",
            ),
            (
                "line breaks",
                format!("[{}]", "\n".repeat(2_000_000)),
                "seq0",
            ),
            (
                "unterminated",
                format!("'{}", "\\\\".repeat(1_000_000)),
                "ERR",
            ),
            (
                "hex digits",
                format!("0x{}", "f".repeat(1_000_000)),
                "num:nz",
            ),
            ("hex zeros", format!("0x{}", "0".repeat(1_000_000)), "num:0"),
            ("4300 digits", "1".repeat(4300), "num:nz"),
            ("4301 digits", "1".repeat(4301), "ERR"),
            ("zeros", "0".repeat(1_000_000), "num:0"),
            (
                "long float",
                format!("{}.0", "1".repeat(1_000_000)),
                "num:nz",
            ),
            ("long imaginary", format!("{}j", "1".repeat(5000)), "num:nz"),
            (
                "199 mixed levels",
                format!("{}1{}", "{'a': [(".repeat(66), ",)]}".repeat(66)),
                "dict1",
            ),
        ];
        for (name, source, want) in cases {
            let start = Instant::now();
            let got = class(&source);
            let elapsed = start.elapsed();
            assert!(elapsed < Duration::from_secs(5), "{name}: {elapsed:?}");
            let got = if want == "str" {
                got.chars().take(3).collect()
            } else {
                got
            };
            assert_eq!(got, want, "{name}");
        }
    }

    /// Number forms at the edges of Python's rules, each checked against
    /// Python 3.13: the 4300-digit limit counts digits only (signs and
    /// underscores excluded), applies to decimal integers only, and a
    /// leading zero still makes a non-zero integer invalid.
    #[test]
    fn number_edges_match_python() {
        let cases: Vec<(String, &str)> = vec![
            (format!("+{}", "1".repeat(4301)), "ERR"),
            (format!("-{}", "1".repeat(4300)), "num:nz"),
            (format!("{}1", "1_".repeat(4300)), "ERR"),
            (format!("{}1", "1_".repeat(4299)), "num:nz"),
            ("0_0".to_string(), "num:0"),
            (format!("0x{}", "_f".repeat(3000)), "num:nz"),
            ("0x__f".to_string(), "ERR"),
            ("0b_".to_string(), "ERR"),
            ("0o_7".to_string(), "num:nz"),
            ("-0x0".to_string(), "num:0"),
            ("+0b0".to_string(), "num:0"),
            (format!("{}.", "1".repeat(4300)), "num:nz"),
            (format!("{}1", "0".repeat(4301)), "ERR"),
        ];
        for (source, want) in cases {
            assert_eq!(
                class(&source),
                want,
                "{:.24}... ({} chars)",
                source,
                source.len()
            );
        }
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(4096))]
        /// Any text: an answer, never a panic. Drawn from the characters the
        /// grammar cares about, so brackets, quotes, escapes, prefixes,
        /// comments and number forms all collide.
        #[test]
        fn never_panics(source in "[{}\\[\\]()'\"\\\\#:,\n \trbufjxoeEN0-9a-f_.+\\-]{0,300}") {
            let _ = parse(&source);
        }

        /// Any Unicode at all, too.
        #[test]
        fn never_panics_on_any_text(source in "\\PC{0,200}") {
            let _ = parse(&source);
        }
    }
}
