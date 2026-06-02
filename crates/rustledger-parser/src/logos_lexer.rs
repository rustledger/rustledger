//! SIMD-accelerated lexer using Logos.
//!
//! This module provides a fast tokenizer for Beancount syntax using the Logos crate,
//! which generates a DFA-based lexer with SIMD optimizations where available.

use logos::Logos;
use std::fmt;
use std::ops::Range;

// The leading-BOM strip happens at the `parse()` entry boundary (see
// `crate::bom::strip_leading`). By the time the lexer runs, the source
// is BOM-free at byte 0 by construction. Any U+FEFF byte the lexer
// encounters is therefore mid-file and unrecognized — logos's default
// error path emits a `Token::Error` for it, and the parser's existing
// error classifier (which searches `error_text` for U+FEFF) surfaces
// the dedicated `ParseErrorKind::BomInDirectiveBody` diagnostic.
//
// No BOM-aware lexer callback, no `Token::Bom` variant, and no
// BOM regex in the Token enum — but the `Err(()) => ...` arm in
// `tokenize` DOES contain one mid-file-BOM special case: it preserves
// `at_line_start` and advances `last_newline_end` past leading BOM
// bytes in the error span, so indented content on the same logical
// line still emits an `Indent` token. That logic lives in the
// `apply_err_layout_transparency` helper below and is unit-tested
// directly (including the multi-BOM coalesced-Err case that logos
// doesn't produce from real input today but might in the future).

/// A span in the source code (byte offsets).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Start byte offset (inclusive).
    pub start: usize,
    /// End byte offset (exclusive).
    pub end: usize,
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

impl From<Span> for Range<usize> {
    fn from(span: Span) -> Self {
        span.start..span.end
    }
}

/// Token types produced by the Logos lexer.
#[derive(Logos, Debug, Clone, PartialEq, Eq)]
// Skip horizontal whitespace (spaces and tabs).
#[logos(skip r"[ \t]+")]
pub enum Token<'src> {
    // ===== Literals =====
    /// A date in YYYY-MM-DD, YYYY-M-D, YYYY/MM/DD, or YYYY/M/D format.
    /// Single-digit month and day are accepted (e.g., 2024-1-5).
    #[regex(r"\d{4}[-/]\d{1,2}[-/]\d{1,2}")]
    Date(&'src str),

    /// A number with optional thousands separators and decimals.
    /// Examples: 123, 1,234.56, 1234.5678, 1. (trailing decimal)
    /// Negative numbers are handled as unary minus (`-` token + number)
    /// to allow subtraction expressions like `3-2` to parse correctly.
    /// Python beancount v3 requires an integer part before the decimal point.
    /// Leading decimals like `.50` are rejected per the beancount v3 spec.
    #[regex(r"(\d{1,3}(,\d{3})*|\d+)(\.\d*)?")]
    Number(&'src str),

    /// A double-quoted string (handles escape sequences).
    /// The slice includes the quotes.
    #[regex(r#""([^"\\]|\\.)*""#)]
    String(&'src str),

    /// An account name like Assets:Bank:Checking, Капитал:Retained-Earnings,
    /// or 资产:银行:支票.
    ///
    /// The first component starts with an uppercase letter (`\p{Lu}`), a
    /// letter without case like CJK ideographs (`\p{Lo}`), or a titlecase
    /// letter (`\p{Lt}`). Sub-components may also start with a digit.
    /// Subsequent characters can be any Unicode letter, digit, or hyphen.
    ///
    /// Note: The beancount v3 spec restricts the first character to ASCII
    /// `[A-Z]`, but this is an artifact of the C flex lexer's poor Unicode
    /// support, not a meaningful language design choice (see
    /// beancount/beancount#161, #398, #733).
    ///
    /// The account type prefix is validated later against options (`name_assets`, etc.).
    #[regex(r"[\p{Lu}\p{Lo}\p{Lt}][\p{L}0-9-]*(:([\p{Lu}\p{Lo}\p{Lt}0-9][\p{L}0-9-]*)+)+")]
    Account(&'src str),

    /// A currency/commodity code like USD, EUR, AAPL, BTC, or single-char tickers like T, V, F.
    /// Uppercase letters, can contain digits, apostrophes, dots, underscores, hyphens.
    /// Single-character currencies (e.g., T for AT&T, V for Visa) are valid NYSE/NASDAQ tickers.
    /// Note: Single-char currencies are disambiguated from transaction flags in the parser.
    /// Also supports `/` prefix for options/futures contracts (e.g., `/ESM24`, `/LOX21_211204_P100.25`).
    /// The `/` prefix requires an uppercase letter first to avoid matching `/1.14` as currency.
    /// Priority 3 ensures Currency wins over Flag for single uppercase letters.
    #[regex(r"/[A-Z][A-Z0-9'._-]*|[A-Z][A-Z0-9'._-]*", priority = 3)]
    Currency(&'src str),

    /// A tag like #tag-name.
    #[regex(r"#[a-zA-Z0-9-_/.]+")]
    Tag(&'src str),

    /// A link like ^link-name.
    #[regex(r"\^[a-zA-Z0-9-_/.]+")]
    Link(&'src str),

    // ===== Keywords =====
    // Using #[token] for exact matches (higher priority than regex)
    /// The `txn` keyword for transactions.
    #[token("txn")]
    Txn,
    /// The `balance` directive keyword.
    #[token("balance")]
    Balance,
    /// The `open` directive keyword.
    #[token("open")]
    Open,
    /// The `close` directive keyword.
    #[token("close")]
    Close,
    /// The `commodity` directive keyword.
    #[token("commodity")]
    Commodity,
    /// The `pad` directive keyword.
    #[token("pad")]
    Pad,
    /// The `event` directive keyword.
    #[token("event")]
    Event,
    /// The `query` directive keyword.
    #[token("query")]
    Query,
    /// The `note` directive keyword.
    #[token("note")]
    Note,
    /// The `document` directive keyword.
    #[token("document")]
    Document,
    /// The `price` directive keyword.
    #[token("price")]
    Price,
    /// The `custom` directive keyword.
    #[token("custom")]
    Custom,
    /// The `option` directive keyword.
    #[token("option")]
    Option_,
    /// The `include` directive keyword.
    #[token("include")]
    Include,
    /// The `plugin` directive keyword.
    #[token("plugin")]
    Plugin,
    /// The `pushtag` directive keyword.
    #[token("pushtag")]
    Pushtag,
    /// The `poptag` directive keyword.
    #[token("poptag")]
    Poptag,
    /// The `pushmeta` directive keyword.
    #[token("pushmeta")]
    Pushmeta,
    /// The `popmeta` directive keyword.
    #[token("popmeta")]
    Popmeta,
    /// The `TRUE` boolean literal (also True, true).
    #[token("TRUE")]
    #[token("True")]
    #[token("true")]
    True,
    /// The `FALSE` boolean literal (also False, false).
    #[token("FALSE")]
    #[token("False")]
    #[token("false")]
    False,
    /// The `NULL` literal.
    #[token("NULL")]
    Null,

    // ===== Punctuation =====
    // Order matters: longer tokens first
    /// Double left brace `{{` for cost specifications (legacy total cost).
    #[token("{{")]
    LDoubleBrace,
    /// Double right brace `}}` for cost specifications.
    #[token("}}")]
    RDoubleBrace,
    /// Left brace with hash `{#` for total cost (new syntax).
    #[token("{#")]
    LBraceHash,
    /// Left brace `{` for cost specifications.
    #[token("{")]
    LBrace,
    /// Right brace `}` for cost specifications.
    #[token("}")]
    RBrace,
    /// Left parenthesis `(` for expressions.
    #[token("(")]
    LParen,
    /// Right parenthesis `)` for expressions.
    #[token(")")]
    RParen,
    /// Double at-sign `@@` for total cost.
    #[token("@@")]
    AtAt,
    /// At-sign `@` for unit cost.
    #[token("@")]
    At,
    /// Colon `:` separator.
    #[token(":")]
    Colon,
    /// Comma `,` separator.
    #[token(",")]
    Comma,
    /// Tilde `~` for tolerance.
    #[token("~")]
    Tilde,
    /// Pipe `|` for deprecated payee/narration separator.
    #[token("|")]
    Pipe,
    /// Plus `+` operator.
    #[token("+")]
    Plus,
    /// Minus `-` operator.
    #[token("-")]
    Minus,
    /// Star `*` for cleared transactions and multiplication.
    #[token("*")]
    Star,
    /// Slash `/` for division.
    #[token("/")]
    Slash,

    // ===== Transaction Flags =====
    /// Pending flag `!` for incomplete transactions.
    #[token("!")]
    Pending,

    /// Other transaction flags: P S T C U R M ? &
    /// Note: # and % are handled as comments when followed by space
    #[regex(r"[PSTCURM?&]")]
    Flag(&'src str),

    // ===== Structural =====
    /// Newline (significant in Beancount for directive boundaries).
    #[regex(r"\r?\n")]
    Newline,

    /// A comment starting with semicolon.
    /// The slice includes the semicolon.
    #[regex(r";[^\n\r]*", allow_greedy = true)]
    Comment(&'src str),

    /// Hash token `#` used as separator in cost specs: `{per_unit # total currency}`
    /// Note: In Python beancount, `#` is only a comment at the START of a line.
    /// Mid-line `# text` is NOT a comment - it's either a cost separator or syntax error.
    /// Start-of-line hash comments are handled in post-processing (tokenize function).
    #[token("#")]
    Hash,

    /// A percent comment (ledger-style).
    /// Python beancount accepts % as a comment character for ledger compatibility.
    #[regex(r"%[^\n\r]*", allow_greedy = true)]
    PercentComment(&'src str),

    /// Shebang line at start of file (e.g., #!/usr/bin/env bean-web).
    /// Treated as a comment-like directive to skip.
    #[regex(r"#![^\n\r]*", allow_greedy = true)]
    Shebang(&'src str),

    /// Emacs org-mode directive (e.g., "#+STARTUP: showall").
    /// These are Emacs configuration lines that should be skipped.
    #[regex(r"#\+[^\n\r]*", allow_greedy = true)]
    EmacsDirective(&'src str),

    /// A metadata key (identifier followed by colon).
    /// Examples: filename:, lineno:, custom-key:, nameOnCard:
    /// The slice includes the trailing colon. Keys must start with a lowercase ASCII letter
    /// per the beancount v3 spec. Keys starting with uppercase are rejected.
    #[regex(r"[a-z][a-zA-Z0-9_-]*:")]
    MetaKey(&'src str),

    /// Indentation token (inserted by post-processing, not by Logos).
    /// Contains the number of leading spaces.
    /// This is a placeholder - actual indentation detection happens in [`tokenize`].
    Indent(usize),

    /// Deep indentation (3+ spaces) - used for posting-level metadata.
    DeepIndent(usize),

    /// Error token for unrecognized input.
    /// Contains the invalid source text for better error messages.
    Error(&'src str),
}

impl Token<'_> {
    /// Returns true if this is a transaction flag (* or !).
    /// Single-character currencies (e.g., T, P, C) can also be used as flags.
    pub const fn is_txn_flag(&self) -> bool {
        match self {
            Self::Star | Self::Pending | Self::Flag(_) | Self::Hash => true,
            // Single-char currencies can be used as transaction flags
            Self::Currency(s) => s.len() == 1,
            _ => false,
        }
    }

    /// Returns true if this is a keyword that starts a directive.
    pub const fn is_directive_keyword(&self) -> bool {
        matches!(
            self,
            Self::Txn
                | Self::Balance
                | Self::Open
                | Self::Close
                | Self::Commodity
                | Self::Pad
                | Self::Event
                | Self::Query
                | Self::Note
                | Self::Document
                | Self::Price
                | Self::Custom
                | Self::Option_
                | Self::Include
                | Self::Plugin
                | Self::Pushtag
                | Self::Poptag
                | Self::Pushmeta
                | Self::Popmeta
        )
    }
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Date(s) => write!(f, "{s}"),
            Self::Number(s) => write!(f, "{s}"),
            Self::String(s) => write!(f, "{s}"),
            Self::Account(s) => write!(f, "{s}"),
            Self::Currency(s) => write!(f, "{s}"),
            Self::Tag(s) => write!(f, "{s}"),
            Self::Link(s) => write!(f, "{s}"),
            Self::Txn => write!(f, "txn"),
            Self::Balance => write!(f, "balance"),
            Self::Open => write!(f, "open"),
            Self::Close => write!(f, "close"),
            Self::Commodity => write!(f, "commodity"),
            Self::Pad => write!(f, "pad"),
            Self::Event => write!(f, "event"),
            Self::Query => write!(f, "query"),
            Self::Note => write!(f, "note"),
            Self::Document => write!(f, "document"),
            Self::Price => write!(f, "price"),
            Self::Custom => write!(f, "custom"),
            Self::Option_ => write!(f, "option"),
            Self::Include => write!(f, "include"),
            Self::Plugin => write!(f, "plugin"),
            Self::Pushtag => write!(f, "pushtag"),
            Self::Poptag => write!(f, "poptag"),
            Self::Pushmeta => write!(f, "pushmeta"),
            Self::Popmeta => write!(f, "popmeta"),
            Self::True => write!(f, "TRUE"),
            Self::False => write!(f, "FALSE"),
            Self::Null => write!(f, "NULL"),
            Self::LDoubleBrace => write!(f, "{{{{"),
            Self::RDoubleBrace => write!(f, "}}}}"),
            Self::LBraceHash => write!(f, "{{#"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::AtAt => write!(f, "@@"),
            Self::At => write!(f, "@"),
            Self::Colon => write!(f, ":"),
            Self::Comma => write!(f, ","),
            Self::Tilde => write!(f, "~"),
            Self::Pipe => write!(f, "|"),
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
            Self::Star => write!(f, "*"),
            Self::Slash => write!(f, "/"),
            Self::Pending => write!(f, "!"),
            Self::Flag(s) => write!(f, "{s}"),
            Self::Newline => write!(f, "\\n"),
            Self::Comment(s) => write!(f, "{s}"),
            Self::Hash => write!(f, "#"),
            Self::PercentComment(s) => write!(f, "{s}"),
            Self::Shebang(s) => write!(f, "{s}"),
            Self::EmacsDirective(s) => write!(f, "{s}"),
            Self::MetaKey(s) => write!(f, "{s}"),
            Self::Indent(n) => write!(f, "<indent:{n}>"),
            Self::DeepIndent(n) => write!(f, "<deep-indent:{n}>"),
            Self::Error(s) => {
                // Strip any embedded U+FEFF bytes (a mid-file BOM
                // captured into a lexer error span) so diagnostics
                // rendering this token stay human-readable. LSP problem
                // panels, CLI stderr, and GitHub-rendered bug reports
                // all silently drop or strip literal BOM bytes — the
                // `<BOM>` placeholder makes the failure mode visible.
                //
                // Streamed (rather than `s.replace(...)`) so this
                // Display impl is zero-allocation. LSP problem panels
                // re-render diagnostics on every keystroke during
                // interactive editing; a `String` allocation per
                // render showed up in flame graphs for files with
                // many BOM-containing Token::Error tokens. The fast
                // path (no BOM in `s`) is one `f.write_str(s)` call.
                if s.contains(crate::bom::BOM_CHAR) {
                    let mut chunks = s.split(crate::bom::BOM_CHAR);
                    // Interleave chunks with "<BOM>" between them.
                    // `split` yields N+1 chunks for N matches, so the
                    // first chunk is emitted as-is and each subsequent
                    // chunk gets a `<BOM>` prefix. Final output is
                    // chunk0 + "<BOM>" + chunk1 + "<BOM>" + chunkN —
                    // matching the (allocating) `s.replace(...)`
                    // behavior exactly.
                    if let Some(first) = chunks.next() {
                        f.write_str(first)?;
                    }
                    for chunk in chunks {
                        f.write_str("<BOM>")?;
                        f.write_str(chunk)?;
                    }
                    Ok(())
                } else {
                    f.write_str(s)
                }
            }
        }
    }
}

/// Apply mid-file BOM layout-transparency rules to lexer-state from
/// inside the `Err` arm of `tokenize`.
///
/// A mid-file BOM (U+FEFF) is layout-transparent: it produces an
/// error diagnostic via the parser's classifier, but must NOT clobber
/// `at_line_start` or move `last_newline_end` past the BOM, otherwise
/// the next token on the same logical line (e.g. an indented posting
/// from a concatenated Windows file) loses its indent classification
/// and the parser mistypes it. Leading-BOM is handled at the
/// `crate::parse` boundary and never reaches this code path; only
/// mid-file BOMs that survived the strip do.
///
/// We use `trim_start_matches` (rather than `starts_with` + a single
/// `BOM_LEN` advance) so a multi-BOM run — e.g., a hypothetical
/// coalesced `\u{FEFF}\u{FEFF}` Err span from a triple-concatenated
/// Windows file — is ENTIRELY layout-transparent. Advancing
/// `last_newline_end` past only the first BOM but then clobbering
/// `at_line_start` because of the second BOM would cascade into
/// misclassifying the next real token. The contract is: every BOM
/// byte is layout-transparent; `at_line_start` is preserved iff the
/// entire error span is BOM bytes; `last_newline_end` advances past
/// the full run of leading BOMs.
///
/// Extracted as a private helper so the multi-BOM defensive code path
/// can be unit-tested independently of logos's emission strategy.
/// Today logos emits one Err per unrecognized char, so the coalesced
/// path is unreachable from real input; the unit tests at the bottom
/// of this file feed the helper synthetic `invalid_text` values that
/// exercise the coalesced case directly.
fn apply_err_layout_transparency(
    invalid_text: &str,
    span_start: usize,
    at_line_start: &mut bool,
    last_newline_end: &mut usize,
) {
    // Round-17 fix: the contract documented above says "every BOM
    // byte is layout-transparent" — i.e., a span like
    // `\u{FEFF}@@\u{FEFF}` should classify its non-BOM bytes for the
    // at_line_start decision, not its BOM bytes. The previous impl
    // only inspected the LEADING run of BOMs and clobbered
    // `at_line_start` for any non-empty tail. That sub-case worked
    // because a coalesced span starting with BOM + non-BOM tail
    // really does break the indent contract. But a coalesced span
    // like `@@\u{FEFF}` (non-BOM head followed by BOM tail) would
    // also clobber — the BOM in the tail is layout-transparent per
    // contract, but the head is real content so the clobber is
    // already correct. The genuinely-wrong case (currently
    // unreachable but reachable under a future logos upgrade that
    // coalesces error sequences) is when the ENTIRE span is BOMs,
    // possibly interleaved with whitespace: those should be fully
    // layout-transparent. We now extract the LEADING run of BOM
    // bytes for `last_newline_end` advancement, and consult the
    // FULL invalid_text minus all BOM bytes for the at_line_start
    // decision.
    let after_leading_bom = invalid_text.trim_start_matches(crate::bom::BOM_CHAR);
    let leading_bom_bytes = invalid_text.len() - after_leading_bom.len();
    if leading_bom_bytes > 0 && *at_line_start && span_start == *last_newline_end {
        *last_newline_end = span_start + leading_bom_bytes;
    }

    // Any non-BOM byte ANYWHERE in the span is "real content" for
    // indent purposes. An all-BOM span (possibly interleaving BOMs
    // at any position) leaves `at_line_start` untouched. The
    // previous `is_empty()` check on JUST the after-leading-BOM
    // tail had a latent gap for a coalesced `@<BOM>` span: the
    // leading run is empty, so the `else` arm clobbered — which
    // happens to be correct for that case, but the path was
    // accidental rather than principled. Walking the whole span
    // makes the rule explicit.
    let has_non_bom_byte = invalid_text.chars().any(|c| c != crate::bom::BOM_CHAR);
    if has_non_bom_byte {
        *at_line_start = false;
    }
}

/// Tokenize source code into a vector of (Token, Span) pairs.
///
/// This function:
/// 1. Runs the Logos lexer for fast tokenization
/// 2. Post-processes to detect indentation at line starts
/// 3. Handles lexer errors by producing Error tokens
pub fn tokenize(source: &str) -> Vec<(Token<'_>, Span)> {
    let mut tokens = Vec::new();
    let mut lexer = Token::lexer(source);
    let mut at_line_start = true;
    let mut last_newline_end = 0usize;

    while let Some(result) = lexer.next() {
        let span = lexer.span();

        match result {
            Ok(Token::Newline) => {
                tokens.push((Token::Newline, span.clone().into()));
                at_line_start = true;
                last_newline_end = span.end;
            }
            Ok(Token::Hash) if at_line_start && span.start == last_newline_end => {
                // Hash at very start of line (no indentation) is a comment
                // Find end of line and create a comment token for the whole line
                let comment_start = span.start;
                let line_end = source[span.end..]
                    .find('\n')
                    .map_or(source.len(), |i| span.end + i);
                let comment_text = &source[comment_start..line_end];
                tokens.push((
                    Token::Comment(comment_text),
                    Span {
                        start: comment_start,
                        end: line_end,
                    },
                ));
                // Skip lexer tokens until we reach the newline
                while let Some(peek_result) = lexer.next() {
                    let peek_span = lexer.span();
                    let peek_end = peek_span.end;
                    if peek_result == Ok(Token::Newline) {
                        tokens.push((Token::Newline, peek_span.into()));
                        at_line_start = true;
                        last_newline_end = peek_end;
                        break;
                    }
                    // Skip other tokens on the comment line
                }
            }
            Ok(token) => {
                // Check for indentation at line start
                if at_line_start && span.start > last_newline_end {
                    // Count leading whitespace between last newline and this token
                    // Tabs count as indentation (treat 1 tab as 4 spaces for counting purposes)
                    let leading = &source[last_newline_end..span.start];
                    let mut space_count = 0;
                    let mut char_count = 0;
                    for c in leading.chars() {
                        match c {
                            ' ' => {
                                space_count += 1;
                                char_count += 1;
                            }
                            '\t' => {
                                space_count += 4; // Treat tab as 4 spaces
                                char_count += 1;
                            }
                            _ => break,
                        }
                    }
                    // Python beancount accepts 1+ space for metadata indentation
                    if space_count >= 1 {
                        let indent_start = last_newline_end;
                        let indent_end = last_newline_end + char_count;
                        // Use DeepIndent for 3+ spaces (posting metadata level).
                        // Python beancount allows flexible indentation where posting
                        // metadata just needs to be more indented than the posting.
                        // Common patterns: 2-space posting / 4-space meta, or
                        // 1-space posting / 3-space meta (as in beancount_reds_plugins).
                        let indent_token = if space_count >= 3 {
                            Token::DeepIndent(space_count)
                        } else {
                            Token::Indent(space_count)
                        };
                        tokens.push((
                            indent_token,
                            Span {
                                start: indent_start,
                                end: indent_end,
                            },
                        ));
                    }
                }
                at_line_start = false;
                tokens.push((token, span.into()));
            }
            Err(()) => {
                // Lexer error - produce an Error token with the invalid source text.
                let invalid_text = &source[span.clone()];
                apply_err_layout_transparency(
                    invalid_text,
                    span.start,
                    &mut at_line_start,
                    &mut last_newline_end,
                );
                tokens.push((Token::Error(invalid_text), span.into()));
            }
        }
    }

    tokens
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize_date() {
        let tokens = tokenize("2024-01-15");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Date("2024-01-15")));
    }

    #[test]
    fn test_tokenize_date_single_digit_month() {
        // Single-digit month should be tokenized as Date
        let tokens = tokenize("2024-1-15");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Date("2024-1-15")));
    }

    #[test]
    fn test_tokenize_date_single_digit_day() {
        // Single-digit day should be tokenized as Date
        let tokens = tokenize("2024-01-5");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Date("2024-01-5")));
    }

    #[test]
    fn test_tokenize_date_single_digit_month_and_day() {
        // Single-digit month and day should be tokenized as Date
        let tokens = tokenize("2024-1-1");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Date("2024-1-1")));
    }

    #[test]
    fn test_tokenize_date_slash_separator_single_digit() {
        // Slash separator with single-digit parts
        let tokens = tokenize("2024/1/5");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Date("2024/1/5")));
    }

    #[test]
    fn test_tokenize_number() {
        let tokens = tokenize("1234.56");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Number("1234.56")));

        // Negative numbers are now Minus + Number (enables subtraction expressions)
        let tokens = tokenize("-1,234.56");
        assert_eq!(tokens.len(), 2);
        assert!(matches!(tokens[0].0, Token::Minus));
        assert!(matches!(tokens[1].0, Token::Number("1,234.56")));
    }

    #[test]
    fn test_tokenize_account() {
        let tokens = tokenize("Assets:Bank:Checking");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(
            tokens[0].0,
            Token::Account("Assets:Bank:Checking")
        ));
    }

    #[test]
    fn test_tokenize_account_unicode() {
        // Unicode uppercase letters and CJK characters are valid at the
        // start of account components. Emoji and symbols are not.

        // Non-letter (emoji) after valid ASCII start — still invalid
        let tokens = tokenize("Assets:CORP✨");
        assert!(
            !matches!(tokens[0].0, Token::Account("Assets:CORP✨")),
            "Unicode emoji in account name should not tokenize as a valid Account"
        );
        assert!(
            tokens.iter().any(|(t, _)| matches!(t, Token::Error(_))),
            "Unicode emoji should produce at least one Error token"
        );

        // CJK sub-component start — now valid (CJK ideographs are \p{Lo})
        let tokens = tokenize("Assets:沪深300");
        assert!(
            matches!(tokens[0].0, Token::Account("Assets:沪深300")),
            "CJK characters at the start of a sub-component should tokenize as Account"
        );

        // Full CJK sub-component — valid
        let tokens = tokenize("Assets:日本銀行");
        assert!(
            matches!(tokens[0].0, Token::Account("Assets:日本銀行")),
            "CJK sub-component should tokenize as Account"
        );

        // Cyrillic account type — valid (Cyrillic uppercase is \p{Lu})
        let tokens = tokenize("Капитал:Retained");
        assert!(
            matches!(tokens[0].0, Token::Account("Капитал:Retained")),
            "Cyrillic-starting account should tokenize as Account"
        );

        // Fully CJK account — valid
        let tokens = tokenize("资产:银行:支票");
        assert!(
            matches!(tokens[0].0, Token::Account("资产:银行:支票")),
            "Fully CJK account should tokenize as Account"
        );
    }

    /// Regression for issue #736/#739: Unicode letters AFTER an ASCII start
    /// in account sub-components are valid per the beancount v3 spec.
    #[test]
    fn test_tokenize_account_unicode_letters_after_ascii_start() {
        // French: É after ASCII start
        let tokens = tokenize("Assets:Banque-Épargne");
        assert!(
            matches!(tokens[0].0, Token::Account("Assets:Banque-Épargne")),
            "accented Latin letter after ASCII start should tokenize as Account, got: {tokens:?}"
        );

        // German: ü after ASCII start
        let tokens = tokenize("Assets:Müller");
        assert!(
            matches!(tokens[0].0, Token::Account("Assets:Müller")),
            "German umlaut after ASCII start should tokenize as Account, got: {tokens:?}"
        );

        // Mixed CJK after ASCII start — letters are allowed
        let tokens = tokenize("Assets:CorpJP日本");
        assert!(
            matches!(tokens[0].0, Token::Account("Assets:CorpJP日本")),
            "CJK letters after ASCII start should tokenize as Account, got: {tokens:?}"
        );
    }

    #[test]
    fn test_tokenize_currency() {
        let tokens = tokenize("USD");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Currency("USD")));
    }

    #[test]
    fn test_tokenize_single_char_currency() {
        // Single-char NYSE/NASDAQ tickers: T (AT&T), V (Visa), F (Ford), X (US Steel)
        let tokens = tokenize("T");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Currency("T")));

        let tokens = tokenize("V");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Currency("V")));

        let tokens = tokenize("F");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Currency("F")));
    }

    #[test]
    fn test_single_char_currency_is_txn_flag() {
        // Single-char currencies should be recognized as potential transaction flags
        let token = Token::Currency("T");
        assert!(token.is_txn_flag());

        // Multi-char currencies should NOT be transaction flags
        let token = Token::Currency("USD");
        assert!(!token.is_txn_flag());
    }

    #[test]
    fn test_tokenize_string() {
        let tokens = tokenize(r#""Hello, World!""#);
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::String(r#""Hello, World!""#)));
    }

    #[test]
    fn test_tokenize_keywords() {
        let tokens = tokenize("txn balance open close");
        assert_eq!(tokens.len(), 4);
        assert!(matches!(tokens[0].0, Token::Txn));
        assert!(matches!(tokens[1].0, Token::Balance));
        assert!(matches!(tokens[2].0, Token::Open));
        assert!(matches!(tokens[3].0, Token::Close));
    }

    #[test]
    fn test_tokenize_tag_and_link() {
        let tokens = tokenize("#my-tag ^my-link");
        assert_eq!(tokens.len(), 2);
        assert!(matches!(tokens[0].0, Token::Tag("#my-tag")));
        assert!(matches!(tokens[1].0, Token::Link("^my-link")));
    }

    #[test]
    fn test_tokenize_comment() {
        let tokens = tokenize("; This is a comment");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Comment("; This is a comment")));
    }

    #[test]
    fn test_tokenize_indentation() {
        let tokens = tokenize("txn\n  Assets:Bank 100 USD");
        // Should have: Txn, Newline, Indent, Account, Number, Currency
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Indent(_))));
    }

    /// `Token::Error`'s Display impl strips embedded BOM bytes — if a
    /// mid-file U+FEFF gets captured into a lexer error span, the
    /// diagnostic still renders human-readably. The leading-BOM case
    /// is handled at the `crate::parse` boundary (see `crate::bom`),
    /// so this defensive measure only matters for mid-file BOMs that
    /// fall into the lexer's default error path.
    #[test]
    fn test_display_token_error_strips_embedded_bom() {
        let payload = "foo\u{FEFF}bar";
        let s = format!("{}", Token::Error(payload));
        assert_eq!(s, "foo<BOM>bar");
        assert!(!s.contains(crate::bom::BOM_CHAR));
    }

    /// A mid-file BOM (any U+FEFF not at strict byte 0) reaches the
    /// lexer with no special handling — there is no BOM regex on the
    /// Token enum anymore. Logos's default error path emits `Token::Error`
    /// for the unrecognized byte; the parser's error classifier (which
    /// searches `error_text` for U+FEFF) surfaces the dedicated
    /// diagnostic on the parser side. This test pins the lexer side:
    /// some `Token::Error` appears in the stream containing the BOM byte.
    #[test]
    fn test_tokenize_mid_file_bom_falls_into_error_path() {
        // Note: this test calls `tokenize` directly with the BOM byte
        // present in the source — it does NOT go through `parse`, which
        // would have stripped a strict-byte-0 BOM. So we put the BOM
        // mid-source to bypass the strip.
        let source = "2024-01-01 open Assets:Bank USD\n\u{FEFF}";
        let tokens = tokenize(source);
        let has_bom_in_error = tokens.iter().any(|(t, _)| {
            if let Token::Error(s) = t {
                s.contains(crate::bom::BOM_CHAR)
            } else {
                false
            }
        });
        assert!(
            has_bom_in_error,
            "mid-file BOM should fall into `Token::Error`, got: {tokens:?}"
        );
    }

    /// Layout-transparency contract for mid-file BOM: a BOM at line
    /// start followed by indented content (the
    /// `cat windows-a.bean windows-b.bean` concatenation case) must
    /// NOT swallow the indent on the next token. The Err arm in
    /// `tokenize` recognizes `Token::Error("\u{FEFF}")` and preserves
    /// `at_line_start` + advances `last_newline_end` so the next
    /// real token still gets its `Token::Indent` emission.
    ///
    /// Without this special case, the Err arm sets `at_line_start =
    /// false` like for any other lex error, the indented posting
    /// fails to produce an Indent token, and the parser misclassifies
    /// the posting as a top-level directive — producing cascading
    /// errors instead of the targeted BOM diagnostic.
    #[test]
    fn test_mid_file_bom_at_line_start_preserves_following_indent() {
        // First a directive, then newline, then mid-file BOM, then
        // indented posting-like content. `tokenize` is called directly
        // (bypassing parse's strip-at-entry) so the BOM is mid-file.
        let source = "2024-01-01 open Assets:Bank USD\n\u{FEFF}  meta-key: \"v\"\n";
        let tokens = tokenize(source);
        // The Token::Error for the BOM must be present.
        let has_bom_error = tokens.iter().any(|(t, _)| {
            if let Token::Error(s) = t {
                *s == crate::bom::BOM
            } else {
                false
            }
        });
        assert!(
            has_bom_error,
            "expected Token::Error(\"\\u{{FEFF}}\") in stream, got: {tokens:?}"
        );
        // Critically: the indent for the 2-space metadata line must
        // survive — it should be a Token::Indent(2), not absorbed.
        let has_indent_2 = tokens.iter().any(|(t, _)| matches!(t, Token::Indent(2)));
        assert!(
            has_indent_2,
            "mid-file BOM at line start must not swallow the following Indent; got: {tokens:?}"
        );
        // And the metadata key tokenizes normally on the same line.
        assert!(
            tokens
                .iter()
                .any(|(t, _)| matches!(t, Token::MetaKey("meta-key:"))),
            "expected MetaKey after BOM-prefixed indent, got: {tokens:?}"
        );
    }

    /// Consecutive BOMs at line start (logos emits each as its own
    /// Err) ALL preserve layout-transparency. The Err arm uses
    /// `trim_start_matches(BOM_CHAR)` to find non-BOM content, so a
    /// triple-concatenated Windows file producing `\n\u{FEFF}\u{FEFF}`
    /// at line start, followed by indented content, still emits the
    /// `Indent` for the metadata line. Without the `trim_start_matches`
    /// approach (using a single-BOM length check instead), the second
    /// BOM would either not advance `last_newline_end` correctly or
    /// would clobber `at_line_start`, breaking the indent walk on the
    /// next real token.
    #[test]
    fn test_consecutive_mid_file_boms_preserve_layout() {
        let source = "2024-01-01 open Assets:Bank USD\n\u{FEFF}\u{FEFF}  meta-key: \"v\"\n";
        let tokens = tokenize(source);
        // Both BOMs should appear as Token::Error.
        let bom_error_count = tokens
            .iter()
            .filter(|(t, _)| matches!(t, Token::Error(s) if *s == crate::bom::BOM))
            .count();
        assert_eq!(
            bom_error_count, 2,
            "expected 2 Token::Error(BOM) tokens, got: {tokens:?}"
        );
        // And the indent on the line containing the BOMs must survive.
        let has_indent_2 = tokens.iter().any(|(t, _)| matches!(t, Token::Indent(2)));
        assert!(
            has_indent_2,
            "consecutive mid-file BOMs at line start must not swallow following indent; \
             got: {tokens:?}"
        );
        assert!(
            tokens
                .iter()
                .any(|(t, _)| matches!(t, Token::MetaKey("meta-key:"))),
            "expected MetaKey after consecutive-BOM-prefixed indent, got: {tokens:?}"
        );
    }

    // ===== Direct tests of `apply_err_layout_transparency` =====
    //
    // These tests exercise the helper independently of logos's
    // emission strategy. Today logos emits one Err per unrecognized
    // char, so the multi-BOM-in-one-Err code path (the
    // `trim_start_matches` loop's motivating case) is unreachable
    // from real input. The tests below feed the helper synthetic
    // invalid_text values so the defensive code is actually
    // validated rather than documentation-only.

    /// Coalesced double-BOM at line start: must advance
    /// `last_newline_end` past BOTH bytes and keep `at_line_start`.
    /// Pins the contract `trim_start_matches` exists to provide.
    #[test]
    fn err_layout_transparency_coalesced_double_bom_at_line_start() {
        let invalid_text = "\u{FEFF}\u{FEFF}";
        let span_start = 10;
        let mut at_line_start = true;
        let mut last_newline_end = 10;
        apply_err_layout_transparency(
            invalid_text,
            span_start,
            &mut at_line_start,
            &mut last_newline_end,
        );
        assert!(
            at_line_start,
            "all-BOM error span must preserve at_line_start"
        );
        assert_eq!(
            last_newline_end,
            10 + 2 * crate::bom::BOM_LEN,
            "last_newline_end must advance past BOTH BOMs, not just the first"
        );
    }

    /// Coalesced BOM + trailing content: `at_line_start` clobbers (real
    /// content follows the BOM run); `last_newline_end` still
    /// advances past the BOM portion only.
    #[test]
    fn err_layout_transparency_coalesced_bom_with_trailing_content() {
        let invalid_text = "\u{FEFF}\u{FEFF}xyz";
        let span_start = 10;
        let mut at_line_start = true;
        let mut last_newline_end = 10;
        apply_err_layout_transparency(
            invalid_text,
            span_start,
            &mut at_line_start,
            &mut last_newline_end,
        );
        assert!(
            !at_line_start,
            "trailing non-BOM content must clobber at_line_start"
        );
        assert_eq!(
            last_newline_end,
            10 + 2 * crate::bom::BOM_LEN,
            "last_newline_end advances past leading BOMs, NOT past trailing content"
        );
    }

    /// Non-BOM error: standard clobber.
    #[test]
    fn err_layout_transparency_non_bom_clobbers() {
        let invalid_text = "garbage";
        let mut at_line_start = true;
        let mut last_newline_end = 10;
        apply_err_layout_transparency(invalid_text, 10, &mut at_line_start, &mut last_newline_end);
        assert!(!at_line_start);
        assert_eq!(last_newline_end, 10, "non-BOM error must not advance");
    }

    /// All-BOM error span but NOT at line start (e.g., BOM appears
    /// mid-line after some content): `at_line_start` was already
    /// false, the inner advance guard fails, and nothing changes.
    #[test]
    fn err_layout_transparency_all_bom_not_at_line_start_is_noop() {
        let invalid_text = "\u{FEFF}\u{FEFF}";
        let span_start = 20;
        let mut at_line_start = false; // mid-line
        let mut last_newline_end = 10;
        apply_err_layout_transparency(
            invalid_text,
            span_start,
            &mut at_line_start,
            &mut last_newline_end,
        );
        assert!(!at_line_start);
        assert_eq!(last_newline_end, 10, "guard prevents stale advance");
    }

    /// Complementary to the previous test: the inner `at_line_start &&
    /// span_start == last_newline_end` guard has two clauses. The
    /// `*_not_at_line_start_*` test above exercises the first
    /// (`at_line_start = false`); THIS test pins the second
    /// (span doesn't begin at `last_newline_end`).
    ///
    /// Without exercising both clauses independently, a refactor that
    /// flipped `&&` to `||` would not be caught — either clause alone
    /// suffices to suppress the advance.
    #[test]
    fn err_layout_transparency_all_bom_span_mismatch_is_noop() {
        let invalid_text = "\u{FEFF}\u{FEFF}";
        // at_line_start IS true (the first clause's condition holds)…
        let mut at_line_start = true;
        // …but span_start (20) != last_newline_end (10), so the
        // second clause's condition fails. Combined: the advance
        // must NOT fire.
        let span_start = 20;
        let mut last_newline_end = 10;
        apply_err_layout_transparency(
            invalid_text,
            span_start,
            &mut at_line_start,
            &mut last_newline_end,
        );
        assert!(
            at_line_start,
            "all-BOM error span must preserve at_line_start regardless of span-vs-last-newline match"
        );
        assert_eq!(
            last_newline_end, 10,
            "span_start != last_newline_end must prevent stale advance"
        );
    }

    /// Round-17/18: the contract "every BOM byte is layout-
    /// transparent" covers BOMs at ANY position in a coalesced error
    /// span, not just the leading run. Pre-round-17 the
    /// implementation only inspected the leading BOM run for the
    /// `at_line_start` decision — a coalesced span like
    /// `@@<BOM>` (non-BOM head, BOM tail) was clobbered by the
    /// leading-only logic even though the trailing BOM should have
    /// been transparent (and the leading `@@` would correctly
    /// clobber on its own). The fixed implementation walks the
    /// whole span: ANY non-BOM byte clobbers; only an all-BOM span
    /// (in any arrangement) preserves `at_line_start`.
    ///
    /// These tests cover the interleaved shapes the round-17
    /// contract claims to handle: BOM-only-tail, BOM-in-middle,
    /// and the recently-flagged "BOM-only in any arrangement"
    /// preservation guarantee.
    #[test]
    fn err_layout_transparency_bom_only_in_any_arrangement_preserves() {
        // All-BOM coalesced span — preserves at_line_start AND
        // advances last_newline_end past the leading run.
        let mut at_line_start = true;
        let mut last_newline_end = 10;
        apply_err_layout_transparency(
            "\u{FEFF}\u{FEFF}",
            10, // span_start == last_newline_end → advance fires
            &mut at_line_start,
            &mut last_newline_end,
        );
        assert!(at_line_start, "all-BOM span preserves at_line_start");
        assert_eq!(
            last_newline_end, 16,
            "leading BOM run advances last_newline_end past both BOM bytes \
             (each BOM is 3 UTF-8 bytes)"
        );
    }

    /// Non-BOM head clobbers `at_line_start`. Pre-round-17 also did
    /// this (correctly); pinning prevents a regression that re-
    /// introduces a BOM-only-trim that misses non-BOM head bytes.
    #[test]
    fn err_layout_transparency_non_bom_head_clobbers() {
        let mut at_line_start = true;
        let mut last_newline_end = 0;
        apply_err_layout_transparency("@@\u{FEFF}", 10, &mut at_line_start, &mut last_newline_end);
        assert!(
            !at_line_start,
            "non-BOM head ('@@') clobbers at_line_start regardless of trailing BOM"
        );
    }

    /// BOM head + non-BOM tail clobbers (because of the tail).
    /// Pre-round-17 the leading-only logic was correct here too;
    /// pinning ensures no regression that flips to leading-only.
    #[test]
    fn err_layout_transparency_bom_head_non_bom_tail_clobbers() {
        let mut at_line_start = true;
        let mut last_newline_end = 10;
        apply_err_layout_transparency("\u{FEFF}@@", 10, &mut at_line_start, &mut last_newline_end);
        assert!(
            !at_line_start,
            "non-BOM tail ('@@') clobbers at_line_start even though span starts with BOM"
        );
        assert_eq!(
            last_newline_end, 13,
            "leading BOM run STILL advances last_newline_end past the BOM"
        );
    }

    /// Non-BOM in the middle of a BOM-flanked span clobbers. THIS
    /// is the case the round-17 docstring specifically claimed to
    /// cover; pre-round-17 the same outcome held (leading BOMs
    /// trimmed, non-empty tail clobbered) but only by accident.
    /// The fixed `has_non_bom_byte = chars().any(|c| c != BOM)`
    /// walks the whole span and makes the case explicit.
    #[test]
    fn err_layout_transparency_bom_flanking_non_bom_clobbers() {
        let mut at_line_start = true;
        let mut last_newline_end = 10;
        apply_err_layout_transparency(
            "\u{FEFF}@@\u{FEFF}",
            10,
            &mut at_line_start,
            &mut last_newline_end,
        );
        assert!(
            !at_line_start,
            "non-BOM middle ('@@') clobbers at_line_start"
        );
        assert_eq!(
            last_newline_end, 13,
            "leading BOM run advances last_newline_end past the leading BOM only"
        );
    }

    #[test]
    fn test_tokenize_transaction_line() {
        let source = "2024-01-15 * \"Grocery Store\" #food\n  Expenses:Food 50.00 USD";
        let tokens = tokenize(source);

        // Check key tokens are present
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Date(_))));
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Star)));
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::String(_))));
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Tag(_))));
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Newline)));
        assert!(
            tokens
                .iter()
                .any(|(t, _)| matches!(t, Token::Indent(_) | Token::DeepIndent(_)))
        );
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Account(_))));
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Number(_))));
        assert!(tokens.iter().any(|(t, _)| matches!(t, Token::Currency(_))));
    }

    #[test]
    fn test_tokenize_metadata_key() {
        let tokens = tokenize("filename:");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::MetaKey("filename:")));
    }

    #[test]
    fn test_tokenize_punctuation() {
        let tokens = tokenize("{ } @ @@ , ~");
        let token_types: Vec<_> = tokens.iter().map(|(t, _)| t.clone()).collect();
        assert!(token_types.contains(&Token::LBrace));
        assert!(token_types.contains(&Token::RBrace));
        assert!(token_types.contains(&Token::At));
        assert!(token_types.contains(&Token::AtAt));
        assert!(token_types.contains(&Token::Comma));
        assert!(token_types.contains(&Token::Tilde));
    }
}
