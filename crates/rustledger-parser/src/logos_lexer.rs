//! SIMD-accelerated lexer using Logos.
//!
//! This module provides a fast tokenizer for Beancount syntax using the Logos crate,
//! which generates a DFA-based lexer with SIMD optimizations where available.

use logos::Logos;
use std::fmt;
use std::ops::Range;

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
#[logos(skip r"[ \t]+")] // Skip horizontal whitespace (spaces and tabs)
pub enum Token<'src> {
    // ===== Literals =====
    /// A date in YYYY-MM-DD or YYYY/MM/DD format.
    #[regex(r"\d{4}[-/]\d{2}[-/]\d{2}")]
    Date(&'src str),

    /// A number with optional sign, thousands separators, and decimals.
    /// Examples: 123, -456, 1,234.56, 1234.5678, .50, -.50, 1. (trailing decimal)
    /// Python beancount accepts trailing decimal (e.g., "1." meaning "1.0").
    #[regex(r"-?(\.\d+|(\d{1,3}(,\d{3})*|\d+)(\.\d*)?)")]
    Number(&'src str),

    /// A double-quoted string (handles escape sequences).
    /// The slice includes the quotes.
    #[regex(r#""([^"\\]|\\.)*""#)]
    String(&'src str),

    /// An account name like Assets:Bank:Checking, Aktiva:Bank:Girokonto, or Ciste-jmeni:Stav.
    /// Must start with a capitalized word (account type prefix) and have at least one sub-account.
    /// Account type prefix can contain hyphens (e.g., Ciste-jmeni for Czech "Čisté jmění").
    /// Sub-accounts must start with uppercase letter, digit, or CJK character (matching Python beancount).
    /// Supports Unicode letters (e.g., Expenses:École-républicaine, Assets:沪深300).
    /// `\p{Lo}` matches CJK characters and other scripts without case distinction.
    /// The account type prefix is validated later against options (`name_assets`, etc.).
    #[regex(r"\p{Lu}\p{L}*(-\p{L}+)*(:[\p{Lu}\p{Lo}0-9][\p{L}0-9-]*)+")]
    Account(&'src str),

    /// A currency/commodity code like USD, EUR, AAPL, BTC.
    /// Uppercase letters, can contain digits, apostrophes, dots, underscores, hyphens.
    /// Note: This pattern is lower priority than Account, Keywords, and Flags.
    /// Currency must have at least 2 characters to avoid conflict with single-letter flags.
    /// Also supports `/` prefix for options/futures contracts (e.g., `/ESM24`, `/LOX21_211204_P100.25`).
    /// The `/` prefix requires an uppercase letter first to avoid matching `/1.14` as currency.
    #[regex(r"/[A-Z][A-Z0-9'._-]*|[A-Z][A-Z0-9'._-]+")]
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
    /// The slice includes the trailing colon. Keys can use camelCase or `snake_case`.
    #[regex(r"[a-zA-Z][a-zA-Z0-9_-]*:")]
    MetaKey(&'src str),

    /// Indentation token (inserted by post-processing, not by Logos).
    /// Contains the number of leading spaces.
    /// This is a placeholder - actual indentation detection happens in [`tokenize`].
    Indent(usize),

    /// Deep indentation (4+ spaces) - used for posting-level metadata.
    DeepIndent(usize),

    /// Error token for unrecognized input.
    /// Contains the invalid source text for better error messages.
    Error(&'src str),
}

impl Token<'_> {
    /// Returns true if this is a transaction flag (* or !).
    pub const fn is_txn_flag(&self) -> bool {
        matches!(
            self,
            Self::Star | Self::Pending | Self::Flag(_) | Self::Hash
        )
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
            Self::Error(s) => write!(f, "{s}"),
        }
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
                        // Use DeepIndent for 4+ spaces (posting metadata level)
                        let indent_token = if space_count >= 4 {
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
                // Lexer error - produce an Error token with the invalid source text
                at_line_start = false;
                let invalid_text = &source[span.clone()];
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
    fn test_tokenize_number() {
        let tokens = tokenize("1234.56");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Number("1234.56")));

        let tokens = tokenize("-1,234.56");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Number("-1,234.56")));
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
    fn test_tokenize_currency() {
        let tokens = tokenize("USD");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].0, Token::Currency("USD")));
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
