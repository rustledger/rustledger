//! Lexer for tokenizing beancount source.

use chumsky::prelude::*;

/// Token types produced by the lexer.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    /// A date: YYYY-MM-DD
    Date(String),
    /// A number (decimal)
    Number(String),
    /// A quoted string
    String(String),
    /// An account name: Assets:Bank:Checking
    Account(String),
    /// A currency code: USD, EUR, AAPL
    Currency(String),
    /// A tag: #tag-name
    Tag(String),
    /// A link: ^link-name
    Link(String),

    // Keywords
    /// txn keyword
    Txn,
    /// balance keyword
    Balance,
    /// open keyword
    Open,
    /// close keyword
    Close,
    /// commodity keyword
    Commodity,
    /// pad keyword
    Pad,
    /// event keyword
    Event,
    /// query keyword
    Query,
    /// note keyword
    Note,
    /// document keyword
    Document,
    /// price keyword
    Price,
    /// custom keyword
    Custom,
    /// option keyword
    Option,
    /// include keyword
    Include,
    /// plugin keyword
    Plugin,
    /// pushtag keyword
    Pushtag,
    /// poptag keyword
    Poptag,
    /// pushmeta keyword
    Pushmeta,
    /// popmeta keyword
    Popmeta,
    /// TRUE keyword
    True,
    /// FALSE keyword
    False,

    // Punctuation
    /// Transaction flag: * or !
    Flag(char),
    /// Opening brace {
    LBrace,
    /// Closing brace }
    RBrace,
    /// Double opening brace {{
    LDoubleBrace,
    /// Double closing brace }}
    RDoubleBrace,
    /// At sign @
    At,
    /// Double at sign @@
    AtAt,
    /// Colon :
    Colon,
    /// Comma ,
    Comma,
    /// Tilde ~
    Tilde,

    // Structural
    /// Newline (significant in beancount)
    Newline,
    /// Indentation (two or more spaces at line start)
    Indent,
    /// Comment text (without the semicolon)
    Comment(String),

    // Metadata
    /// A metadata key (lowercase identifier followed by :)
    MetaKey(String),
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Date(s) => write!(f, "{s}"),
            Self::Number(s) => write!(f, "{s}"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Account(s) => write!(f, "{s}"),
            Self::Currency(s) => write!(f, "{s}"),
            Self::Tag(s) => write!(f, "#{s}"),
            Self::Link(s) => write!(f, "^{s}"),
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
            Self::Option => write!(f, "option"),
            Self::Include => write!(f, "include"),
            Self::Plugin => write!(f, "plugin"),
            Self::Pushtag => write!(f, "pushtag"),
            Self::Poptag => write!(f, "poptag"),
            Self::Pushmeta => write!(f, "pushmeta"),
            Self::Popmeta => write!(f, "popmeta"),
            Self::True => write!(f, "TRUE"),
            Self::False => write!(f, "FALSE"),
            Self::Flag(c) => write!(f, "{c}"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::LDoubleBrace => write!(f, "{{{{"),
            Self::RDoubleBrace => write!(f, "}}}}"),
            Self::At => write!(f, "@"),
            Self::AtAt => write!(f, "@@"),
            Self::Colon => write!(f, ":"),
            Self::Comma => write!(f, ","),
            Self::Tilde => write!(f, "~"),
            Self::Newline => write!(f, "\\n"),
            Self::Indent => write!(f, "<indent>"),
            Self::Comment(s) => write!(f, ";{s}"),
            Self::MetaKey(s) => write!(f, "{s}:"),
        }
    }
}

/// Create the lexer.
pub fn lexer<'a>() -> impl Parser<'a, &'a str, Vec<(Token, SimpleSpan)>, extra::Err<Rich<'a, char>>> {
    let date = text::int(10)
        .then(just('-').or(just('/')))
        .then(text::int(10))
        .then(just('-').or(just('/')))
        .then(text::int(10))
        .to_slice()
        .map(|s: &str| Token::Date(s.to_string()));

    let number = just('-')
        .or_not()
        .then(
            text::digits(10)
                .then(just(',').then(text::digits(10)).repeated())
                .then(just('.').then(text::digits(10)).or_not()),
        )
        .to_slice()
        .map(|s: &str| Token::Number(s.replace(',', "")));

    // Multi-line string: """..."""
    let multiline_string = just("\"\"\"")
        .ignore_then(
            none_of("\"")
                .or(just('"').then_ignore(none_of("\"")))
                .or(just("\"\"").then_ignore(none_of("\"")))
                .repeated()
                .to_slice(),
        )
        .then_ignore(just("\"\"\""))
        .map(|s: &str| Token::String(s.to_string()));

    // Single-line string: "..."
    let single_string = just('"')
        .ignore_then(
            none_of("\"\\")
                .or(just('\\').ignore_then(any()))
                .repeated()
                .to_slice(),
        )
        .then_ignore(just('"'))
        .map(|s: &str| Token::String(s.to_string()));

    // Try multiline first, then single-line
    let string = multiline_string.or(single_string);

    let account_type = choice((
        just("Assets"),
        just("Liabilities"),
        just("Equity"),
        just("Income"),
        just("Expenses"),
    ));

    let account_component = one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
        .then(
            one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-")
                .repeated(),
        );

    let account = account_type
        .then(just(':').then(account_component).repeated().at_least(1))
        .to_slice()
        .map(|s: &str| Token::Account(s.to_string()));

    let currency = one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
        .then(one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'._-").repeated())
        .to_slice()
        .map(|s: &str| Token::Currency(s.to_string()));

    let tag = just('#')
        .ignore_then(
            one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_/")
                .repeated()
                .at_least(1)
                .to_slice(),
        )
        .map(|s: &str| Token::Tag(s.to_string()));

    let link = just('^')
        .ignore_then(
            one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_/")
                .repeated()
                .at_least(1)
                .to_slice(),
        )
        .map(|s: &str| Token::Link(s.to_string()));

    let meta_key = one_of("abcdefghijklmnopqrstuvwxyz")
        .then(one_of("abcdefghijklmnopqrstuvwxyz0123456789-_").repeated())
        .to_slice()
        .then_ignore(just(':'))
        .map(|s: &str| Token::MetaKey(s.to_string()));

    let keyword = choice((
        just("txn").to(Token::Txn),
        just("balance").to(Token::Balance),
        just("open").to(Token::Open),
        just("close").to(Token::Close),
        just("commodity").to(Token::Commodity),
        just("pad").to(Token::Pad),
        just("event").to(Token::Event),
        just("query").to(Token::Query),
        just("note").to(Token::Note),
        just("document").to(Token::Document),
        just("price").to(Token::Price),
        just("custom").to(Token::Custom),
        just("option").to(Token::Option),
        just("include").to(Token::Include),
        just("plugin").to(Token::Plugin),
        just("pushtag").to(Token::Pushtag),
        just("poptag").to(Token::Poptag),
        just("pushmeta").to(Token::Pushmeta),
        just("popmeta").to(Token::Popmeta),
        just("TRUE").to(Token::True),
        just("FALSE").to(Token::False),
    ));

    // Extended transaction flags: * ! P S T C U R M # ? % &
    // * = completed/cleared
    // ! = pending/needs review
    // P = generated by Pad directive
    // S = summarization transaction
    // T = balance transfer
    // C = price conversion
    // U = unrealized gains
    // R = return (dividend/interest)
    // M = merge
    let flag = one_of("*!PSTCURM#?%&").map(Token::Flag);

    let punctuation = choice((
        just("{{").to(Token::LDoubleBrace),
        just("}}").to(Token::RDoubleBrace),
        just("{").to(Token::LBrace),
        just("}").to(Token::RBrace),
        just("@@").to(Token::AtAt),
        just("@").to(Token::At),
        just(":").to(Token::Colon),
        just(",").to(Token::Comma),
        just("~").to(Token::Tilde),
        flag,
    ));

    let comment = just(';')
        .ignore_then(none_of("\n\r").repeated().to_slice())
        .map(|s: &str| Token::Comment(s.to_string()));

    let newline = just('\n')
        .or(just("\r\n").to('\n'))
        .to(Token::Newline);

    let indent = just(' ')
        .repeated()
        .at_least(2)
        .to(Token::Indent);

    let whitespace = just(' ').or(just('\t')).repeated().at_least(1);

    // Order matters: try more specific patterns first
    let token = choice((
        date,
        string,
        comment,
        tag,
        link,
        meta_key,
        keyword,
        punctuation,
        account,
        number,
        currency,
    ));

    // At the start of a line, check for indent
    let line_start = indent.or_not().map(|opt| opt.unwrap_or(Token::Newline));

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(whitespace.or_not())
        .repeated()
        .collect()
}
