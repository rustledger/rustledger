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
// `tokenize` DOES contain one mid-file-BOM special case: a BOM that
// starts its line keeps its own extent (elsewhere it starts an invalid run
// to the next blank, like any other error; #2928), and it preserves
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
///
/// Horizontal whitespace is emitted as a first-class [`Token::Whitespace`]
/// token (was previously skipped via `#[logos(skip r"[ \t]+")]`). The
/// existing [`tokenize`] entry point filters whitespace out for
/// backward-compat with the AST-style parser; the new
/// [`tokenize_lossless`] entry point keeps them so the CST can
/// reconstruct source byte-for-byte. Both paths share the same Logos
/// implementation — there is exactly one tokenization pass per file.
///
/// Built with logos's `state_machine_codegen` (workspace `Cargo.toml`): one
/// looping state machine, because the default tail-calling functions
/// recursed per character for long tokens and overflowed the stack (#2789).
/// That one function has a large frame, which is the trade (see the
/// module-level `expect` at the top of this file).
#[derive(Logos, Debug, Clone, PartialEq, Eq)]
pub enum Token<'src> {
    /// Horizontal whitespace (`[ \t]+`). Significant for the CST and
    /// for the existing indent post-processing in [`tokenize`]; both
    /// callers handle this variant.
    #[regex(r"[ \t]+")]
    Whitespace(&'src str),
    // ===== Literals =====
    /// A date: beancount's `DATE` rule, `[0-9]{4,}[-/][0-9]+[-/][0-9]+`, so
    /// single-digit fields (`2024-1-5`), `/` separators and extra leading zeros
    /// (`02024-01-01`, `2024-001-01`) all lex as one date, as in beancount
    /// (#2808). Whether the fields form a real date is decided when the token is
    /// read, by `parse_date_token`, as beancount decides it when its lexer
    /// builds the date.
    #[regex(r"[0-9]{4,}[-/][0-9]+[-/][0-9]+")]
    Date(&'src str),

    /// A number with optional thousands separators and decimals.
    /// Examples: 123, 1,234.56, 1234.5678, 1. (trailing decimal)
    /// Negative numbers are handled as unary minus (`-` token + number)
    /// to allow subtraction expressions like `3-2` to parse correctly.
    /// Python beancount v3 requires an integer part before the decimal point.
    /// Leading decimals like `.50` are rejected per the beancount v3 spec.
    ///
    /// ASCII digits only, as beancount's `[0-9]`: the regex `\d` is any
    /// Unicode digit, so `५` (Devanagari five) lexed as a number here, a
    /// metadata value `kk: ५` was dropped with no error, and `५$५` was
    /// three tokens where beancount reads one invalid token.
    #[regex(r"([0-9]{1,3}(,[0-9]{3})*|[0-9]+)(\.[0-9]*)?")]
    Number(&'src str),

    /// A double-quoted string (handles escape sequences).
    /// The slice includes the quotes.
    #[regex(r#""([^"\\]|\\.)*""#)]
    String(&'src str),

    /// An account name like Assets:Bank:Checking, Капитал:Retained-Earnings,
    /// or 资产:银行:支票.
    ///
    /// This is beancount 3.2.3's lexer rule (`lexer.l`, #2906):
    ///
    /// ```text
    /// ACCOUNTTYPE  ([A-Z]|{UTF-8-ONLY})([A-Za-z0-9\-]|{UTF-8-ONLY})*
    /// ACCOUNTNAME  ([A-Z0-9]|{UTF-8-ONLY})([A-Za-z0-9\-]|{UTF-8-ONLY})*
    /// ACCOUNT      {ACCOUNTTYPE}(:{ACCOUNTNAME})+
    /// ```
    ///
    /// so ANY non-ASCII character can start or continue a component:
    /// `Assets:٣` (an Arabic-Indic digit), `Assets:éclair` and `Assets:😀` are
    /// each one account token. Which of them is a valid account NAME is decided
    /// after lexing, as beancount decides it (its grammar checks every account
    /// token against a regex and reports `Invalid account name`): see
    /// [`is_valid_account_name`], whose verdict the validator reports as
    /// `E1005`. A component used to have to START with `\p{Lu}`, `\p{Lo}`,
    /// `\p{Lt}` or a digit here, which split `Assets:٣Foo` into stray tokens,
    /// so ledgers beancount loads failed to parse.
    ///
    /// The non-ASCII allowance inside a component (#1930) matches what
    /// beancount accepts, which is broader than letters: `Assets:CORP✨`
    /// (`So`), `Assets:CORP½` (`No`) and `Assets:CORP→` all load there.
    ///
    /// Restricted to NON-ASCII beyond `[A-Za-z0-9-]` on purpose, and that is
    /// the safety argument: every character with syntactic meaning in beancount
    /// (`@ # ^ { } " ; , * ! ~ ( ) :`) is ASCII, so an account name cannot
    /// swallow a price annotation, tag or cost brace. And no other token
    /// (currency, number, date, keyword, tag, link, key) starts with a
    /// non-ASCII character, so a non-ASCII start is never ambiguous.
    ///
    /// One deliberate difference: a BOM (U+FEFF) does not START an account
    /// here (it may continue one). beancount lexes `\u{feff}Assets:A` as one
    /// account and rejects the name; here a BOM at the start of a line stays its
    /// own layout-transparent error token (`apply_err_layout_transparency`), so
    /// the directive of a concatenated file after it still parses, under the
    /// `BomInDirectiveBody` diagnostic. Anywhere else it starts an invalid run
    /// to the next blank (#2928), unless an account follows it: then the run
    /// of BOMs is its own token there too, so it is reported as the stray BOM
    /// it is, and the account lexes as one (`bom_led_account`).
    /// beancount reads the BOMs into the account and rejects the name when it
    /// loads.
    ///
    /// KNOWN SHARP EDGE: the non-ASCII range includes Unicode whitespace,
    /// control and line-separator characters (NBSP U+00A0, LINE SEPARATOR
    /// U+2028, NEL U+0085, ZWSP U+200B and friends), so `Assets:A<NBSP>B`
    /// lexes as ONE account whose name is visually indistinguishable from
    /// `Assets:A B`. That is deliberate: beancount accepts every one of those
    /// inside an account name (verified individually), so excluding them would
    /// reject files beancount loads. If this is ever revisited it should be as
    /// a lint over account names, not a lexer restriction, so the file still
    /// parses.
    ///
    /// The account type prefix is validated later against options (`name_assets`, etc.).
    #[regex(
        r"([A-Z]|[\x{80}-\x{FEFE}\x{FF00}-\x{10FFFF}])([A-Za-z0-9\-]|[\x{80}-\x{10FFFF}])*(:([A-Z0-9]|[\x{80}-\x{10FFFF}])([A-Za-z0-9\-]|[\x{80}-\x{10FFFF}])*)+"
    )]
    Account(&'src str),

    /// A currency/commodity code like USD, EUR, AAPL, BTC, or single-char tickers like T, V, F.
    /// Uppercase letters, can contain digits, apostrophes, dots, underscores, hyphens,
    /// and must END with a letter or digit: `CAC_` is `CAC` followed by a stray `_`.
    /// BOTH alternatives are beancount's rules exactly (`lexer.l`, #2802): the plain
    /// form is `[A-Z][A-Z0-9'._-]*[A-Z0-9]` or a lone capital letter (beancount's
    /// `CAPITAL`, which it lexes only before whitespace; that part is checked on
    /// directive header lines by `cst::directive_header`, not here).
    /// Single-character currencies (e.g., T for AT&T, V for Visa) are valid NYSE/NASDAQ tickers.
    /// Note: Single-char currencies are disambiguated from transaction flags in the parser.
    /// Also supports `/` prefix for options/futures contracts (e.g., `/ESM24`, `/6J`,
    /// `/LOX21_211204_P100.25`). The `/` form is beancount's rule exactly
    /// (`lexer.l`): after the slash it must contain an uppercase letter, and
    /// it ends with a letter or digit, so `/1.14` is a division and `/6J` (a
    /// futures symbol beancount's own comment uses) is a currency. Longest
    /// match decides between it and `Slash`, as in flex: `10 /6J` is an amount
    /// in `/6J`, `10/6` a division.
    /// Priority 3 ensures Currency wins over Flag for single uppercase letters.
    #[regex(
        r"/[A-Z0-9'._-]*[A-Z]([A-Z0-9'._-]*[A-Z0-9])?|[A-Z]([A-Z0-9'._-]*[A-Z0-9])?",
        priority = 3
    )]
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
    /// The `TRUE` boolean literal. Only the upper-case spelling, as in
    /// beancount (`TRUE` is its only rule): `True` and `true` are its
    /// `Invalid token`, and were read as booleans here (#2813).
    #[token("TRUE")]
    True,
    /// The `FALSE` boolean literal, upper case only, as `TRUE` (#2813).
    #[token("FALSE")]
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
    ///
    /// At least TWO characters before the colon (`+`, not `*`) — beancount's
    /// key rule is a lowercase letter followed by one or more further
    /// characters, so a bare `k:` does not lex as a key there at all and the
    /// file fails to load. We accepted it (#1955).
    ///
    /// Only the LENGTH diverged. Every other part of this rule already matched:
    /// `kk`, `k1`, `k-` and `k_` are accepted by both tools, and an uppercase
    /// start like `A:` is rejected by both. So this is deliberately a minimal
    /// `*` -> `+` rather than a rewrite of the character classes.
    #[regex(r"[a-z][a-zA-Z0-9_-]+:")]
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
            Self::Whitespace(s) => write!(f, "{s}"),
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

/// Whether `name` is a valid beancount account name, as an account token in
/// a ledger is judged.
///
/// This is the CANONICAL rule for an account a ledger can hold, shared by
/// every surface that admits one from ledger text or as ledger text: the
/// validator's Open and account-reference checks, which report `E1005`; the
/// FFI directive builder; a budget's quoted account; the CLI's `--account`.
/// Configuration values that beancount validates with its STRICTER
/// `account.is_valid` family (a plugin's base account, the `account_*` and
/// `name_*` options) use [`is_valid_account_name_strict`] instead.
///
/// Two parts, both needed, as in beancount (#2906):
///
/// 1. `name` lexes to exactly one [`Token::Account`] spanning the whole
///    input. Implemented by running the actual lexer, so this predicate
///    CANNOT drift from what the parser accepts, and a valid name always
///    round-trips through the language. (Before this existed, the validator
///    and loader each hand-implemented the rule with different accepted
///    character sets, and accounts that could never be parsed back could
///    enter through synthesized-directive surfaces.)
/// 2. The name check beancount's grammar applies to every account token it
///    lexed (`valid_account_regexp` in `beancount/parser/grammar.py`, a
///    `regex.match`, so anchored at the start only): the root is one of the
///    configured roots, and the FIRST sub-component starts with `\p{Lu}` or
///    `\p{Nd}` (`ACC_COMP_NAME_RE`). Because the match is a prefix match,
///    later sub-components take anything the lexer takes: `Assets:A:éclair`
///    is valid there and here. The root list is ledger configuration, so it
///    is checked by the caller (the validator, against `name_*`); here the
///    root must start with `\p{Lu}`, which is what beancount requires of a
///    root name (`is_valid_root`, `ACC_COMP_TYPE_RE`).
///
/// So `Assets:٣` (`\p{Nd}`) is valid, while `Assets:éclair` (lowercase),
/// `Assets:😀`, `Assets:²` (`\p{No}`) and a combining-mark start lex as an
/// account but are invalid names, as in bean-check.
///
/// Deliberately broader than beancount in one place, kept from #816 (PR
/// #817): a component may also start with a caseless letter (`\p{Lo}`: CJK,
/// Arabic, Hebrew, ...) or a titlecase letter (`\p{Lt}`), so `資産:現金` and
/// `Assets:日本` are valid here and `Invalid account name` in beancount. Its
/// `\p{Lu}` start is an artifact of scripts with case; rejecting every
/// caseless script would break the non-Latin ledgers #816 was fixed for
/// (beancount/beancount#161, #398, #733). [`is_valid_account_name_strict`]
/// keeps the same extension. Pinned by `is_valid_account_name_matches_beancount`
/// below.
#[must_use]
pub fn is_valid_account_name(name: &str) -> bool {
    if !lexes_as_one_account(name) {
        return false;
    }
    // A lexed account has a root and at least one sub-component, each
    // non-empty, so both starts exist.
    let mut components = name.split(':');
    let starts_validly = |component: Option<&str>, is_root: bool| {
        component
            .and_then(|c| c.chars().next())
            .is_some_and(|c| is_valid_component_start(c, is_root))
    };
    starts_validly(components.next(), true) && starts_validly(components.next(), false)
}

/// Whether `name` is a valid account name by beancount's STRICT check.
///
/// That check is `account.is_valid`: a full match of `ACCOUNT_RE`, so EVERY
/// component starts with `\p{Lu}` (or, after the root, `\p{Nd}`) and holds only
/// letters, decimal digits and `-` (`[\p{L}\p{Nd}\-]`).
///
/// beancount applies it where a value is configuration rather than ledger
/// text: the `currency_accounts` plugin's base account (`account.is_valid`,
/// falling back to `Equity:CurrencyAccounts`), the `account_*` options
/// (`is_valid_leaf`, every component a full `ACC_COMP_NAME_RE` match) and
/// the `name_*` options (`is_valid_root`, a full `ACC_COMP_TYPE_RE` match).
/// Those callers check `Assets:<leaf>` and `<root>:X` through this function.
/// So `Equity:CA:é`, `Conv:😀` and `A😀` are rejected here although
/// [`is_valid_account_name`] accepts the first two as ledger accounts.
///
/// Keeps the `\p{Lo}`/`\p{Lt}` start of [`is_valid_account_name`] (#816), on
/// every component, so a CJK root or leaf configured by option stays usable
/// (`option "name_liabilities" "負債"`), as it was before #2906.
///
/// Implies [`is_valid_account_name`], which it runs first, so a name that
/// passes still round-trips through the lexer.
#[must_use]
pub fn is_valid_account_name_strict(name: &str) -> bool {
    is_valid_account_name(name)
        && name.split(':').enumerate().all(|(i, component)| {
            let mut chars = component.chars();
            chars
                .next()
                .is_some_and(|c| is_valid_component_start(c, i == 0))
                && chars.all(|c| account_char_class(c).is_some())
        })
}

/// A run of BOMs that starts `text`, with nothing else: its length. Every BOM
/// run the lexer and the error recovery look at is trimmed here, so the test
/// counters see each byte it costs.
pub(crate) fn leading_bom_run(text: &str) -> usize {
    let run = text.len() - text.trim_start_matches(crate::bom::BOM_CHAR).len();
    #[cfg(test)]
    test_counters::ERROR_SCANNED_BYTES.with(|c| c.set(c.get() + run));
    run
}

/// When `text` starts with a run of BOMs that beancount reads as the start of
/// an account, the run's length and the account's end (both in bytes from
/// the start of `text`). `None` otherwise.
///
/// beancount's account type is `([A-Z]|{UTF-8-ONLY})` followed by its
/// continuation class, so a BOM, being non-ASCII, may be an account's first
/// character: `\u{feff}Assets:A`, `\u{feff}assets:A`, `\u{feff}1:A` and
/// `\u{feff}:A` are each ONE account there, whose name is rejected only
/// when the file loads. The lexer's own account rule decides it here, on the
/// word with a stand-in non-ASCII character in the BOMs' place (the run's
/// other BOMs are continuation characters, which the stand-in covers too).
///
/// Linear: it reads no further than the next blank, which an account never
/// holds (so an unterminated `"` after the BOMs is not scanned to the end of
/// the file).
pub(crate) fn bom_led_account(text: &str) -> Option<(usize, usize)> {
    const STAND_IN: char = '\u{dc}'; // Ü
    let run = leading_bom_run(text);
    if run == 0 {
        return None;
    }
    let after = &text[run..];
    let word = &after[..after.find([' ', '\t', '\r', '\n']).unwrap_or(after.len())];
    #[cfg(test)]
    test_counters::ERROR_SCANNED_BYTES.with(|c| c.set(c.get() + word.len()));
    let stand_in = format!("{STAND_IN}{word}");
    match Token::lexer(&stand_in).next() {
        Some(Ok(Token::Account(account))) => Some((run, run + account.len() - STAND_IN.len_utf8())),
        _ => None,
    }
}

/// Whether an account begins right where the BOMs that start `text` end, as
/// a token of its own (`\u{feff}Assets:A`, but not `\u{feff}assets:A`, which
/// is an account only with its BOM). See [`bom_led_account`].
pub(crate) fn account_follows_bom_run(text: &str) -> bool {
    bom_led_account(text).is_some_and(|(run, end)| {
        let rest = &text[run..end];
        let mut lexer = Token::lexer(rest);
        matches!(lexer.next(), Some(Ok(Token::Account(_)))) && lexer.span().end == rest.len()
    })
}

/// Whether `name` lexes to exactly one [`Token::Account`] spanning it.
fn lexes_as_one_account(name: &str) -> bool {
    let mut lexer = Token::lexer(name);
    let Some(Ok(Token::Account(_))) = lexer.next() else {
        return false;
    };
    lexer.span() == (0..name.len()) && lexer.next().is_none()
}

/// Whether `c` validly starts an account component (the root when
/// `is_root`): `\p{Lu}`, a decimal digit after the root, or the `\p{Lo}` /
/// `\p{Lt}` extension (#816). See [`is_valid_account_name`].
fn is_valid_component_start(c: char, is_root: bool) -> bool {
    match account_char_class(c) {
        Some(AccountChar::Uppercase | AccountChar::CaselessOrTitlecase) => true,
        Some(AccountChar::Digit) => !is_root,
        Some(AccountChar::OtherLetterOrHyphen) | None => false,
    }
}

/// The characters beancount allows in an account component
/// (`[\p{L}\p{Nd}\-]`), by the class that decides where they may stand:
/// see [`is_valid_account_name`] and [`is_valid_account_name_strict`].
#[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
enum AccountChar {
    /// `\p{Lu}`, a valid start in beancount for the root and a sub-component.
    #[regex(r"\p{Lu}")]
    Uppercase,
    /// `\p{Nd}`, a valid sub-component start in beancount (not a root start).
    #[regex(r"\p{Nd}")]
    Digit,
    /// `\p{Lo}` or `\p{Lt}`: a start only by rledger's deliberate extension
    /// (#816).
    #[regex(r"[\p{Lo}\p{Lt}]")]
    CaselessOrTitlecase,
    /// The rest of `[\p{L}\p{Nd}\-]`: `\p{Ll}`, `\p{Lm}` and `-`, never a
    /// start.
    #[regex(r"[\p{Ll}\p{Lm}\-]")]
    OtherLetterOrHyphen,
}

/// The [`AccountChar`] class of `c`, if it has one. Classified by logos, so
/// the Unicode categories are the same tables the lexer uses.
fn account_char_class(c: char) -> Option<AccountChar> {
    let mut buf = [0u8; 4];
    let text = c.encode_utf8(&mut buf);
    let mut lexer = AccountChar::lexer(text);
    match lexer.next() {
        Some(Ok(class)) if lexer.span().end == text.len() => Some(class),
        _ => None,
    }
}

/// The byte length of the date `text` starts with, or `None` if it does not
/// start with one.
///
/// Implemented by running the lexer, as [`is_valid_account_name`] is, so it is
/// the parser's own rule (beancount's `DATE`, `[0-9]{4,}[-/][0-9]+[-/][0-9]+`):
/// `2024-1-5`, `2024/01/05` and `02024-01-01` are dates, `24-01-15` is not.
/// Says nothing about whether the fields form a real calendar date; see
/// [`crate::parse_date`] for that.
#[must_use]
pub fn leading_date_len(text: &str) -> Option<usize> {
    let mut lexer = Token::lexer(text);
    let Some(Ok(Token::Date(date))) = lexer.next() else {
        return None;
    };
    Some(date.len())
}

/// Whether `name` is a valid commodity (currency) name.
///
/// Implemented by running the lexer, so it is the same rule the parser
/// applies: a configured currency the parser would reject is caught where it
/// is configured rather than when the emitted ledger fails to re-parse.
///
/// This is the canonical currency-name check; route new callers here.
/// The one surface that cannot is `rustledger-core`'s `Amount::from_str`
/// (core is below the parser), which keeps a documented copy
/// (`is_valid_commodity` in `rustledger-core/src/amount.rs`) pinned to
/// this function by the `amount_from_str_currency_matches_lexer` test.
#[must_use]
pub fn is_valid_currency(name: &str) -> bool {
    let mut lexer = Token::lexer(name);
    let Some(Ok(Token::Currency(_))) = lexer.next() else {
        return false;
    };
    lexer.span() == (0..name.len()) && lexer.next().is_none()
}

/// Tokenize source code into a vector of (Token, Span) pairs for the
/// AST-style parser.
///
/// Filters out [`Token::Whitespace`] (mid-line horizontal whitespace)
/// but otherwise emits everything the lexer produces, with
/// post-processing for line-start `#` comments, org-mode `*` headings
/// and indentation.
/// Callers that need a fully-lossless token stream (the CST builder)
/// use [`tokenize_lossless`] instead.
pub fn tokenize(source: &str) -> Vec<(Token<'_>, Span)> {
    tokenize_inner(source, /* keep_whitespace = */ false)
}

/// Tokenize source code losslessly: every byte of `source` appears in
/// exactly one emitted `(Token, Span)` entry. This is the input to
/// the CST builder.
///
/// Differs from [`tokenize`] in that [`Token::Whitespace`] tokens are
/// preserved (the AST-style parser drops them; the CST keeps them so
/// the round-trip stays byte-identical).
pub fn tokenize_lossless(source: &str) -> Vec<(Token<'_>, Span)> {
    tokenize_inner(source, /* keep_whitespace = */ true)
}

/// Upper bound on the up-front token-vector reservation (see `tokenize_inner` /
/// `lossless_kind_tokens`). ~4M entries (~100 MB for a `(kind, span)` tuple) is
/// far above any real ledger's token count, but stops a pathological input from
/// turning `source.len() / 4` into a multi-GB reservation.
pub(crate) const TOKEN_CAPACITY_CAP: usize = 4 << 20;

/// Pull-based tokenizer: the former `tokenize_inner` loop body as an
/// iterator, so the CST path can consume tokens one at a time.
///
/// Materializing the whole-file `Vec<(Token, Span)>` peaked at 2.6 GB
/// of heap on a 173 MB ledger (profiling, issue #2742), and the CST
/// immediately projected it into a second whole-file
/// `Vec<(SyntaxKind, Range)>` (1.6 GB more). [`tokenize`] /
/// [`tokenize_lossless`] keep their `Vec` API by collecting from this
/// iterator; the structured parser streams it instead.
pub(crate) struct TokenIter<'src> {
    lexer: logos::Lexer<'src, Token<'src>>,
    source: &'src str,
    /// End of the text the current `lexer` sees: the whole source, or, in
    /// line-at-a-time mode, the end of the current line (#2784).
    lex_end: usize,
    /// How far line-at-a-time mode lasts: the furthest end of any failed
    /// string scan that was cut at its line (#2784). Before it, every `"`
    /// is escaped in the cut scan's alignment, so no later scan can close
    /// earlier; lexing one line at a time keeps each of them on its line.
    chunk_until: usize,
    keep_whitespace: bool,
    at_line_start: bool,
    last_newline_end: usize,
    /// End of the last `[ \t\r]` run that `stray_cr_trivia_end` scanned and
    /// found not to reach a line ending (#2804 review). A token that starts
    /// before it lies inside that run, so its own scan would stop at the same
    /// byte and fail too; skipping it keeps a long run linear instead of
    /// rescanning the rest of the run for each of its `\r` bytes.
    stray_cr_failed_until: usize,
    /// End of the last run of non-blank characters that `error_later_in_run`
    /// lexed after a lone capital and found free of errors. A lone capital
    /// before it is in that run, so its own lookahead would find no error
    /// either; skipping it keeps a long run of glued one-letter tokens
    /// (`V,V,V,...`) linear.
    capital_run_clean_until: usize,
    pending: Option<(Token<'src>, Span)>,
}

impl<'src> TokenIter<'src> {
    /// Tokenize `source`, preserving or dropping mid-line
    /// [`Token::Whitespace`] per `keep_whitespace` (the AST path drops
    /// it, the CST path keeps it). Layout post-processing (line-start
    /// `#` comments, `*` headings and `Indent`/`DeepIndent` synthesis)
    /// is identical on both paths.
    pub(crate) fn new(source: &'src str, keep_whitespace: bool) -> Self {
        Self {
            lexer: Token::lexer(source),
            source,
            lex_end: source.len(),
            chunk_until: 0,
            keep_whitespace,
            at_line_start: true,
            last_newline_end: 0,
            stray_cr_failed_until: 0,
            capital_run_clean_until: 0,
            pending: None,
        }
    }

    /// Replace the lexer with one over `source[..lex_end]`, positioned at
    /// `from`. In tests, count the bytes the new lexer can see, so the
    /// linear-cost guard can tell a restart over the rest of the file from
    /// a restart over one line (#2784).
    fn restart_lexer(&mut self, from: usize) {
        #[cfg(test)]
        test_counters::RESTART_VISIBLE_BYTES.with(|c| c.set(c.get() + (self.lex_end - from)));
        let mut lexer = Token::lexer(&self.source[..self.lex_end]);
        lexer.bump(from);
        self.lexer = lexer;
    }

    /// The first lexer error in the run of non-blank characters that goes on
    /// at `from`, right after a lone capital: its start, and a lexer that has
    /// just produced it. `None`, and the run remembered as clean, when every
    /// token that starts in the run lexes, or the first error is a `\r`
    /// (which keeps its own extent; see the `Err` arm). A BOM is an error
    /// like any other here: it keeps its own extent only at the start of a
    /// line, and a run that goes on after a lone capital is never there.
    ///
    /// Lexes on a clone of the lexer, dropped unless it is returned. Linear:
    /// a run with an error becomes one error token, so it is not lexed again,
    /// and a clean run is skipped by every later lone capital in it.
    fn error_later_in_run(
        &mut self,
        from: usize,
    ) -> Option<(usize, logos::Lexer<'src, Token<'src>>)> {
        let rest = &self.source.as_bytes()[from..self.lex_end];
        let run_end = from
            + rest
                .iter()
                .position(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
                .unwrap_or(rest.len());
        #[cfg(test)]
        test_counters::CAPITAL_RUN_SCANNED_BYTES.with(|c| c.set(c.get() + (run_end - from)));
        let mut peek = self.lexer.clone();
        while let Some(result) = peek.next() {
            let at = peek.span().start;
            if at >= run_end {
                break;
            }
            if result.is_err() {
                if self.source[at..].starts_with('\r') {
                    break;
                }
                return Some((at, peek));
            }
        }
        self.capital_run_clean_until = run_end;
        None
    }
}

impl TokenIter<'_> {
    /// Where a run of stray `\r` bytes that ends its line ends, if the token
    /// the lexer just produced starts one (#2774).
    ///
    /// Beancount's lexer skips `\r` as whitespace (`[ \t\r]+`), so a `\r`
    /// left over before the line ending (`\r\r\n`, which some editors and
    /// converters write) or at the end of the file is accepted there. Ours
    /// has no rule for a lone `\r`: the `Newline` token (`\r?\n`) claims
    /// only the one right before the `\n`, so every other `\r` came out as an
    /// error token. This turns the whole `[ \t\r]` run, starting at a
    /// `Whitespace` token or a lone-`\r` error, into one `Whitespace` token
    /// when it contains a `\r` and reaches the line ending (stopping before
    /// the `\r` of a `\r\n`, which stays in the `Newline`) or the end of the
    /// source. The bytes stay in the token stream, as trivia.
    ///
    /// Stricter than beancount, deliberately: a `\r` with more of the line
    /// after it (`open\rAssets:Cash`, `; a\rb`, or before the first token of
    /// a line) is still an error, where beancount takes it as a token
    /// separator. The formatter folds such a bare `\r` into a line break
    /// (`crlf_to_lf_outside_strings`, which is what keeps classic-Mac files
    /// formattable), so accepting it would make `rledger format` split a
    /// line that `rledger check` called valid. Pinned by
    /// `test_parse_cr_with_more_of_the_line_after_it_stays_an_error` in
    /// `tests/stray_cr.rs`.
    ///
    /// Returns `None`, after one byte comparison, for an ordinary
    /// `Whitespace` token. Linear: a run that reaches the line ending is
    /// consumed by the token, and a run that does not is remembered in
    /// `stray_cr_failed_until`, so later tokens inside it (its `\r` bytes and
    /// spaces, each a suffix of the run that would stop at the same byte)
    /// return `None` without scanning. Each byte is scanned at most once.
    ///
    /// The offsets are absolute, like the spans. A restart never re-lexes
    /// before a failed run's end: line-at-a-time mode restarts at the old
    /// `lex_end`, and the `Err` arm at the end of the line of a `"` token,
    /// which the lexer only reached by passing the run.
    fn stray_cr_trivia_end(
        &mut self,
        result: &Result<Token<'_>, ()>,
        span: &Range<usize>,
    ) -> Option<usize> {
        let bytes = self.source.as_bytes();
        let mut has_cr = match result {
            Ok(Token::Whitespace(_)) => false,
            Err(()) if &bytes[span.clone()] == b"\r" => true,
            _ => return None,
        };
        if span.start < self.stray_cr_failed_until {
            return None;
        }
        let mut end = span.end;
        while end < self.lex_end {
            match bytes[end] {
                b' ' | b'\t' => end += 1,
                b'\r' if bytes.get(end + 1) != Some(&b'\n') => {
                    has_cr = true;
                    end += 1;
                }
                _ => break,
            }
            #[cfg(test)]
            test_counters::STRAY_CR_SCANNED_BYTES.with(|c| c.set(c.get() + 1));
        }
        // The run ends at a `\n`, at the `\r` of a `\r\n`, or at the end of
        // the source. Line-at-a-time mode ends each chunk after a `\n`, so
        // the scan stops at that `\n` before it reaches a chunk end.
        let at_line_end = if end == self.lex_end {
            end == self.source.len()
        } else {
            matches!(bytes[end], b'\n' | b'\r')
        };
        if has_cr && at_line_end {
            Some(end)
        } else {
            self.stray_cr_failed_until = end;
            None
        }
    }
}

#[cfg(test)]
pub(crate) mod test_counters {
    thread_local! {
        /// Total bytes visible to the lexers `TokenIter::restart_lexer`
        /// created on this thread.
        pub(crate) static RESTART_VISIBLE_BYTES: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
        /// Bytes `TokenIter::stray_cr_trivia_end` stepped over on this thread.
        pub(crate) static STRAY_CR_SCANNED_BYTES: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
        /// Bytes `TokenIter::error_later_in_run` scanned for the end of a run
        /// after a lone capital, on this thread.
        pub(crate) static CAPITAL_RUN_SCANNED_BYTES: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
        /// Bytes logos scanned into the error spans the `Err` arm received,
        /// and bytes the BOM-run and account lookaheads looked at, on this
        /// thread.
        pub(crate) static ERROR_SCANNED_BYTES: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
    }
}

impl<'src> Iterator for TokenIter<'src> {
    type Item = (Token<'src>, Span);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(pending) = self.pending.take() {
            return Some(pending);
        }
        let source = self.source;
        loop {
            let Some(result) = self.lexer.next() else {
                // Line-at-a-time mode (see the `Err` arm): move on to the
                // next line while still before `chunk_until`, then back to
                // the whole rest of the source; stop at its real end.
                if self.lex_end < source.len() {
                    let from = self.lex_end;
                    self.lex_end = if from < self.chunk_until {
                        line_chunk_end(source, from)
                    } else {
                        source.len()
                    };
                    self.restart_lexer(from);
                    continue;
                }
                return None;
            };
            let mut result = result;
            let mut span = self.lexer.span();
            if let Some(end) = self.stray_cr_trivia_end(&result, &span) {
                self.lexer.bump(end - span.end);
                span.end = end;
                result = Ok(Token::Whitespace(&source[span.clone()]));
            }
            // Where the lexer's own error starts, when `result` is one. Past
            // `span.start` only for a lone capital merged into the error
            // after it (below).
            let mut error_start = span.start;
            // beancount lexes a lone capital letter (its `CAPITAL`) only
            // before a space, tab or `\n` (`[A-Z]/[ \t\n]`). Glued to anything
            // else, no rule takes it, so it starts an invalid token there that
            // runs to the next space: `R\x04` is `Invalid token: 'R\x04'` and
            // `Assets:a` is `Invalid token: 'Assets:a'`. Here a lone capital is
            // a `Currency` (or a `Flag`) wherever it stands, and what follows
            // lexes on its own (`Assets:a` is `A`, the key `ssets:` and an
            // error `a`). So when the rest of its run of non-blank characters
            // holds an error, the run from the capital on is one error, as
            // there. Only then: a capital glued to tokens that all lex
            // (`{1 V, 2024-01-01}`, `T#!`) is still a token here, and the
            // parser's glued one-letter rules report it (`directive_header`,
            // `txn_header`).
            if is_lone_capital(&result)
                && span.end >= self.capital_run_clean_until
                && let Some((at, lexer)) = self.error_later_in_run(span.end)
            {
                error_start = at;
                span.end = lexer.span().end;
                self.lexer = lexer;
                result = Err(());
            }
            // A `%` that is not at column 0 is a FLAG in beancount (`[!&#?%]`),
            // never a comment: `  % Assets:A  1 USD` is a flagged posting and
            // `2024-01-01 % "x"` a transaction there (#2802). Only a column-0 `%`
            // line is skipped, as a whole-line comment. Lexing it as a comment to
            // the end of the line dropped the posting, or the rest of the line, in
            // silence. Rewritten here, before the arms below, so an indented one
            // still gets its `Indent` like any other token; the lexer resumes
            // right after it, and a stray `%` elsewhere is reported by the line's
            // own rule.
            //
            // A column-0 `%` with nothing after it on its line is a FLAG too:
            // beancount's rule is `^{FLAGS}/.`, which needs one more character
            // before the line ending, so a bare `%` line is its `unexpected
            // FLAG` error there (#2779). A `\r` counts as that character, so a
            // bare `%` on a CRLF line is still skipped.
            if matches!(result, Ok(Token::PercentComment(_)))
                && !(self.at_line_start
                    && span.start == self.last_newline_end
                    && beancount_ignores_line(&source[span.start..]))
            {
                self.restart_lexer(span.start + 1);
                span.end = span.start + 1;
                result = Ok(Token::Flag(&source[span.clone()]));
            }

            if !self.keep_whitespace && matches!(result, Ok(Token::Whitespace(_))) {
                // AST-path drops mid-line whitespace; the CST path keeps
                // it. Layout-relevant whitespace (start-of-line indentation,
                // BOM error spans) is handled by the dedicated arms below
                // regardless of which path we are on.
                continue;
            }

            match result {
                Ok(Token::Newline) => {
                    self.at_line_start = true;
                    self.last_newline_end = span.end;
                    return Some((Token::Newline, span.into()));
                }
                // A column-0 `#`, `!`, `&`, `?` or `:` with more of its line
                // after it: beancount ignores the whole line (`^[\*\:\#]/.`
                // and `^{FLAGS}/.`, with `FLAGS [!&#?%]`, enter its IGNORE
                // state), so it is one comment token here. The `!`, `&`, `?`
                // and `:` lines were errors before (#2779). A bare marker,
                // with its line ending (or the end of the source) right after
                // it, is not ignored there, as the rule needs one more
                // character: it stays its own token and the parser reports the
                // line, as beancount reports `unexpected HASH`, `FLAG` or
                // `COLON`. `%` is handled above and `*` below. A `#` followed
                // by a tag character never gets here: logos lexes it as a
                // `Tag`, as beancount's tag rule wins over `^#/.` there too.
                Ok(Token::Hash | Token::Pending | Token::Colon | Token::Flag("&" | "?"))
                    if self.at_line_start
                        && span.start == self.last_newline_end
                        && beancount_ignores_line(&source[span.start..]) =>
                {
                    let comment_start = span.start;
                    let line_end = line_end_before_newline(source, span.end);
                    let comment_text = &source[comment_start..line_end];
                    // Skip the rest of the line without lexing it, as
                    // beancount's lexer does (`^#` enters an IGNORE state
                    // that eats `.*`). Lexing it token by token let a `"`
                    // in the comment open a multi-line string that ran
                    // past the line ending and swallowed the directives
                    // after it, with no error (#2775). The lexer resumes
                    // exactly at `line_end`, so the next call emits the
                    // `Newline` (or the stray-`\r` trivia before it, or ends
                    // the stream) normally. `line_end` sits on a `\r`, a
                    // `\n` or the end of the source, so it is always a char
                    // boundary in range.
                    self.lexer.bump(line_end - span.end);
                    self.at_line_start = false;
                    return Some((
                        Token::Comment(comment_text),
                        Span {
                            start: comment_start,
                            end: line_end,
                        },
                    ));
                }
                Ok(Token::Star) if self.at_line_start && span.start == self.last_newline_end => {
                    // An org-mode heading. Beancount ignores the whole line
                    // (`^\*/.` enters the same IGNORE state as `^#`), so,
                    // like the `#` arm, the rest of the line is not lexed.
                    // Lexing it token by token let a `"` in the heading open
                    // an unterminated string that ran to the end of the file
                    // and swallowed every directive after it, with no error
                    // (#2778). The rest of the line comes out as one
                    // `Error` token after the `Star`, so the line keeps its
                    // shape: a `STAR`-led `ERROR_NODE`, silenced by the
                    // section-marker checks in both conversion paths, and
                    // copied verbatim by the formatter. Which `STAR` lines
                    // are SILENCED is decided separately, and more
                    // narrowly, by `convert::is_section_marker` (#2783):
                    // keep this arm at least as broad as that rule, so a
                    // silenced line is always one whose rest was skipped.
                    let line_end = line_end_before_newline(source, span.end);
                    self.at_line_start = false;
                    if line_end > span.end {
                        self.lexer.bump(line_end - span.end);
                        self.pending = Some((
                            Token::Error(&source[span.end..line_end]),
                            Span {
                                start: span.end,
                                end: line_end,
                            },
                        ));
                    }
                    return Some((Token::Star, span.into()));
                }
                Ok(token) => {
                    // Check for indentation at line start
                    if self.at_line_start && span.start > self.last_newline_end {
                        // Count leading whitespace between last newline and this token
                        // Tabs count as indentation (treat 1 tab as 4 spaces for counting purposes)
                        let leading = &source[self.last_newline_end..span.start];
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
                            let indent_start = self.last_newline_end;
                            let indent_end = self.last_newline_end + char_count;
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
                            self.pending = Some((token, span.into()));
                            self.at_line_start = false;
                            return Some((
                                indent_token,
                                Span {
                                    start: indent_start,
                                    end: indent_end,
                                },
                            ));
                        }
                    }
                    self.at_line_start = false;
                    return Some((token, span.into()));
                }
                Err(()) => {
                    // Lexer error - produce an Error token with the invalid source text.
                    let mut span = span;
                    // beancount's invalid token (its `INVALID` state): from the
                    // first character no rule takes, everything up to the next
                    // space, tab, `\r` or `\n` (`[^ \t\n\r]+`) is ONE token and
                    // one `Invalid token` error. logos ends its error where its
                    // own scan stopped, often after one character, so
                    // `Ass'ets:A` came out as several error tokens and the
                    // tokens between them, each reported. The run takes in
                    // everything glued to the bad character, a `"` or a `;`
                    // too, so that quote opens no string and that `;` no
                    // comment, as there.
                    //
                    // Two errors keep their own extent. A `\r` with more of
                    // its line after it (beancount reads it as a space; see
                    // `stray_cr_trivia_end`). And a mid-file BOM that starts
                    // its line, which is layout-transparent here
                    // (`apply_err_layout_transparency`) so that the directive
                    // of a concatenated file after it still parses, under its
                    // own `BomInDirectiveBody` diagnostic: deliberately not
                    // beancount's `Invalid token: '\ufeff2024-01-01'`.
                    //
                    // Only there (#2928). Anywhere else on a line, layout is
                    // not at stake, and a BOM-led error runs to the next
                    // blank like any other, as beancount's does: `<BOM>"x"`,
                    // `<BOM>#!d` and `<BOM>#+x` are each one invalid token,
                    // so the quote opens no string and the `#!` / `#+` starts
                    // no token of its own.
                    let text = &source[span.start..];
                    #[cfg(test)]
                    test_counters::ERROR_SCANNED_BYTES
                        .with(|c| c.set(c.get() + (span.end - span.start)));
                    let bom_starts_line = text.starts_with(crate::bom::BOM_CHAR)
                        && self.at_line_start
                        && span.start == self.last_newline_end;
                    let end = if text.starts_with('\r') || bom_starts_line {
                        span.end
                    } else if let Some((run, account_end)) = bom_led_account(text) {
                        // A run of BOMs beancount reads as an account's start
                        // (`bom_led_account`). When an account of its own
                        // follows the BOMs (`$x \u{feff}Assets:A`), they are
                        // one token, as the line-start ones are, and the
                        // account lexes as one; otherwise (`\u{feff}assets:A`,
                        // `\u{feff}1:A`) the token ends where beancount's
                        // account does. Either way the error recovery counts
                        // it as none of beancount's invalid tokens.
                        if account_follows_bom_run(text) {
                            span.start + run
                        } else {
                            span.start + account_end
                        }
                    } else {
                        span.start + text.find([' ', '\t', '\r', '\n']).unwrap_or(text.len())
                    };
                    let mut restart = end < span.end;
                    // A failed `String` scan. logos reports everything the
                    // `"([^"\\]|\\.)*"` regex scanned as ONE error, so a
                    // stray quote hid every directive after it behind a
                    // single error (#2784); beancount reports the quote's
                    // run and carries on. The scan fails in one of two ways:
                    // it reaches the end of the input without a closing `"`,
                    // or it stops at a `\` before a line break (`\\.` does
                    // not match a newline). Either way the error ends at its
                    // run, above, and lexing resumes there. This cannot
                    // change which quotes pair up: every `"` inside the
                    // scanned region was escaped from the scan's point of
                    // view, so it is glued to the `\` before it, and the
                    // invalid run that takes that `\` takes the quote too.
                    if source[error_start..span.end].starts_with('"') {
                        let line_end = line_end_before_newline(source, error_start);
                        if line_end < span.end {
                            // Every `"` up to where this scan stopped is
                            // escaped in its alignment, so any later scan
                            // starting before that point reaches it (or the
                            // end of its own line) too. Lex one line at a
                            // time up to there, so each such scan stops at
                            // its own line: restarting over the whole rest
                            // of the file let K stray quotes cost O(K * n)
                            // (one `\"` per line), whichever way the scans
                            // stopped.
                            self.chunk_until = self.chunk_until.max(span.end);
                            self.lex_end = line_chunk_end(source, line_end);
                            restart = true;
                        }
                    }
                    if restart {
                        self.restart_lexer(end);
                    } else if end > span.end {
                        self.lexer.bump(end - span.end);
                    }
                    span.end = end;
                    let invalid_text = &source[span.clone()];
                    apply_err_layout_transparency(
                        invalid_text,
                        span.start,
                        &mut self.at_line_start,
                        &mut self.last_newline_end,
                    );
                    return Some((Token::Error(invalid_text), span.into()));
                }
            }
        }
    }
}

/// Whether `result` is a lone ASCII capital letter, which lexes as a one-letter
/// `Currency` (or `Flag`) here and is beancount's `CAPITAL` only before a
/// space, tab or `\n`. See the lookahead in `TokenIter::next`.
const fn is_lone_capital(result: &Result<Token<'_>, ()>) -> bool {
    matches!(result, Ok(Token::Currency(s) | Token::Flag(s))
        if s.len() == 1 && s.as_bytes()[0].is_ascii_uppercase())
}

/// Whether beancount ignores the whole line starting at column 0 with `line`.
///
/// `line` is the line's text from column 0 on (the rest of the source from
/// there will do). Ignored are a `;` comment, and a `#`, `*`, `:` or flag
/// character (`[!&#?%]`) with at least one more byte on its line, except a
/// `#` that starts a tag (#2779).
///
/// Beancount's rules are `^[\*\:\#]/.` and `^{FLAGS}/.`, and flex's `.` is
/// any byte but `\n`: a bare marker, with its line ending or the end of the
/// source right after it, is a token there (reported as `unexpected HASH`,
/// `FLAG`, `ASTERISK` or `COLON`), and a `\r` counts as the byte, so a bare
/// marker on a CRLF line is ignored. A `#` with a tag character after it is
/// a `TAG`, as beancount's longer tag match wins. The one rule for the
/// lexer's column-0 `#`, `!`, `&`, `?`, `:` and `%` arms in `TokenIter` and
/// for `convert`'s `previous_line_is_a_gap` and `is_section_marker` (the
/// `*` heading), of the formatter's `emit_error_node`, and of the LSP's
/// parse-error surface cleanup (`clean_line` in `rustledger-lsp`), which is
/// why it is public. The formatter's line-ending helpers follow it through
/// the lexer itself (`format::StringLiterals`).
#[must_use]
pub fn beancount_ignores_line(line: &str) -> bool {
    match line.as_bytes() {
        [b';', ..] => true,
        [b'#', next, ..] => {
            *next != b'\n' && !(next.is_ascii_alphanumeric() || b"-_/.".contains(next))
        }
        [b'*' | b':' | b'!' | b'&' | b'?' | b'%', next, ..] => *next != b'\n',
        _ => false,
    }
}

/// The end of the line that contains `from`, including its `\n` (or the end
/// of the source). `TokenIter` lexes one such line at a time after a failed
/// string scan was cut at its line, up to where that scan stopped (#2784).
fn line_chunk_end(source: &str, from: usize) -> usize {
    source[from..]
        .find('\n')
        .map_or(source.len(), |i| from + i + 1)
}

/// Where a whole-line token that starts before `from` ends: before the
/// `Newline` token that follows it, or at the end of the source, and before
/// the stray-`\r` run (a `[ \t\r]` run from a `\r` on) right in front of
/// either.
///
/// `Newline` is `\r?\n`, so on a CRLF line it starts at the `\r`; ending at
/// the `\n` would hand that byte to both tokens and break the lossless
/// round-trip (#2769). A run of spaces, tabs and `\r`s from a `\r` on before
/// it (`\r\r\n`, `\r \r\n`), or before the end of the source, is left out
/// too: it lexes as the `Whitespace` trivia that follows the line (#2774),
/// as after any other token, and `format::crlf_to_lf_outside_strings` drops
/// it, so the formatter reads the line the same with or without that fold
/// (#2779). Spaces and tabs before the run's first `\r` stay in the line,
/// and so does a `\r` with more of the line after it. The result sits on a
/// `\r`, a `\n` or the end of the source, so it is always a char boundary.
/// Shared by the column-0 `#` comment and `*` heading arms of `TokenIter`,
/// and by its cut of an unterminated string.
fn line_end_before_newline(source: &str, from: usize) -> usize {
    let nl = source[from..].find('\n').map_or(source.len(), |i| from + i);
    let line = &source[from..nl];
    let run_start = line.trim_end_matches([' ', '\t', '\r']).len();
    from + line[run_start..]
        .find('\r')
        .map_or(line.len(), |i| run_start + i)
}

fn tokenize_inner(source: &str, keep_whitespace: bool) -> Vec<(Token<'_>, Span)> {
    // Pre-size to avoid reallocation churn. A beancount token averages ~4 bytes
    // of source (dates, numbers, currencies, whitespace runs), so `len / 4` is a
    // close estimate of the token count. Profiling showed the unsized `Vec`
    // reallocating ~17× — the single largest lexer allocation (see the
    // `profiling` data branch). Capped so a pathological input (e.g. a huge
    // whitespace/comment run that lexes to few tokens) can't amplify into a
    // multi-GB up-front reservation — the parser must handle malformed input
    // gracefully; beyond the cap the `Vec` just grows normally.
    let mut tokens = Vec::with_capacity((source.len() / 4).min(TOKEN_CAPACITY_CAP));
    tokens.extend(TokenIter::new(source, keep_whitespace));
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
        // START of account components. Emoji and symbols are not — there.
        //
        // INSIDE a component they now are (#1930). This assertion used to
        // require the opposite; beancount accepts `Assets:CORP✨` and a
        // committed fava-portfolio-returns fixture uses it, so the old
        // expectation was pinning a stricter-than-beancount rule that made us
        // refuse real files. Verified against beancount before flipping it.
        let tokens = tokenize("Assets:CORP✨");
        assert!(
            matches!(tokens[0].0, Token::Account("Assets:CORP✨")),
            "a non-ASCII symbol inside a component is a valid Account (beancount accepts it)"
        );
        assert!(
            !tokens.iter().any(|(t, _)| matches!(t, Token::Error(_))),
            "the whole name lexes cleanly now; no Error token should remain"
        );
        // The boundary that keeps the widening safe: ASCII punctuation still
        // terminates the account, so a price sigil cannot be swallowed into it.
        let tokens = tokenize("Assets:CORP@2.00");
        assert!(
            matches!(tokens[0].0, Token::Account("Assets:CORP")),
            "an ASCII `@` must still end the account name, not join it"
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

    /// Cutting a failed `"` scan at its line must not make lexing quadratic
    /// (#2784 review). With one `\"` per line, every line's quote opens a
    /// scan that cannot close; restarting the lexer over the rest of the
    /// file for each one cost O(lines * size) (55 s on 900 KB). The scans
    /// fail either at the end of the input or, with a lone `\` line after
    /// them, at that `\`-before-newline stop (43 s on 900 KB before the
    /// line mode covered that case). The bytes visible to restarted lexers
    /// must stay linear in the input either way.
    #[test]
    fn test_tokenize_lossless_unterminated_quotes_lex_in_linear_time() {
        const LINES: usize = 2_000;
        for (label, tail) in [("end of input", ""), ("backslash stop", "\\\n")] {
            let src = "\\\"\n".repeat(LINES) + tail;
            test_counters::RESTART_VISIBLE_BYTES.with(|c| c.set(0));
            let tokens = tokenize_lossless(&src);
            let visible = test_counters::RESTART_VISIBLE_BYTES.with(std::cell::Cell::get);
            assert!(
                visible <= 2 * src.len(),
                "{label}: restarted lexers saw {visible} bytes of a {}-byte input",
                src.len()
            );
            // And each `\"` line still comes out as one invalid token, as in
            // beancount, then its newline.
            assert!(
                tokens[..2 * LINES]
                    .chunks(2)
                    .all(|t| matches!(t, [(Token::Error("\\\""), _), (Token::Newline, _)])),
                "{label}: {:?}",
                &tokens[..6]
            );
        }
    }

    /// The lookahead after a lone capital (`error_later_in_run`) stays linear
    /// (#2872). Each lone capital in a run of glued one-letter tokens would
    /// rescan the rest of the run for an error; a clean run is remembered, and
    /// a run with an error becomes one token, so neither is scanned again.
    #[test]
    fn test_tokenize_lossless_lone_capital_lookahead_is_linear() {
        const N: usize = 20_000;
        for (label, src, errors) in [
            ("clean run", "{1 ".to_string() + &"V,".repeat(N) + "}\n", 0),
            ("error at its end", "V,".repeat(N) + "$\n", 1),
        ] {
            test_counters::CAPITAL_RUN_SCANNED_BYTES.with(|c| c.set(0));
            let tokens = tokenize_lossless(&src);
            let scanned = test_counters::CAPITAL_RUN_SCANNED_BYTES.with(std::cell::Cell::get);
            assert!(
                scanned <= 2 * src.len(),
                "{label}: scanned {scanned} bytes of a {}-byte input",
                src.len()
            );
            let found = tokens
                .iter()
                .filter(|(t, _)| matches!(t, Token::Error(_)))
                .count();
            assert_eq!(found, errors, "{label}");
        }
    }

    /// A long `[ \t\r]` run that does not reach its line ending must not
    /// make lexing quadratic (#2804 review). Each of its `\r` bytes is a
    /// lone-`\r` error token whose stray-`\r` scan ran to the end of the run
    /// and failed, so a run of N bytes cost O(N^2) (over 120 s on 1 MB). The
    /// bytes those scans step over must stay linear in the input.
    #[test]
    fn test_tokenize_lossless_long_cr_run_not_at_a_line_end_lexes_in_linear_time() {
        const N: usize = 20_000;
        for (label, src) in [
            (
                "\\r run",
                "2024-01-01 open Assets:A\n".to_string() + &"\r".repeat(N) + "x\n",
            ),
            ("\\r and space run", "\r ".repeat(N) + "x\n"),
            // An unterminated quote puts the rest of the file in
            // line-at-a-time mode, so the run is lexed after a restart.
            (
                "\\r run in line-at-a-time mode",
                "\"x\n".to_string() + &"\r".repeat(N) + "y\n",
            ),
        ] {
            test_counters::STRAY_CR_SCANNED_BYTES.with(|c| c.set(0));
            let tokens = tokenize_lossless(&src);
            let scanned = test_counters::STRAY_CR_SCANNED_BYTES.with(std::cell::Cell::get);
            assert!(
                scanned <= 2 * src.len(),
                "{label}: stray-\\r scans stepped over {scanned} bytes of a {}-byte input",
                src.len()
            );
            // Still errors: the run is followed by more of the line.
            assert!(
                tokens.iter().any(|(t, _)| matches!(t, Token::Error("\r"))),
                "{label}"
            );
        }
    }

    /// A column-0 `#` comment ends exactly where the following `Newline`
    /// token starts: before the one `\r` that `\r?\n` claims (#2769). Extra
    /// `\r` bytes before it, and a trailing `\r` at EOF, are `Whitespace`
    /// trivia after the comment, as after any other token (#2774); a `\r`
    /// with more of the line after it stays in the comment.
    #[test]
    fn test_tokenize_lossless_hash_comment_ends_before_crlf() {
        let span = |t: &(Token<'_>, Span)| (t.1.start, t.1.end);

        let tokens = tokenize_lossless("# note\r\n");
        assert_eq!(tokens.len(), 2);
        assert!(matches!(tokens[0].0, Token::Comment("# note")));
        assert!(matches!(tokens[1].0, Token::Newline));
        assert_eq!((span(&tokens[0]), span(&tokens[1])), ((0, 6), (6, 8)));

        let tokens = tokenize_lossless("# note\r\r\n");
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[0].0, Token::Comment("# note")));
        assert!(matches!(tokens[1].0, Token::Whitespace("\r")));
        assert!(matches!(tokens[2].0, Token::Newline));
        let spans: Vec<_> = tokens.iter().map(span).collect();
        assert_eq!(spans, [(0, 6), (6, 7), (7, 9)]);

        let tokens = tokenize_lossless("# note\n");
        assert!(matches!(tokens[0].0, Token::Comment("# note")));
        assert_eq!((span(&tokens[0]), span(&tokens[1])), ((0, 6), (6, 7)));

        // No `\n` follows, so no newline token claims the `\r`: it is the
        // trailing whitespace of the last line.
        let tokens = tokenize_lossless("# note\r");
        assert_eq!(tokens.len(), 2);
        assert!(matches!(tokens[0].0, Token::Comment("# note")));
        assert!(matches!(tokens[1].0, Token::Whitespace("\r")));
        assert_eq!(span(&tokens[1]), (6, 7));

        let tokens = tokenize_lossless("# a\rb\r\n");
        assert!(matches!(tokens[0].0, Token::Comment("# a\rb")));
        assert!(matches!(tokens[1].0, Token::Newline));
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

    /// A `%` that is not at column 0 is a FLAG, as in beancount (#2802), and an
    /// indented one still gets its `Indent`, like any token starting a line. At
    /// column 0 it is a whole-line comment.
    #[test]
    fn test_tokenize_percent_is_a_flag_outside_column_0() {
        let tokens = tokenize("2024-01-01 *\n  % Assets:A  1 USD\n% note\n");
        let kinds: Vec<String> = tokens.iter().map(|(t, _)| format!("{t:?}")).collect();
        let at = kinds
            .iter()
            .position(|k| k.starts_with("Flag(\"%\")"))
            .expect("a `%` flag");
        assert!(kinds[at - 1].starts_with("Indent("), "{kinds:?}");
        assert!(kinds[at + 1].starts_with("Account("), "{kinds:?}");
        assert!(
            kinds
                .iter()
                .any(|k| k.starts_with("PercentComment(\"% note\")")),
            "{kinds:?}"
        );
    }

    /// Which column-0 lines beancount ignores (#2779), checked against
    /// bean-check 3.2.3, and that the lexer makes exactly those (but `*`,
    /// which keeps its own token shape) one comment token.
    #[test]
    fn test_beancount_ignores_line_matches_the_lexer() {
        let cases = [
            ("; x", true),
            (";", true),
            ("# x", true),
            ("#!x", true),
            ("#\r", true),
            ("#", false),
            ("#\n", false),
            ("#a b", false),
            ("#.x", false),
            ("! x", true),
            ("!x", true),
            ("!\r", true),
            ("!", false),
            ("!\n", false),
            ("&x", true),
            ("&", false),
            ("?x", true),
            ("?\n", false),
            (":x", true),
            (": \"q", true),
            (":\n", false),
            ("%x", true),
            ("%\r", true),
            ("%\n", false),
            ("*x", true),
            ("*", false),
            ("P x", false),
            ("2024", false),
        ];
        for (line, ignored) in cases {
            assert_eq!(beancount_ignores_line(line), ignored, "{line:?}");
            if line.starts_with('*') {
                continue;
            }
            let first = &tokenize(line)[0].0;
            let is_comment = matches!(
                first,
                Token::Comment(_) | Token::PercentComment(_) | Token::Shebang(_)
            );
            assert_eq!(is_comment, ignored, "{line:?}: {first:?}");
        }
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

    /// A long run of BOMs, at the start of a line or in the middle of one, and
    /// glued to an invalid run or to an account, is lexed and parsed in linear time: no
    /// BOM makes logos or the account lookahead rescan the BOMs after it, and
    /// no restart sees the rest of the line again (#2928). A version that let
    /// a BOM start an account scanned each line-start BOM through every BOM
    /// after it, and a 1 MB line took over a minute.
    #[test]
    fn test_tokenize_long_bom_runs_are_linear() {
        let bom = crate::bom::BOM;
        // A short run first, so a quadratic version fails on the counts in a
        // few seconds rather than running for minutes on the 1 MB one.
        for count in [20_000, 350_000] {
            let run = bom.repeat(count);
            // A wall-clock bound too, generous for a debug build, for a
            // rescan the counters do not see (a lookahead that trims the
            // rest of the run itself): quadratic, the short run takes many
            // seconds, linear well under one.
            let started = std::time::Instant::now();
            check_linear_bom_run(&[
                format!("x\n{run}a\n"),
                format!("x\n{run}Assets:A\n"),
                format!("x {run}a\n"),
                format!("x {run}Assets:A\n"),
                format!("x\n{run} a\n"),
            ]);
            if count == 20_000 {
                let took = started.elapsed();
                assert!(took.as_secs() < 5, "{count} BOMs took {took:?}");
            }
        }
    }

    fn check_linear_bom_run(sources: &[String]) {
        for source in sources {
            test_counters::ERROR_SCANNED_BYTES.with(|c| c.set(0));
            test_counters::RESTART_VISIBLE_BYTES.with(|c| c.set(0));
            let tokens = tokenize_lossless(source);
            assert!(!tokens.is_empty());
            // The whole parse too: its error recovery asks about each BOM
            // token, and a lookahead over the rest of the run per BOM was
            // quadratic there while the lexer was linear.
            let result = crate::parse(source);
            assert!(!result.errors.is_empty());
            let scanned = test_counters::ERROR_SCANNED_BYTES.with(std::cell::Cell::get);
            let restarted = test_counters::RESTART_VISIBLE_BYTES.with(std::cell::Cell::get);
            assert!(
                scanned <= 8 * source.len() && restarted <= 8 * source.len(),
                "{} bytes: {scanned} scanned in errors, {restarted} seen by restarts",
                source.len()
            );
        }
    }

    /// The error tokens of `source`, through the lossless (CST) tokenizer.
    fn error_tokens(source: &str) -> Vec<&str> {
        tokenize_lossless(source)
            .into_iter()
            .filter_map(|(t, _)| match t {
                Token::Error(s) => Some(s),
                _ => None,
            })
            .collect()
    }

    /// In the middle of a line, a BOM-led error runs to the next space, tab
    /// or line ending, as beancount's `<INVALID>[^ \t\n\r]+` does (#2928): a
    /// `"` after the BOM opens no string, and a `#!` or `#+` starts no token
    /// of its own. Two BOMs in a row are one run too.
    #[test]
    fn test_tokenize_mid_line_bom_runs_to_next_blank() {
        let bom = crate::bom::BOM;
        for (rest, run) in [
            (format!("{bom}\"x\" USD"), format!("{bom}\"x\"")),
            (format!("{bom}#!d"), format!("{bom}#!d")),
            (format!("{bom}#+x\tUSD"), format!("{bom}#+x")),
            (format!("{bom}{bom}\"x\"\n"), format!("{bom}{bom}\"x\"")),
            (format!("x{bom}\"y\""), format!("x{bom}\"y\"")),
        ] {
            let source = format!("2024-01-02 * \"n\" {rest}");
            assert_eq!(error_tokens(&source), vec![run.as_str()], "{source:?}");
        }
    }

    /// After a lone capital, a BOM is an error like any other: the run from
    /// the capital on is one error token, so its quote opens no string.
    #[test]
    fn test_tokenize_bom_after_lone_capital_runs_to_next_blank() {
        let bom = crate::bom::BOM;
        let source = format!("2024-01-02 * \"n\" A{bom}\"x\" USD\n");
        assert_eq!(
            error_tokens(&source),
            vec![format!("A{bom}\"x\"").as_str()],
            "{source:?}"
        );
    }

    /// At the start of a line a BOM still keeps its own extent (layout
    /// transparency for concatenated files, #2928 leaves it as it was): the
    /// date after it lexes, and so does a quote, each BOM being one token.
    #[test]
    fn test_tokenize_line_start_bom_keeps_own_extent() {
        let bom = crate::bom::BOM;
        for (source, errors) in [
            (format!("x\n{bom}2024-01-02 open Assets:A\n"), vec![bom]),
            (format!("x\n{bom}{bom}\"q\"\n"), vec![bom, bom]),
        ] {
            let mut want = vec!["x"];
            want.extend(errors);
            assert_eq!(error_tokens(&source), want, "{source:?}");
        }
        let source = format!("x\n{bom}2024-01-02 open Assets:A\n");
        assert!(
            tokenize_lossless(&source)
                .iter()
                .any(|(t, _)| matches!(t, Token::Date(_))),
            "{source:?}"
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

    #[test]
    fn is_valid_currency_matches_lexer_rule() {
        use super::is_valid_currency as ok;
        for good in ["USD", "EUR", "T", "VTI", "BRK.B", "ETH-2", "U.S-D'X"] {
            assert!(ok(good), "{good}");
        }
        for bad in ["", "usd", "€", " USD", "USD ", "US D", "1USD"] {
            assert!(!ok(bad), "{bad:?}");
        }
    }

    /// Drift guard for #2807: `rustledger-core`'s `Amount::from_str` cannot
    /// call [`is_valid_currency`] (core is below the parser), so it carries a
    /// documented copy of the rule (`is_valid_commodity` in
    /// `rustledger-core/src/amount.rs`). This compares the two on every
    /// string of up to five characters over an alphabet covering each
    /// character class the rule distinguishes, plus the one-letter flag
    /// letters, the shapes that broke and the keyword tokens that outrank a
    /// currency.
    #[test]
    fn amount_from_str_currency_matches_lexer() {
        use rustledger_core::Amount;
        use std::str::FromStr;

        fn agree(s: &str) {
            let core = Amount::from_str(&format!("1 {s}")).is_ok();
            assert_eq!(
                core,
                is_valid_currency(s),
                "Amount::from_str and is_valid_currency disagree on {s:?}"
            );
        }

        // `T` and `P` are flag letters (`[PSTCURM]`): a lexer change that let a
        // flag token beat `Currency` for one letter would trip here.
        const ALPHABET: [char; 12] = [
            'A', 'T', 'P', '0', '\'', '.', '_', '-', '/', 'a', ':', '\u{c9}',
        ];
        let mut frontier = vec![String::new()];
        for _ in 0..5 {
            let mut next = Vec::with_capacity(frontier.len() * ALPHABET.len());
            for prefix in &frontier {
                for c in ALPHABET {
                    let mut s = prefix.clone();
                    s.push(c);
                    agree(&s);
                    next.push(s);
                }
            }
            frontier = next;
        }

        for s in [
            "/6J",
            "/ESM24",
            "/LOX21_211204_P100.25",
            "USD_",
            "A",
            "C_",
            "HOOL'",
            "P",
            "S",
            "T",
            "C",
            "U",
            "R",
            "M",
            "TT",
            "USD-",
            "BRK.B",
            "/1.14",
            "TRUE",
            "FALSE",
            "NULL",
            "True",
            "TRUEX",
            "NULL1",
            "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789",
        ] {
            agree(s);
        }
        // The named shapes, pinned on both sides (not just agreement).
        for good in ["/6J", "/ESM24", "A"] {
            assert!(is_valid_currency(good), "{good}");
        }
        for bad in ["USD_", "C_", "HOOL'", "USD-"] {
            assert!(!is_valid_currency(bad), "{bad}");
        }
    }

    #[test]
    fn is_valid_account_name_matches_lexer_rule() {
        use super::is_valid_account_name as ok;
        // Valid: standard, unicode roots/components, digit-start SUB-component,
        // hyphens, deep nesting.
        assert!(ok("Assets:Cash"));
        assert!(ok("Assets:US:BofA:Checking"));
        assert!(ok("Assets:2024-Bonus"));
        assert!(ok("Активы:Наличные")); // Cyrillic (\p{Lu} root)
        assert!(ok("資産:現金")); // CJK (\p{Lo} root)
        assert!(ok("Assets:Ægir")); // non-ASCII uppercase start
        // Invalid: single component (roots alone are not accounts).
        assert!(!ok("Assets"));
        // Invalid: digit-start ROOT (sub-components may, roots may not).
        assert!(!ok("1Assets:Cash"));
        // Invalid: lowercase starts (ASCII and non-ASCII).
        assert!(!ok("assets:Cash"));
        assert!(!ok("Assets:cash"));
        assert!(!ok("Assets:\u{e9}cash")); // é — lowercase letter start
        // Invalid: ASCII characters outside letters/digits/hyphen. The ASCII
        // restriction is the safety boundary — every character with syntactic
        // meaning in beancount is ASCII, so these can never be absorbed into an
        // account name.
        assert!(!ok("Assets:Ca sh"));
        assert!(!ok("Assets:Cash!"));
        assert!(!ok("Assets:Ca_sh")); // underscore is currency-only
        // Valid since #1930: ANY non-ASCII inside a component. beancount
        // accepts all of these; requiring `\p{L}` here meant rejecting files
        // that exist.
        assert!(ok("Assets:N\u{2116}1")); // № numero sign (So)
        assert!(ok("Assets:Cash\u{1F600}")); // emoji (So)
        // Invalid: structural.
        assert!(!ok(""));
        assert!(!ok("Assets:"));
        assert!(!ok(":Cash"));
        assert!(!ok("Assets::Cash"));
        assert!(!ok(" Assets:Cash"));
        assert!(!ok("Assets:Cash "));
        assert!(!ok("Assets:Cash\nAssets:Two"));
    }

    /// #2906: an account is lexed as beancount 3.2.3 lexes it (any non-ASCII
    /// character starts a component), and its name is then judged as
    /// beancount's grammar judges it. Each verdict below was checked with
    /// bean-check 3.2.3 (`2024-01-01 open <name>`), except the two marked as
    /// rledger's deliberate `\p{Lo}`/`\p{Lt}` extension (#816).
    #[test]
    fn is_valid_account_name_matches_beancount() {
        use super::is_valid_account_name as ok;
        let lexes_whole = |name: &str| {
            let tokens = tokenize(name);
            tokens.len() == 1 && tokens[0].0 == Token::Account(name)
        };
        // Valid in beancount: a `\p{Nd}` or `\p{Lu}` first sub-component
        // start, and anything the lexer takes after it.
        for name in [
            "Assets:\u{663}",            // ٣, Arabic-Indic digit three (Nd)
            "Assets:\u{663}Foo",         // ٣Foo
            "Assets:A\u{663}",           // A٣
            "Assets:\u{dc}n\u{ef}",      // Ünï
            "Assets:\u{c4}",             // Ä
            "Assets:3",                  // ASCII digit
            "Assets:A\u{1F600}",         // A😀
            "Assets:A:\u{65e5}\u{672c}", // later component: 日本
            "Assets:A:\u{e9}clair",      // later component: lowercase start
            "Assets:A:\u{1F600}",        // later component: emoji start
            "Assets:\u{663}:\u{e9}",     // ٣:é
        ] {
            assert!(lexes_whole(name), "{name} lexes as one account");
            assert!(ok(name), "{name} is valid in beancount");
        }
        // Lexed as one account by both, but `Invalid account name` in
        // beancount: the first sub-component start is not `\p{Lu}`/`\p{Nd}`.
        for name in [
            "Assets:\u{e9}clair", // éclair: lowercase (Ll)
            "Assets:\u{1F600}",   // emoji (So)
            "Assets:\u{1F600}A",
            "Assets:\u{308}A", // combining diaeresis (Mn)
            "Assets:\u{b2}",   // superscript two (No)
            "Assets:\u{2160}", // Roman numeral one (Nl)
            "\u{e9}clair:A",   // lowercase root start
            "\u{663}ssets:A",  // digit root start
        ] {
            assert!(lexes_whole(name), "{name} lexes as one account");
            assert!(!ok(name), "{name} is an invalid account name");
        }
        // rledger's deliberate extension (#816): caseless and titlecase
        // starts, which beancount rejects.
        assert!(ok("Assets:\u{65e5}\u{672c}")); // 日本 (Lo)
        assert!(ok("Assets:\u{1c5}")); // ǅ (Lt)
        // A BOM never starts an account (it stays its own error token).
        assert!(!lexes_whole("\u{feff}Assets:A"));
        assert!(lexes_whole("Assets:A\u{feff}"));
    }

    /// #2906: the strict check is beancount's `account.is_valid` (a full
    /// match of `ACCOUNT_RE`), plus the `\p{Lo}`/`\p{Lt}` start (#816).
    /// Verdicts checked against beancount 3.2.3 through the plugin and
    /// option sites that use it.
    #[test]
    fn is_valid_account_name_strict_matches_beancount_is_valid() {
        use super::{is_valid_account_name as ledger_ok, is_valid_account_name_strict as ok};
        for name in [
            "Assets:Cash",
            "Equity:\u{663}",       // ٣
            "Equity:CA:\u{663}x",   // ٣x
            "Assets:\u{dc}n\u{ef}", // Ünï
            "\u{c9}quit\u{e9}:A",   // Équité root
            "Assets:A-b:C",
            "\u{8cc7}\u{7522}:\u{73fe}\u{91d1}", // 資産:現金 (#816)
            "Equity:CA:\u{65e5}\u{672c}",        // 日本 (#816)
        ] {
            assert!(ok(name), "{name}");
            assert!(ledger_ok(name), "{name}: strict implies the ledger rule");
        }
        // Valid ledger accounts that beancount's `account.is_valid` rejects.
        for name in [
            "Equity:CA:\u{e9}",    // é starts a later component
            "Equity:CA:\u{1F600}", // emoji starts a later component
            "Equity:C\u{1F600}",   // emoji inside
            "Assets:Conv:\u{1F600}",
            "Assets:Rounding:\u{e9}clair",
            "A\u{1F600}:X", // a root outside [\p{L}\p{Nd}-]
        ] {
            assert!(ledger_ok(name), "{name} is a valid ledger account");
            assert!(!ok(name), "{name} fails account.is_valid");
        }
        for name in ["Assets:\u{e9}clair", "Assets:A_b", "Assets", "1A:B"] {
            assert!(!ok(name), "{name}");
        }
    }
}
