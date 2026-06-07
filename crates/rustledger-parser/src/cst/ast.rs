//! Typed AST wrappers over the lossless CST.
//!
//! Phase 3 of #1262. The CST (phase 1-2) preserves every byte of
//! the source as an untyped tree of `SyntaxKind` nodes and tokens.
//! This module adds a thin typed layer on top: newtype wrappers
//! around `SyntaxNode` / `SyntaxToken` with `kind()`-gated
//! constructors (`cast`) and structural accessors (`date()`,
//! `account()`, `amount()`, etc.).
//!
//! Two traits anchor the surface:
//!
//! - [`AstNode`]: typed wrapper around a `SyntaxNode`. Each wrapper
//!   pins its expected `SyntaxKind` via `can_cast` and offers
//!   accessors that walk direct children.
//! - [`AstToken`]: typed wrapper around a `SyntaxToken`. Provides
//!   `text()` for the raw bytes; specific token wrappers (`Date`,
//!   `Account`, `Number`, ...) can layer parsing on top.
//!
//! The wrappers are zero-cost — they store a `SyntaxNode` /
//! `SyntaxToken` by value and forward to it. Cloning is cheap
//! (rowan's nodes/tokens are `Arc`-backed). All accessors return
//! `Option<_>` because the CST is lossless: a malformed input
//! still produces a tree, just one with missing children.
//!
//! # Round-trip
//!
//! Every wrapper exposes `syntax()` returning the underlying
//! `SyntaxNode`/`SyntaxToken`, whose `text()` reproduces the
//! original bytes exactly. Typed-AST consumers that want to
//! modify the source can therefore navigate via accessors and
//! splice via raw text ranges.
#![allow(missing_docs)] // Accessors are self-documenting via function name + return type.

use crate::cst::syntax_kind::{SyntaxKind, SyntaxNode, SyntaxToken};

/// Typed wrapper around a `SyntaxNode` of a specific
/// `SyntaxKind`.
pub trait AstNode: Sized {
    /// Returns true iff `kind` is the wrapper's expected node
    /// kind. Used by `cast` and by enum dispatch.
    fn can_cast(kind: SyntaxKind) -> bool;

    /// Wrap `syntax` if its kind matches; otherwise `None`.
    fn cast(syntax: SyntaxNode) -> Option<Self>;

    /// The underlying CST node. `text()` reproduces the original
    /// bytes; `children()` / `children_with_tokens()` walk the
    /// tree.
    fn syntax(&self) -> &SyntaxNode;
}

/// Typed wrapper around a `SyntaxToken` of a specific
/// `SyntaxKind`. Like [`AstNode`] but for leaf tokens.
pub trait AstToken: Sized {
    fn can_cast(kind: SyntaxKind) -> bool;
    fn cast(token: SyntaxToken) -> Option<Self>;
    fn syntax(&self) -> &SyntaxToken;

    /// The raw token text (bytes from the source).
    fn text(&self) -> String {
        self.syntax().text().to_string()
    }
}

// ---- Helpers --------------------------------------------------

/// First direct-child token of `kind` under `node`, or `None`.
fn first_token(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    node.children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .find(|t| t.kind() == kind)
}

/// Nth (0-indexed) direct-child token of `kind` under `node`.
fn nth_token(node: &SyntaxNode, kind: SyntaxKind, n: usize) -> Option<SyntaxToken> {
    node.children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| t.kind() == kind)
        .nth(n)
}

/// All direct-child tokens of `kind` under `node`.
fn tokens_of_kind(node: &SyntaxNode, kind: SyntaxKind) -> impl Iterator<Item = SyntaxToken> + '_ {
    node.children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(move |t| t.kind() == kind)
}

/// First direct-child node castable to `N`.
fn first_child<N: AstNode>(node: &SyntaxNode) -> Option<N> {
    node.children().find_map(N::cast)
}

/// All direct-child nodes castable to `N`.
fn children<'a, N: AstNode + 'a>(node: &'a SyntaxNode) -> impl Iterator<Item = N> + 'a {
    node.children().filter_map(N::cast)
}

// ---- Macros ---------------------------------------------------

macro_rules! ast_node {
    ($(#[$meta:meta])* $name:ident, $kind:ident) => {
        $(#[$meta])*
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $name(SyntaxNode);

        impl AstNode for $name {
            fn can_cast(kind: SyntaxKind) -> bool {
                kind == SyntaxKind::$kind
            }
            fn cast(syntax: SyntaxNode) -> Option<Self> {
                Self::can_cast(syntax.kind()).then_some(Self(syntax))
            }
            fn syntax(&self) -> &SyntaxNode {
                &self.0
            }
        }
    };
}

macro_rules! ast_token {
    ($(#[$meta:meta])* $name:ident, $kind:ident) => {
        $(#[$meta])*
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $name(SyntaxToken);

        impl AstToken for $name {
            fn can_cast(kind: SyntaxKind) -> bool {
                kind == SyntaxKind::$kind
            }
            fn cast(token: SyntaxToken) -> Option<Self> {
                Self::can_cast(token.kind()).then_some(Self(token))
            }
            fn syntax(&self) -> &SyntaxToken {
                &self.0
            }
        }
    };
}

// ---- Token wrappers -------------------------------------------

ast_token!(
    /// `DATE` token (e.g., `2024-01-15`).
    Date, DATE
);
ast_token!(
    /// `ACCOUNT` token (e.g., `Assets:Cash`).
    Account, ACCOUNT
);
ast_token!(
    /// `CURRENCY` token (e.g., `USD`).
    CurrencyName, CURRENCY
);
ast_token!(
    /// `STRING` literal (e.g., `"Coffee"`). `text()` includes the
    /// surrounding quotes; use `text_unquoted()` for the content.
    StringLit, STRING
);

impl StringLit {
    /// String content with surrounding `"` stripped. Returns
    /// `None` if the raw text isn't a well-formed quoted string.
    pub fn text_unquoted(&self) -> Option<String> {
        let raw = self.text();
        let bytes = raw.as_bytes();
        if bytes.len() < 2 || bytes[0] != b'"' || bytes[bytes.len() - 1] != b'"' {
            return None;
        }
        Some(raw[1..raw.len() - 1].to_string())
    }
}

ast_token!(
    /// `NUMBER` token (e.g., `100.00`).
    Number, NUMBER
);
ast_token!(
    /// `META_KEY` token (e.g., `note:`). Note the trailing colon
    /// is part of the token; use `text_without_colon()` to strip it.
    MetaKey, META_KEY
);

impl MetaKey {
    /// Key name with the trailing `:` stripped.
    pub fn text_without_colon(&self) -> String {
        let raw = self.text();
        raw.strip_suffix(':').unwrap_or(&raw).to_string()
    }
}

ast_token!(
    /// `TAG` token (e.g., `#trip`).
    Tag, TAG
);
ast_token!(
    /// `LINK` token (e.g., `^expense-123`).
    Link, LINK
);
ast_token!(
    /// `BOOL_TRUE` token literal.
    BoolTrue, BOOL_TRUE
);
ast_token!(
    /// `BOOL_FALSE` token literal.
    BoolFalse, BOOL_FALSE
);

// ---- Source file root + Directive enum ------------------------

ast_node!(
    /// Root of a parsed Beancount file. `SourceFile::parse(src)` is
    /// the typed-AST entry point — it wraps `parse_structured`.
    SourceFile, SOURCE_FILE
);

impl SourceFile {
    /// Parse `source` into a typed source-file tree.
    #[must_use]
    pub fn parse(source: &str) -> Self {
        let node = crate::cst::parser::parse_structured(source);
        Self::cast(node).expect("parse_structured always returns a SOURCE_FILE")
    }

    /// All recognized directives, in source order.
    pub fn directives(&self) -> impl Iterator<Item = Directive> + '_ {
        self.syntax().children().filter_map(Directive::cast)
    }

    /// All `ERROR_NODE` wrappers (unrecognized / malformed lines).
    pub fn errors(&self) -> impl Iterator<Item = ErrorNode> + '_ {
        self.syntax().children().filter_map(ErrorNode::cast)
    }
}

/// Sum type over every recognized top-level directive wrapper.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Directive {
    Open(OpenDirective),
    Close(CloseDirective),
    Balance(BalanceDirective),
    Pad(PadDirective),
    Event(EventDirective),
    Query(QueryDirective),
    Note(NoteDirective),
    Document(DocumentDirective),
    Price(PriceDirective),
    Commodity(CommodityDirective),
    Pushtag(PushtagDirective),
    Poptag(PoptagDirective),
    Pushmeta(PushmetaDirective),
    Popmeta(PopmetaDirective),
    Option(OptionDirective),
    Include(IncludeDirective),
    Plugin(PluginDirective),
    Custom(CustomDirective),
    Transaction(Transaction),
}

impl Directive {
    /// Cast a `SyntaxNode` to a typed directive if it's a
    /// recognized directive kind.
    #[must_use]
    pub fn cast(node: SyntaxNode) -> Option<Self> {
        Some(match node.kind() {
            SyntaxKind::OPEN_DIRECTIVE => Self::Open(OpenDirective(node)),
            SyntaxKind::CLOSE_DIRECTIVE => Self::Close(CloseDirective(node)),
            SyntaxKind::BALANCE_DIRECTIVE => Self::Balance(BalanceDirective(node)),
            SyntaxKind::PAD_DIRECTIVE => Self::Pad(PadDirective(node)),
            SyntaxKind::EVENT_DIRECTIVE => Self::Event(EventDirective(node)),
            SyntaxKind::QUERY_DIRECTIVE => Self::Query(QueryDirective(node)),
            SyntaxKind::NOTE_DIRECTIVE => Self::Note(NoteDirective(node)),
            SyntaxKind::DOCUMENT_DIRECTIVE => Self::Document(DocumentDirective(node)),
            SyntaxKind::PRICE_DIRECTIVE => Self::Price(PriceDirective(node)),
            SyntaxKind::COMMODITY_DIRECTIVE => Self::Commodity(CommodityDirective(node)),
            SyntaxKind::PUSHTAG_DIRECTIVE => Self::Pushtag(PushtagDirective(node)),
            SyntaxKind::POPTAG_DIRECTIVE => Self::Poptag(PoptagDirective(node)),
            SyntaxKind::PUSHMETA_DIRECTIVE => Self::Pushmeta(PushmetaDirective(node)),
            SyntaxKind::POPMETA_DIRECTIVE => Self::Popmeta(PopmetaDirective(node)),
            SyntaxKind::OPTION_DIRECTIVE => Self::Option(OptionDirective(node)),
            SyntaxKind::INCLUDE_DIRECTIVE => Self::Include(IncludeDirective(node)),
            SyntaxKind::PLUGIN_DIRECTIVE => Self::Plugin(PluginDirective(node)),
            SyntaxKind::CUSTOM_DIRECTIVE => Self::Custom(CustomDirective(node)),
            SyntaxKind::TRANSACTION => Self::Transaction(Transaction(node)),
            _ => return None,
        })
    }

    /// The underlying `SyntaxNode` regardless of variant.
    #[must_use]
    pub fn syntax(&self) -> &SyntaxNode {
        match self {
            Self::Open(d) => d.syntax(),
            Self::Close(d) => d.syntax(),
            Self::Balance(d) => d.syntax(),
            Self::Pad(d) => d.syntax(),
            Self::Event(d) => d.syntax(),
            Self::Query(d) => d.syntax(),
            Self::Note(d) => d.syntax(),
            Self::Document(d) => d.syntax(),
            Self::Price(d) => d.syntax(),
            Self::Commodity(d) => d.syntax(),
            Self::Pushtag(d) => d.syntax(),
            Self::Poptag(d) => d.syntax(),
            Self::Pushmeta(d) => d.syntax(),
            Self::Popmeta(d) => d.syntax(),
            Self::Option(d) => d.syntax(),
            Self::Include(d) => d.syntax(),
            Self::Plugin(d) => d.syntax(),
            Self::Custom(d) => d.syntax(),
            Self::Transaction(d) => d.syntax(),
        }
    }

    /// Metadata sub-lines attached to this directive (phase 2.2a
    /// `META_ENTRY` wrapping). Every directive wrapper may carry
    /// indented metadata.
    pub fn meta_entries(&self) -> impl Iterator<Item = MetaEntry> + '_ {
        children(self.syntax())
    }
}

ast_node!(
    /// Wrapper for unrecognized / malformed top-level content
    /// (PR 2.4 `ERROR_NODE`). Typed-AST consumers can use this to
    /// surface error regions to users (e.g., LSP diagnostics).
    ErrorNode, ERROR_NODE
);

impl ErrorNode {
    /// The raw bytes of the malformed region.
    #[must_use]
    pub fn text(&self) -> String {
        self.syntax().text().to_string()
    }
}

// ---- 10 dated single-line directives (PR 2.1a) -----------------

ast_node!(
    /// `DATE open ACCOUNT [CURRENCY[,CURRENCY]*] ["BOOKING"]`.
    OpenDirective, OPEN_DIRECTIVE
);
impl OpenDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }
    /// Comma-separated currency constraint list (may be empty).
    pub fn currencies(&self) -> impl Iterator<Item = CurrencyName> + '_ {
        tokens_of_kind(self.syntax(), SyntaxKind::CURRENCY).filter_map(CurrencyName::cast)
    }
    /// Optional booking-method string (e.g., `"STRICT"`).
    pub fn booking_method(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `DATE close ACCOUNT`.
    CloseDirective, CLOSE_DIRECTIVE
);
impl CloseDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }
}

ast_node!(
    /// `DATE balance ACCOUNT AMOUNT_TOKENS`. Amount stays flat
    /// (phase 2.2c scopes AMOUNT wrapping to POSTING only) — walk
    /// `number()` and `currency()` to read it.
    BalanceDirective, BALANCE_DIRECTIVE
);
impl BalanceDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }
    pub fn number(&self) -> Option<Number> {
        first_token(self.syntax(), SyntaxKind::NUMBER).and_then(Number::cast)
    }
    pub fn currency(&self) -> Option<CurrencyName> {
        first_token(self.syntax(), SyntaxKind::CURRENCY).and_then(CurrencyName::cast)
    }
}

ast_node!(
    /// `DATE pad ACCOUNT_TARGET ACCOUNT_SOURCE`.
    PadDirective, PAD_DIRECTIVE
);
impl PadDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn target_account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }
    pub fn source_account(&self) -> Option<Account> {
        nth_token(self.syntax(), SyntaxKind::ACCOUNT, 1).and_then(Account::cast)
    }
}

ast_node!(
    /// `DATE event "TYPE" "VALUE"`.
    EventDirective, EVENT_DIRECTIVE
);
impl EventDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn event_type(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
    pub fn value(&self) -> Option<StringLit> {
        nth_token(self.syntax(), SyntaxKind::STRING, 1).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `DATE query "NAME" "QUERY"`.
    QueryDirective, QUERY_DIRECTIVE
);
impl QueryDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn name(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
    pub fn query(&self) -> Option<StringLit> {
        nth_token(self.syntax(), SyntaxKind::STRING, 1).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `DATE note ACCOUNT "TEXT"`.
    NoteDirective, NOTE_DIRECTIVE
);
impl NoteDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }
    pub fn text(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `DATE document ACCOUNT "PATH"`.
    DocumentDirective, DOCUMENT_DIRECTIVE
);
impl DocumentDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }
    pub fn path(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `DATE price CURRENCY NUMBER CURRENCY`.
    PriceDirective, PRICE_DIRECTIVE
);
impl PriceDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn base_currency(&self) -> Option<CurrencyName> {
        first_token(self.syntax(), SyntaxKind::CURRENCY).and_then(CurrencyName::cast)
    }
    pub fn number(&self) -> Option<Number> {
        first_token(self.syntax(), SyntaxKind::NUMBER).and_then(Number::cast)
    }
    pub fn quote_currency(&self) -> Option<CurrencyName> {
        nth_token(self.syntax(), SyntaxKind::CURRENCY, 1).and_then(CurrencyName::cast)
    }
}

ast_node!(
    /// `DATE commodity CURRENCY`.
    CommodityDirective, COMMODITY_DIRECTIVE
);
impl CommodityDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn currency(&self) -> Option<CurrencyName> {
        first_token(self.syntax(), SyntaxKind::CURRENCY).and_then(CurrencyName::cast)
    }
}

// ---- 4 standalone-keyword directives (PR 2.1a) -----------------

ast_node!(
    /// `pushtag #TAG`.
    PushtagDirective, PUSHTAG_DIRECTIVE
);
impl PushtagDirective {
    pub fn tag(&self) -> Option<Tag> {
        first_token(self.syntax(), SyntaxKind::TAG).and_then(Tag::cast)
    }
}

ast_node!(
    /// `poptag #TAG`.
    PoptagDirective, POPTAG_DIRECTIVE
);
impl PoptagDirective {
    pub fn tag(&self) -> Option<Tag> {
        first_token(self.syntax(), SyntaxKind::TAG).and_then(Tag::cast)
    }
}

ast_node!(
    /// `pushmeta KEY: VALUE`.
    PushmetaDirective, PUSHMETA_DIRECTIVE
);
impl PushmetaDirective {
    pub fn key(&self) -> Option<MetaKey> {
        first_token(self.syntax(), SyntaxKind::META_KEY).and_then(MetaKey::cast)
    }
}

ast_node!(
    /// `popmeta KEY:`.
    PopmetaDirective, POPMETA_DIRECTIVE
);
impl PopmetaDirective {
    pub fn key(&self) -> Option<MetaKey> {
        first_token(self.syntax(), SyntaxKind::META_KEY).and_then(MetaKey::cast)
    }
}

// ---- 4 edge directives (PR 2.3) --------------------------------

ast_node!(
    /// `option "KEY" "VALUE"`.
    OptionDirective, OPTION_DIRECTIVE
);
impl OptionDirective {
    pub fn key(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
    pub fn value(&self) -> Option<StringLit> {
        nth_token(self.syntax(), SyntaxKind::STRING, 1).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `include "PATH"`.
    IncludeDirective, INCLUDE_DIRECTIVE
);
impl IncludeDirective {
    pub fn path(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `plugin "MODULE" ["CONFIG"]`.
    PluginDirective, PLUGIN_DIRECTIVE
);
impl PluginDirective {
    pub fn module(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
    pub fn config(&self) -> Option<StringLit> {
        nth_token(self.syntax(), SyntaxKind::STRING, 1).and_then(StringLit::cast)
    }
}

ast_node!(
    /// `DATE custom "TYPE" values...`. Heterogeneous value list
    /// stays flat (phase 2.3); walk `values()` for the raw token
    /// sequence.
    CustomDirective, CUSTOM_DIRECTIVE
);
impl CustomDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    /// The type-name string (always the first `STRING` after the
    /// `custom` keyword).
    pub fn custom_type(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
}

// ---- TRANSACTION + body sub-nodes ------------------------------

ast_node!(
    /// `DATE FLAG ["PAYEE"] "NARRATION" #TAG... ^LINK...`
    /// followed by indented `POSTING` lines and `META_ENTRY`
    /// sub-lines.
    Transaction, TRANSACTION
);

impl Transaction {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }

    /// Transaction flag token. May be `STAR` (`*`), `PENDING_KW`
    /// (`!`), `FLAG` letter, `HASH` (`#`), `TXN_KW`
    /// (the `txn` keyword), single-char `CURRENCY`, or absent
    /// (implied via a leading `STRING` payee/narration).
    pub fn flag(&self) -> Option<SyntaxToken> {
        self.syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| {
                matches!(
                    t.kind(),
                    SyntaxKind::STAR
                        | SyntaxKind::PENDING_KW
                        | SyntaxKind::FLAG
                        | SyntaxKind::HASH
                        | SyntaxKind::TXN_KW
                )
            })
    }

    /// The payee string, if a separate payee + narration pair is
    /// present. With two `STRING` children, the first is the
    /// payee. With only one `STRING`, the entire string is
    /// considered narration.
    pub fn payee(&self) -> Option<StringLit> {
        let strings: Vec<StringLit> = tokens_of_kind(self.syntax(), SyntaxKind::STRING)
            .filter_map(StringLit::cast)
            .collect();
        if strings.len() >= 2 {
            Some(strings.into_iter().next().unwrap())
        } else {
            None
        }
    }

    /// The narration string. The last `STRING` child of the
    /// header line (handles both the payee+narration and
    /// narration-only cases).
    pub fn narration(&self) -> Option<StringLit> {
        let mut strings: Vec<StringLit> = tokens_of_kind(self.syntax(), SyntaxKind::STRING)
            .filter_map(StringLit::cast)
            .collect();
        strings.pop()
    }

    /// All `#TAG` tokens attached to the transaction header.
    pub fn tags(&self) -> impl Iterator<Item = Tag> + '_ {
        tokens_of_kind(self.syntax(), SyntaxKind::TAG).filter_map(Tag::cast)
    }

    /// All `^LINK` tokens attached to the transaction header.
    pub fn links(&self) -> impl Iterator<Item = Link> + '_ {
        tokens_of_kind(self.syntax(), SyntaxKind::LINK).filter_map(Link::cast)
    }

    /// All `POSTING` sub-lines, in source order.
    pub fn postings(&self) -> impl Iterator<Item = Posting> + '_ {
        children(self.syntax())
    }

    /// Transaction-level `META_ENTRY` sub-lines (at the standard
    /// indent, NOT the deeper posting-attached metadata).
    pub fn meta_entries(&self) -> impl Iterator<Item = MetaEntry> + '_ {
        children(self.syntax())
    }
}

ast_node!(
    /// `WS [(FLAG | STAR | PENDING_KW | HASH | single-char CURRENCY) WS] ACCOUNT [AMOUNT] [COST_SPEC] [PRICE_ANNOTATION]`.
    Posting, POSTING
);

impl Posting {
    /// Posting flag (optional). Same kinds as `Transaction::flag`
    /// but indicates whether THIS posting is pending, etc.
    pub fn flag(&self) -> Option<SyntaxToken> {
        // Walk children up to the ACCOUNT; any flag-kind token
        // before ACCOUNT is the posting flag.
        for el in self.syntax().children_with_tokens() {
            if let rowan::NodeOrToken::Token(t) = el {
                match t.kind() {
                    SyntaxKind::WHITESPACE => {}
                    SyntaxKind::ACCOUNT => return None,
                    SyntaxKind::STAR
                    | SyntaxKind::PENDING_KW
                    | SyntaxKind::FLAG
                    | SyntaxKind::HASH => return Some(t),
                    SyntaxKind::CURRENCY if t.text().len() == 1 => return Some(t),
                    _ => return None,
                }
            }
        }
        None
    }

    pub fn account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }

    /// Units `AMOUNT` (optional — auto postings have none).
    pub fn amount(&self) -> Option<Amount> {
        first_child(self.syntax())
    }

    /// `COST_SPEC` annotation, if present.
    pub fn cost_spec(&self) -> Option<CostSpec> {
        first_child(self.syntax())
    }

    /// `PRICE_ANNOTATION`, if present.
    pub fn price_annotation(&self) -> Option<PriceAnnotation> {
        first_child(self.syntax())
    }

    /// Posting-attached metadata (strictly deeper-indent
    /// `META_ENTRY` sub-lines following the posting line).
    pub fn meta_entries(&self) -> impl Iterator<Item = MetaEntry> + '_ {
        children(self.syntax())
    }
}

// ---- AMOUNT / COST_SPEC / PRICE_ANNOTATION / META_ENTRY --------

ast_node!(
    /// Units amount: `[sign] (NUMBER | PAREN_EXPR) ([WS] op
    /// [WS] [sign] (NUMBER | PAREN_EXPR))* [WS CURRENCY]`, or a
    /// bare `CURRENCY`. Phase 2.4 extension supports arithmetic.
    Amount, AMOUNT
);

impl Amount {
    /// Sign token (`MINUS` or `PLUS`), if present as the FIRST
    /// non-whitespace child of AMOUNT. Returns `None` if no
    /// sign or if the sign is inside an arithmetic-expression
    /// inner operand.
    pub fn sign(&self) -> Option<SyntaxToken> {
        let first = self
            .syntax()
            .children_with_tokens()
            .find_map(rowan::NodeOrToken::into_token)?;
        matches!(first.kind(), SyntaxKind::MINUS | SyntaxKind::PLUS).then_some(first)
    }

    /// First `NUMBER` child token (the leading operand). For an
    /// arithmetic expression like `10+5 USD`, this is `10`; for
    /// a bare CURRENCY amount this is `None`.
    pub fn number(&self) -> Option<Number> {
        first_token(self.syntax(), SyntaxKind::NUMBER).and_then(Number::cast)
    }

    /// The trailing currency. For `100 USD` or `100USD` or
    /// `(1+2) USD`, this is `USD`. For bare currency-only
    /// `AMOUNT(CURRENCY)`, it's the same token.
    pub fn currency(&self) -> Option<CurrencyName> {
        // The currency is the LAST direct-child CURRENCY token
        // (a paren-expression interior may contain currency-shaped
        // tokens that we want to ignore for the typed accessor).
        tokens_of_kind(self.syntax(), SyntaxKind::CURRENCY)
            .last()
            .and_then(CurrencyName::cast)
    }

    /// Returns true iff the amount contains an arithmetic operator
    /// (`+`, `-` between operands, `*`, `/`) or a parenthesized
    /// sub-expression — useful for typed-AST consumers that need
    /// to defer to expression evaluation.
    #[must_use]
    pub fn is_arithmetic(&self) -> bool {
        let mut seen_first_operand = false;
        for el in self.syntax().children_with_tokens() {
            if let rowan::NodeOrToken::Token(t) = el {
                match t.kind() {
                    SyntaxKind::NUMBER => seen_first_operand = true,
                    SyntaxKind::L_PAREN | SyntaxKind::R_PAREN => return true,
                    SyntaxKind::STAR | SyntaxKind::SLASH => return true,
                    SyntaxKind::PLUS | SyntaxKind::MINUS if seen_first_operand => return true,
                    _ => {}
                }
            }
        }
        false
    }
}

ast_node!(
    /// Bracketed cost annotation: `{...}` (per-unit), `{#...}`
    /// (per-unit + total), or `{{...}}` (total-only). Contents
    /// stay flat (phase 2.2c); accessors scan the children.
    CostSpec, COST_SPEC
);

impl CostSpec {
    /// Returns true iff the opener is `{{` (total-cost form).
    #[must_use]
    pub fn is_total(&self) -> bool {
        first_token(self.syntax(), SyntaxKind::L_DOUBLE_BRACE).is_some()
    }

    /// Returns true iff the opener is `{#` (per-unit + total
    /// form).
    #[must_use]
    pub fn is_per_unit_plus_total(&self) -> bool {
        first_token(self.syntax(), SyntaxKind::L_BRACE_HASH).is_some()
    }

    /// Cost number (first NUMBER child token).
    pub fn number(&self) -> Option<Number> {
        first_token(self.syntax(), SyntaxKind::NUMBER).and_then(Number::cast)
    }

    /// Cost currency (first CURRENCY child token).
    pub fn currency(&self) -> Option<CurrencyName> {
        first_token(self.syntax(), SyntaxKind::CURRENCY).and_then(CurrencyName::cast)
    }

    /// Cost date (first DATE child token), if present.
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }

    /// Cost label (first STRING child token), if present.
    pub fn label(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }

    /// Returns true iff the cost spec contains a `*` merge marker.
    #[must_use]
    pub fn is_merge(&self) -> bool {
        first_token(self.syntax(), SyntaxKind::STAR).is_some()
    }
}

ast_node!(
    /// Price annotation: `AT [WS AMOUNT]` (per-unit) or
    /// `AT_AT [WS AMOUNT]` (total).
    PriceAnnotation, PRICE_ANNOTATION
);

impl PriceAnnotation {
    /// Returns true iff the opener is `@@` (total-price form).
    #[must_use]
    pub fn is_total(&self) -> bool {
        first_token(self.syntax(), SyntaxKind::AT_AT).is_some()
    }

    /// The price's inner `AMOUNT`, if present.
    pub fn amount(&self) -> Option<Amount> {
        first_child(self.syntax())
    }
}

ast_node!(
    /// Metadata sub-line: `WS META_KEY ... (NEWLINE | EOF)`.
    /// Key is the `META_KEY` token; value is the remaining flat
    /// content tokens. Use `key()` and `value_*()` accessors.
    MetaEntry, META_ENTRY
);

impl MetaEntry {
    pub fn key(&self) -> Option<MetaKey> {
        first_token(self.syntax(), SyntaxKind::META_KEY).and_then(MetaKey::cast)
    }

    /// Value as a typed STRING, if the value is a quoted string.
    pub fn value_string(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }

    /// Value as a NUMBER token, if the value is numeric.
    pub fn value_number(&self) -> Option<Number> {
        first_token(self.syntax(), SyntaxKind::NUMBER).and_then(Number::cast)
    }

    /// Value as a DATE token, if the value is a date literal.
    pub fn value_date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }

    /// Value as an ACCOUNT token.
    pub fn value_account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }

    /// Value as a CURRENCY token.
    pub fn value_currency(&self) -> Option<CurrencyName> {
        first_token(self.syntax(), SyntaxKind::CURRENCY).and_then(CurrencyName::cast)
    }

    /// Value as a boolean (true / false token).
    pub fn value_bool(&self) -> Option<bool> {
        for el in self.syntax().children_with_tokens() {
            if let rowan::NodeOrToken::Token(t) = el {
                match t.kind() {
                    SyntaxKind::BOOL_TRUE => return Some(true),
                    SyntaxKind::BOOL_FALSE => return Some(false),
                    _ => {}
                }
            }
        }
        None
    }
}
