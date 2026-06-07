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

/// Re-export of rowan's `SyntaxText` — a rope view over a
/// `SyntaxNode`'s text without allocation. Returned by
/// [`ErrorNode::text`] so consumers don't need a direct
/// `rowan` dependency.
pub use rowan::SyntaxText;

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

    /// The raw token text (borrowed from the green tree, zero
    /// allocation). Tokens are always contiguous, so a `&str`
    /// slice is well-defined.
    fn text(&self) -> &str {
        self.syntax().text()
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
    /// Borrowed from the green tree (zero allocation).
    pub fn text_unquoted(&self) -> Option<&str> {
        let raw = self.text();
        let bytes = raw.as_bytes();
        if bytes.len() < 2 || bytes[0] != b'"' || bytes[bytes.len() - 1] != b'"' {
            return None;
        }
        Some(&raw[1..raw.len() - 1])
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
    /// Key name with the trailing `:` stripped. Borrowed from the
    /// green tree (zero allocation).
    pub fn text_without_colon(&self) -> &str {
        let raw = self.text();
        raw.strip_suffix(':').unwrap_or(raw)
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

// ---- Heterogeneous flag/sign token wrappers --------------------
//
// These wrap a SyntaxToken whose kind is one of several
// possibilities (a transaction flag may be STAR, PENDING_KW, FLAG
// letter, HASH, TXN_KW, or single-char CURRENCY). We deliberately
// do NOT implement AstToken for them: AstToken::can_cast is
// kind-only, and the CURRENCY case needs a length check (only
// single-character CURRENCY counts as a ticker-letter flag).
// Inherent cast() runs the full check.
//
// Downstream code that needs exhaustive matching should use the
// `kind()` method paired with the dedicated `*FlagKind` enum
// returned by `classify()` (or `Sign::classify()`), which is
// pinned to the same variant set as `cast`.

/// Exhaustive classification of a [`TransactionFlag`] token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TransactionFlagKind {
    /// `*` token.
    Star,
    /// `!` (the `PENDING_KW` token).
    Pending,
    /// Single-letter `FLAG` token (e.g. `P` from `posti P`).
    Letter,
    /// `#` token.
    Hash,
    /// `txn` keyword.
    Txn,
    /// Single-character `CURRENCY` token used as the
    /// ticker-letter flag.
    CurrencyLetter,
}

/// Typed wrapper for the transaction-header flag token.
///
/// May be `STAR` (`*`), `PENDING_KW` (`!`), `FLAG` (letter),
/// `HASH` (`#`), `TXN_KW` (`txn`), or single-character `CURRENCY`
/// (ticker-letter flag, e.g. `T`). Use [`Self::classify`] for
/// exhaustive `match` ergonomics, or the `is_*` predicates for
/// boolean checks.
///
/// **Note**: [`Self::cast`] is position-AGNOSTIC — it accepts any
/// token of a flag-eligible kind regardless of where it sits in
/// the tree. To get the leading flag of a transaction, use
/// [`Transaction::flag`] (which scopes the search to the
/// pre-content header region).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TransactionFlag {
    token: SyntaxToken,
    classification: TransactionFlagKind,
}

impl TransactionFlag {
    /// Wrap the token if its kind is a valid transaction flag.
    /// For `CURRENCY`, only single-character forms qualify.
    ///
    /// Single source of truth: this match also derives
    /// [`Self::classify`]'s result, so cast + classify cannot
    /// drift.
    pub fn cast(token: SyntaxToken) -> Option<Self> {
        let classification = match token.kind() {
            SyntaxKind::STAR => TransactionFlagKind::Star,
            SyntaxKind::PENDING_KW => TransactionFlagKind::Pending,
            SyntaxKind::FLAG => TransactionFlagKind::Letter,
            SyntaxKind::HASH => TransactionFlagKind::Hash,
            SyntaxKind::TXN_KW => TransactionFlagKind::Txn,
            SyntaxKind::CURRENCY if token.text().len() == 1 => TransactionFlagKind::CurrencyLetter,
            _ => return None,
        };
        Some(Self {
            token,
            classification,
        })
    }

    pub const fn syntax(&self) -> &SyntaxToken {
        &self.token
    }
    pub fn kind(&self) -> SyntaxKind {
        self.token.kind()
    }
    pub fn text(&self) -> &str {
        self.token.text()
    }

    /// Exhaustive classification — pair with a `match` for
    /// compiler-checked coverage of every variant. Cached at
    /// `cast()` time; no runtime panic risk.
    pub const fn classify(&self) -> TransactionFlagKind {
        self.classification
    }

    pub const fn is_star(&self) -> bool {
        matches!(self.classification, TransactionFlagKind::Star)
    }
    pub const fn is_pending(&self) -> bool {
        matches!(self.classification, TransactionFlagKind::Pending)
    }
    pub const fn is_hash(&self) -> bool {
        matches!(self.classification, TransactionFlagKind::Hash)
    }
    pub const fn is_txn(&self) -> bool {
        matches!(self.classification, TransactionFlagKind::Txn)
    }
    pub const fn is_letter_flag(&self) -> bool {
        matches!(self.classification, TransactionFlagKind::Letter)
    }
    pub const fn is_currency_letter(&self) -> bool {
        matches!(self.classification, TransactionFlagKind::CurrencyLetter)
    }
}

/// Exhaustive classification of a [`PostingFlag`] token.
/// Same as [`TransactionFlagKind`] minus `Txn` (postings cannot
/// carry the `txn` keyword).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PostingFlagKind {
    Star,
    Pending,
    Letter,
    Hash,
    CurrencyLetter,
}

/// Typed wrapper for a posting-line flag token. Same as
/// [`TransactionFlag`] minus the `TXN_KW` variant (postings can't
/// carry the `txn` keyword). Use [`Self::classify`] for
/// exhaustive `match` ergonomics.
///
/// **Note**: [`Self::cast`] is position-AGNOSTIC. To get the
/// leading flag of a posting, use [`Posting::flag`] (which
/// scopes the search to the pre-ACCOUNT region of the posting).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PostingFlag {
    token: SyntaxToken,
    classification: PostingFlagKind,
}

impl PostingFlag {
    /// Single source of truth for cast + classify — drift impossible.
    pub fn cast(token: SyntaxToken) -> Option<Self> {
        let classification = match token.kind() {
            SyntaxKind::STAR => PostingFlagKind::Star,
            SyntaxKind::PENDING_KW => PostingFlagKind::Pending,
            SyntaxKind::FLAG => PostingFlagKind::Letter,
            SyntaxKind::HASH => PostingFlagKind::Hash,
            SyntaxKind::CURRENCY if token.text().len() == 1 => PostingFlagKind::CurrencyLetter,
            _ => return None,
        };
        Some(Self {
            token,
            classification,
        })
    }

    pub const fn syntax(&self) -> &SyntaxToken {
        &self.token
    }
    pub fn kind(&self) -> SyntaxKind {
        self.token.kind()
    }
    pub fn text(&self) -> &str {
        self.token.text()
    }

    /// Exhaustive classification — cached at `cast()` time;
    /// no runtime panic risk.
    pub const fn classify(&self) -> PostingFlagKind {
        self.classification
    }

    pub const fn is_star(&self) -> bool {
        matches!(self.classification, PostingFlagKind::Star)
    }
    pub const fn is_pending(&self) -> bool {
        matches!(self.classification, PostingFlagKind::Pending)
    }
    pub const fn is_hash(&self) -> bool {
        matches!(self.classification, PostingFlagKind::Hash)
    }
    pub const fn is_letter_flag(&self) -> bool {
        matches!(self.classification, PostingFlagKind::Letter)
    }
    pub const fn is_currency_letter(&self) -> bool {
        matches!(self.classification, PostingFlagKind::CurrencyLetter)
    }
}

/// Typed wrapper for an amount sign token (`PLUS` or `MINUS`).
///
/// `Sign::cast` is a position-AGNOSTIC kind check: it accepts ANY
/// `PLUS` or `MINUS` token, including operator-position signs
/// inside arithmetic (e.g., the `-` in `10 + -5 USD`). To get the
/// LEADING sign of an `Amount`, use [`Amount::sign`] which scopes
/// to the first non-whitespace token of `AMOUNT`. Calling
/// `Sign::cast` on an arbitrary token does not imply the token
/// occupies the leading-sign position.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sign(SyntaxToken);

impl Sign {
    pub fn cast(token: SyntaxToken) -> Option<Self> {
        matches!(token.kind(), SyntaxKind::PLUS | SyntaxKind::MINUS).then_some(Self(token))
    }
    pub const fn syntax(&self) -> &SyntaxToken {
        &self.0
    }
    pub fn kind(&self) -> SyntaxKind {
        self.0.kind()
    }
    pub fn text(&self) -> &str {
        self.0.text()
    }
    pub fn is_plus(&self) -> bool {
        self.kind() == SyntaxKind::PLUS
    }
    pub fn is_minus(&self) -> bool {
        self.kind() == SyntaxKind::MINUS
    }
}

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

// Sum-type Directive enum + AstNode impl + per-variant struct
// declarations, all derived from a single variant list. The
// macro is the single source of truth for "what directives
// exist": adding a new directive requires editing exactly one
// line. Drift between any of {can_cast, cast, syntax, per-variant
// struct decl, per-variant AstNode impl} is structurally
// impossible.
//
// Per-variant accessor methods (date(), account(), etc.) stay
// in separate `impl SomeDirective { ... }` blocks below.
macro_rules! directive_enum {
    ($($(#[$variant_meta:meta])* $variant:ident($struct:ident, $kind:ident)),* $(,)?) => {
        // Per-variant struct + AstNode impl, formerly emitted via
        // `ast_node!` invocations. Folded into directive_enum! so
        // the variant list is the only source of truth.
        $(
            $(#[$variant_meta])*
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct $struct(SyntaxNode);

            impl AstNode for $struct {
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
        )*

        /// Sum type over every recognized top-level directive wrapper.
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub enum Directive {
            $($variant($struct),)*
        }

        impl AstNode for Directive {
            fn can_cast(kind: SyntaxKind) -> bool {
                matches!(kind, $(SyntaxKind::$kind)|*)
            }

            fn cast(node: SyntaxNode) -> Option<Self> {
                Some(match node.kind() {
                    $(SyntaxKind::$kind => Self::$variant($struct(node)),)*
                    _ => return None,
                })
            }

            fn syntax(&self) -> &SyntaxNode {
                match self {
                    $(Self::$variant(d) => d.syntax(),)*
                }
            }
        }
    };
}

directive_enum!(
    /// `DATE open ACCOUNT [CURRENCY[,CURRENCY]*] ["BOOKING"]`.
    Open(OpenDirective, OPEN_DIRECTIVE),
    /// `DATE close ACCOUNT`.
    Close(CloseDirective, CLOSE_DIRECTIVE),
    /// `DATE balance ACCOUNT AMOUNT_TOKENS`. Amount stays flat
    /// (phase 2.2c scopes AMOUNT wrapping to POSTING only); walk
    /// `number()` and `currency()` to read it.
    Balance(BalanceDirective, BALANCE_DIRECTIVE),
    /// `DATE pad ACCOUNT_TARGET ACCOUNT_SOURCE`.
    Pad(PadDirective, PAD_DIRECTIVE),
    /// `DATE event "TYPE" "VALUE"`.
    Event(EventDirective, EVENT_DIRECTIVE),
    /// `DATE query "NAME" "QUERY"`.
    Query(QueryDirective, QUERY_DIRECTIVE),
    /// `DATE note ACCOUNT "TEXT"`.
    Note(NoteDirective, NOTE_DIRECTIVE),
    /// `DATE document ACCOUNT "PATH"`.
    Document(DocumentDirective, DOCUMENT_DIRECTIVE),
    /// `DATE price CURRENCY NUMBER CURRENCY`.
    Price(PriceDirective, PRICE_DIRECTIVE),
    /// `DATE commodity CURRENCY`.
    Commodity(CommodityDirective, COMMODITY_DIRECTIVE),
    /// `pushtag #TAG`.
    Pushtag(PushtagDirective, PUSHTAG_DIRECTIVE),
    /// `poptag #TAG`.
    Poptag(PoptagDirective, POPTAG_DIRECTIVE),
    /// `pushmeta KEY: VALUE`.
    Pushmeta(PushmetaDirective, PUSHMETA_DIRECTIVE),
    /// `popmeta KEY:`.
    Popmeta(PopmetaDirective, POPMETA_DIRECTIVE),
    /// `option "KEY" "VALUE"`.
    Option(OptionDirective, OPTION_DIRECTIVE),
    /// `include "PATH"`.
    Include(IncludeDirective, INCLUDE_DIRECTIVE),
    /// `plugin "MODULE" ["CONFIG"]`.
    Plugin(PluginDirective, PLUGIN_DIRECTIVE),
    /// `DATE custom "TYPE" values...`. Heterogeneous value list
    /// stays flat (phase 2.3); walk the raw token sequence
    /// via `syntax().children_with_tokens()`.
    Custom(CustomDirective, CUSTOM_DIRECTIVE),
    /// `DATE FLAG ["PAYEE"] "NARRATION" #TAG... ^LINK...`
    /// followed by indented `POSTING` lines and `META_ENTRY`
    /// sub-lines.
    Transaction(Transaction, TRANSACTION),
);

impl Directive {
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
    /// The raw bytes of the malformed region as a [`SyntaxText`]
    /// rope view. Zero allocation; use `.to_string()` on the
    /// result if you need an owned `String`, or `format!` /
    /// `Display` for direct output.
    #[must_use]
    pub fn text(&self) -> SyntaxText {
        self.syntax().text()
    }
}

// ---- 10 dated single-line directives (PR 2.1a) -----------------
//
// The 19 directive struct declarations + AstNode impls are
// generated by the `directive_enum!` macro invocation above.
// Per-variant accessor methods live in the `impl` blocks below.

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

impl CloseDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn account(&self) -> Option<Account> {
        first_token(self.syntax(), SyntaxKind::ACCOUNT).and_then(Account::cast)
    }
}

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

impl CommodityDirective {
    pub fn date(&self) -> Option<Date> {
        first_token(self.syntax(), SyntaxKind::DATE).and_then(Date::cast)
    }
    pub fn currency(&self) -> Option<CurrencyName> {
        first_token(self.syntax(), SyntaxKind::CURRENCY).and_then(CurrencyName::cast)
    }
}

// ---- 4 standalone-keyword directives (PR 2.1a) -----------------

impl PushtagDirective {
    pub fn tag(&self) -> Option<Tag> {
        first_token(self.syntax(), SyntaxKind::TAG).and_then(Tag::cast)
    }
}

impl PoptagDirective {
    pub fn tag(&self) -> Option<Tag> {
        first_token(self.syntax(), SyntaxKind::TAG).and_then(Tag::cast)
    }
}

impl PushmetaDirective {
    pub fn key(&self) -> Option<MetaKey> {
        first_token(self.syntax(), SyntaxKind::META_KEY).and_then(MetaKey::cast)
    }
}

impl PopmetaDirective {
    pub fn key(&self) -> Option<MetaKey> {
        first_token(self.syntax(), SyntaxKind::META_KEY).and_then(MetaKey::cast)
    }
}

// ---- 4 edge directives (PR 2.3) --------------------------------

impl OptionDirective {
    pub fn key(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
    pub fn value(&self) -> Option<StringLit> {
        nth_token(self.syntax(), SyntaxKind::STRING, 1).and_then(StringLit::cast)
    }
}

impl IncludeDirective {
    pub fn path(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
}

impl PluginDirective {
    pub fn module(&self) -> Option<StringLit> {
        first_token(self.syntax(), SyntaxKind::STRING).and_then(StringLit::cast)
    }
    pub fn config(&self) -> Option<StringLit> {
        nth_token(self.syntax(), SyntaxKind::STRING, 1).and_then(StringLit::cast)
    }
}

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

impl Transaction {
    /// Direct-child tokens of TRANSACTION in the header region
    /// only: leading trivia (whitespace, newlines, comments
    /// attached as inter-directive leading trivia per the
    /// Directive-Terminator Rule) is skipped, then tokens are
    /// collected until the first NEWLINE that terminates the
    /// header line. Body content (`POSTING` / `META_ENTRY` nodes;
    /// flat tokens emitted by `emit_transaction_body`'s catch-all
    /// for malformed indented lines) is excluded.
    fn header_tokens(&self) -> impl Iterator<Item = SyntaxToken> + '_ {
        self.syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            // Skip leading trivia (blank-line newlines, top-of-
            // directive whitespace, leading comments). The first
            // non-trivia token marks the start of the header.
            //
            // Comment-trivia covers all four comment kinds — ledger-
            // style `%` comments and org-mode `#!`/`#+` lines are
            // attached as leading trivia by the Directive-Terminator
            // Rule the same way `;` comments are, so a transaction
            // preceded by any of them must skip them too. BOM stays
            // OUT of the skip set: a mid-file BOM in a transaction
            // header is a corruption to surface, not trivia.
            .skip_while(|t| {
                matches!(
                    t.kind(),
                    SyntaxKind::WHITESPACE
                        | SyntaxKind::NEWLINE
                        | SyntaxKind::COMMENT
                        | SyntaxKind::PERCENT_COMMENT
                        | SyntaxKind::SHEBANG
                        | SyntaxKind::EMACS_DIRECTIVE
                )
            })
            .take_while(|t| t.kind() != SyntaxKind::NEWLINE)
    }

    /// Header tokens BEFORE the first STRING/TAG/LINK — i.e., the
    /// flag-position region (between DATE and the first header
    /// content token). Used by [`Self::flag`] to scope its search.
    fn flag_region_tokens(&self) -> impl Iterator<Item = SyntaxToken> + '_ {
        self.header_tokens().take_while(|t| {
            !matches!(
                t.kind(),
                SyntaxKind::STRING | SyntaxKind::TAG | SyntaxKind::LINK
            )
        })
    }

    pub fn date(&self) -> Option<Date> {
        // DATE is in the header, so first_token over the whole node
        // is fine — but for symmetry, scope to header_tokens.
        self.header_tokens()
            .find(|t| t.kind() == SyntaxKind::DATE)
            .and_then(Date::cast)
    }

    /// Transaction flag token. May be `STAR` (`*`), `PENDING_KW`
    /// (`!`), `FLAG` letter, `HASH` (`#`), `TXN_KW`
    /// (the `txn` keyword), single-char `CURRENCY` (ticker-letter
    /// flag), or absent (implied via a leading `STRING`
    /// payee/narration).
    ///
    /// Scoped to the flag-position region (between `DATE` and the
    /// first `STRING`/`TAG`/`LINK`) so a stray trailing
    /// single-char `CURRENCY` after the narration is NOT
    /// misclassified as a flag.
    pub fn flag(&self) -> Option<TransactionFlag> {
        self.flag_region_tokens().find_map(TransactionFlag::cast)
    }

    /// All `STRING` tokens in the header, in source order.
    ///
    /// Scoped to the header (tokens before the terminating
    /// `NEWLINE`), so `STRING` tokens emitted into TRANSACTION by
    /// `emit_transaction_body`'s catch-all for malformed indented
    /// body lines are excluded.
    ///
    /// The 2-string convention (`"payee" "narration"`) is the
    /// canonical form; [`Self::payee`] and [`Self::narration`]
    /// follow it strictly. For 3+ strings (malformed but
    /// losslessly parsed), use this method to surface every
    /// header string.
    pub fn strings(&self) -> impl Iterator<Item = StringLit> + '_ {
        self.header_tokens()
            .filter(|t| t.kind() == SyntaxKind::STRING)
            .filter_map(StringLit::cast)
    }

    /// The payee string, if a separate payee + narration pair is
    /// present. Returns `Some(first)` ONLY when exactly two
    /// header `STRING` tokens appear (the canonical
    /// `"payee" "narration"` shape). With 0, 1, or 3+ strings
    /// the convention is ambiguous and this returns `None` —
    /// use [`Self::strings`] for lossless access.
    pub fn payee(&self) -> Option<StringLit> {
        // Take up to 3 to disambiguate 2 from 3+ without
        // allocating the whole sequence.
        let mut iter = self.strings();
        let first = iter.next()?;
        let second = iter.next()?;
        if iter.next().is_some() {
            None
        } else {
            // Exactly 2 strings; first is payee.
            let _ = second;
            Some(first)
        }
    }

    /// The narration string. Returns `Some(only)` for a single
    /// header string and `Some(last)` for the 2-string
    /// `"payee" "narration"` form. Returns `None` for 0 or 3+
    /// strings — use [`Self::strings`] for lossless access on
    /// malformed headers.
    pub fn narration(&self) -> Option<StringLit> {
        let mut iter = self.strings();
        let first = iter.next()?;
        let second = iter.next();
        let third = iter.next();
        match (second, third) {
            (None, _) => Some(first),
            (Some(s2), None) => Some(s2),
            _ => None,
        }
    }

    /// All `#TAG` tokens attached to the transaction header.
    /// Scoped to the header region (excludes body tokens).
    pub fn tags(&self) -> impl Iterator<Item = Tag> + '_ {
        self.header_tokens()
            .filter(|t| t.kind() == SyntaxKind::TAG)
            .filter_map(Tag::cast)
    }

    /// All `^LINK` tokens attached to the transaction header.
    /// Scoped to the header region (excludes body tokens).
    pub fn links(&self) -> impl Iterator<Item = Link> + '_ {
        self.header_tokens()
            .filter(|t| t.kind() == SyntaxKind::LINK)
            .filter_map(Link::cast)
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
    /// Posting flag (optional). Same kinds as
    /// [`TransactionFlag`] minus `TXN_KW` — indicates whether
    /// THIS posting is pending, marked, etc.
    pub fn flag(&self) -> Option<PostingFlag> {
        // Walk children up to the ACCOUNT; the first non-whitespace
        // token is the flag iff it's a valid PostingFlag kind.
        for el in self.syntax().children_with_tokens() {
            if let rowan::NodeOrToken::Token(t) = el {
                match t.kind() {
                    SyntaxKind::WHITESPACE => {}
                    SyntaxKind::ACCOUNT => return None,
                    _ => return PostingFlag::cast(t),
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
    /// sign or if the leading non-whitespace token is something
    /// else (e.g., `L_PAREN`, `NUMBER`, `CURRENCY`).
    pub fn sign(&self) -> Option<Sign> {
        let first = self
            .syntax()
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| t.kind() != SyntaxKind::WHITESPACE)?;
        Sign::cast(first)
    }

    /// First `NUMBER` child token (the leading operand). For an
    /// arithmetic expression like `10+5 USD`, this is `10`; for
    /// a bare CURRENCY amount this is `None`.
    pub fn number(&self) -> Option<Number> {
        first_token(self.syntax(), SyntaxKind::NUMBER).and_then(Number::cast)
    }

    /// The trailing currency at paren-depth 0.
    ///
    /// For `100 USD`, `100USD`, `(1+2) USD`: returns the trailing
    /// `USD`. For bare currency-only `AMOUNT(CURRENCY)`: returns
    /// the same token. For malformed `(1 USD)` (CURRENCY inside
    /// parens, no outer trailing currency): returns `None`. For
    /// unclosed `(1 USD\n` or stray-closer `1 USD)` (unbalanced
    /// parens): returns `None`, refusing to surface a possibly
    /// paren-internal currency.
    ///
    /// Single forward pass with paren-depth tracking; no
    /// allocation. `emit_amount_operand` keeps paren contents
    /// flat under AMOUNT (no `PAREN_EXPR` sub-node), so depth
    /// tracking is the only structural disambiguator.
    pub fn currency(&self) -> Option<CurrencyName> {
        let mut depth: i32 = 0;
        let mut last_at_depth_0: Option<SyntaxToken> = None;
        for el in self.syntax().children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            match t.kind() {
                SyntaxKind::L_PAREN => depth += 1,
                SyntaxKind::R_PAREN => depth -= 1,
                SyntaxKind::CURRENCY if depth == 0 => last_at_depth_0 = Some(t),
                _ => {}
            }
        }
        // Unbalanced parens (unclosed or stray closer): refuse to
        // surface a currency rather than guess.
        if depth != 0 {
            return None;
        }
        last_at_depth_0.and_then(CurrencyName::cast)
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

    /// Returns true iff the opener is immediately followed by a
    /// `*` merge marker (e.g., `{*}` or `{* 500 USD}`). A STAR
    /// elsewhere in the cost spec is the multiplication operator
    /// (e.g., `{500 * 2 USD}`), NOT a merge marker; position
    /// matters.
    #[must_use]
    pub fn is_merge(&self) -> bool {
        let mut past_opener = false;
        for el in self.syntax().children_with_tokens() {
            if let rowan::NodeOrToken::Token(t) = el {
                match t.kind() {
                    SyntaxKind::L_BRACE | SyntaxKind::L_DOUBLE_BRACE | SyntaxKind::L_BRACE_HASH => {
                        past_opener = true;
                    }
                    SyntaxKind::WHITESPACE if past_opener => {}
                    SyntaxKind::STAR if past_opener => return true,
                    _ if past_opener => return false,
                    _ => {}
                }
            }
        }
        false
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
