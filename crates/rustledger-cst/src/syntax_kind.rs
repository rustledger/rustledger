//! Lossless syntax-tree kinds for the Beancount CST.
//!
//! Phase 1 of the parser-CST migration (#1262). Every byte of source
//! is reachable from the tree: content tokens (Date, String, Account,
//! ...) carry their own bytes, and structural trivia (whitespace,
//! newlines, comments, BOM) lives as first-class tokens too. The
//! formatter and any future refactor / rename / structural-search
//! consumer walks the tree without needing access to the original
//! source.
//!
//! # Phase 1 scope
//!
//! Phase 1 emits a FLAT CST — every token is a direct child of a
//! single [`SyntaxKind::SOURCE_FILE`] node. Phase 2 will introduce
//! the structural node kinds (`DIRECTIVE`, `POSTING`, `AMOUNT_NODE`,
//! ...) and the parser logic that nests tokens under them. The
//! placeholders for those node kinds are pre-allocated below so the
//! phase 2 PR is purely additive (no `SyntaxKind` discriminant
//! renumbering — which would invalidate any serialized form, see
//! decision §3.11 of #1262 about wire stability).
//!
//! # Discriminant stability
//!
//! `SyntaxKind` discriminants ARE part of the public ABI: `rowan`
//! stores them as a `u16` inside every green token / node. Reordering
//! the enum, removing a variant, or inserting one mid-stream all
//! change the integer mapping. For phase 1 the discriminants are
//! freely renumberable because nothing is yet persisted; once any
//! consumer caches `GreenNode`s on disk (or a wire format ships) the
//! discriminants become a stability surface that future PRs must
//! preserve.

#![allow(non_camel_case_types)]
// Variant naming follows rust-analyzer / rowan conventions (SCREAMING_SNAKE_CASE).
// Clippy's standard "type names use CamelCase" lint flags every variant; the
// `allow` is the project-wide pattern for this style.
#![allow(missing_docs)]
// Most variants are self-documenting one-to-one mirrors of the Logos
// lexer's `Token` enum (keywords like `OPEN_KW`, punctuation like
// `L_BRACE`); the doc on the parent enum and the [`crate::lossless_tokens`]
// mapping function are the canonical references. Variants that DO need
// commentary (trivia, structural-node reservations) carry their own
// doc comments below.

/// Every kind of node or token that can appear in a Beancount CST.
///
/// The variants split into three groups:
///
/// - **Tokens** (`*` or content-named) are LEAF nodes that carry source
///   bytes.
/// - **Trivia tokens** (`WHITESPACE`, `NEWLINE`, `COMMENT`, ...) are
///   semantically uninteresting but byte-significant. The typed AST in
///   phase 2 will skip them; the formatter walks them.
/// - **Node kinds** (`SOURCE_FILE`, `DIRECTIVE`, ...) are non-leaf
///   nodes. Phase 1 only uses `SOURCE_FILE`; the rest are pre-
///   allocated for phase 2.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u16)]
pub enum SyntaxKind {
    // --- Trivia tokens -----------------------------------------------------
    /// 3-byte UTF-8 byte-order mark at the very start of a file.
    /// Stripped pre-lexer in `rustledger_parser::bom`; phase 1 synthesizes
    /// a token for it so the round-trip stays byte-identical.
    BOM,
    /// Horizontal whitespace (`[ \t]+`). The existing Logos lexer
    /// silently drops these between content tokens via
    /// `#[logos(skip ...)]`; phase 1's lossless adapter recovers them
    /// from the byte gaps between consecutive token spans.
    WHITESPACE,
    /// `\r?\n`.
    NEWLINE,
    /// `; ...` to end-of-line.
    COMMENT,
    /// `% ...` to end-of-line (ledger-compat).
    PERCENT_COMMENT,
    /// `#! ...` (org-mode shebang at top of file).
    SHEBANG,
    /// `#+ ...` (org-mode property line).
    EMACS_DIRECTIVE,
    /// Leading whitespace at line start when a content token follows
    /// (1-2 spaces). Span covers the whitespace bytes.
    INDENT,
    /// Leading whitespace at line start, 3+ spaces (posting-metadata
    /// indentation level).
    DEEP_INDENT,

    // --- Literal tokens ----------------------------------------------------
    /// `YYYY-MM-DD` or `YYYY/M/D`.
    DATE,
    /// Integer or decimal literal (may carry thousands commas).
    NUMBER,
    /// Double-quoted string with escape sequences.
    STRING,
    /// Account name (`Assets:Bank:Checking`).
    ACCOUNT,
    /// Currency symbol (`USD`, `/GAINS`).
    CURRENCY,
    /// `#tag`.
    TAG,
    /// `^link`.
    LINK,
    /// `meta-key:` at line start.
    META_KEY,
    /// Single-character flag token (`*`, `!`, etc. introducing a transaction).
    FLAG,
    /// `TRUE` / `True` / `true`.
    BOOL_TRUE,
    /// `FALSE` / `False` / `false`.
    BOOL_FALSE,
    /// `NULL`.
    NULL_KW,

    // --- Keyword tokens ----------------------------------------------------
    TXN_KW,
    BALANCE_KW,
    OPEN_KW,
    CLOSE_KW,
    COMMODITY_KW,
    PAD_KW,
    EVENT_KW,
    QUERY_KW,
    NOTE_KW,
    DOCUMENT_KW,
    PRICE_KW,
    CUSTOM_KW,
    OPTION_KW,
    INCLUDE_KW,
    PLUGIN_KW,
    PUSHTAG_KW,
    POPTAG_KW,
    PUSHMETA_KW,
    POPMETA_KW,
    /// `P` pending flag.
    PENDING_KW,

    // --- Punctuation tokens ------------------------------------------------
    L_BRACE,
    R_BRACE,
    L_DOUBLE_BRACE,
    R_DOUBLE_BRACE,
    L_BRACE_HASH,
    L_PAREN,
    R_PAREN,
    AT,
    AT_AT,
    COLON,
    COMMA,
    TILDE,
    PIPE,
    PLUS,
    MINUS,
    STAR,
    SLASH,
    /// Bare `#` (cost-spec date separator; line-start `#` is folded
    /// into COMMENT by the lexer post-processing pass).
    HASH,

    // --- Error tokens ------------------------------------------------------
    /// Lexer error (invalid bytes preserved in span for diagnostics).
    ERROR_TOKEN,

    // --- Node kinds (non-leaf) ---------------------------------------------
    /// Root node — every byte of the file is reachable under this node.
    SOURCE_FILE,

    // The following node kinds are RESERVED for phase 2's structural
    // parser. They are not emitted by phase 1's flat parser. Listed
    // here so the discriminants stay stable when phase 2 starts using
    // them.
    DIRECTIVE,
    POSTING,
    POSTING_LIST,
    AMOUNT_NODE,
    COST_SPEC,
    PRICE_ANNOTATION,
    META_ENTRY,
    META_BLOCK,
    TAG_LINK_LIST,
    /// Generic structural error recovery node.
    ERROR_NODE,
}

impl SyntaxKind {
    /// Returns true if the kind is a leaf token (carries source bytes)
    /// rather than a parent node.
    #[must_use]
    pub const fn is_token(self) -> bool {
        // Discriminants for token-shaped kinds come strictly before
        // the SOURCE_FILE node-shaped boundary. Keep this in lock-step
        // with the enum order above.
        (self as u16) < (Self::SOURCE_FILE as u16)
    }

    /// Returns true if the kind is trivia (whitespace, newline,
    /// comment, BOM) that the typed AST in phase 2 will skip when
    /// walking the tree.
    #[must_use]
    pub const fn is_trivia(self) -> bool {
        matches!(
            self,
            Self::BOM
                | Self::WHITESPACE
                | Self::NEWLINE
                | Self::COMMENT
                | Self::PERCENT_COMMENT
                | Self::SHEBANG
                | Self::EMACS_DIRECTIVE
                | Self::INDENT
                | Self::DEEP_INDENT
        )
    }
}

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

/// The Beancount language tag for `rowan`. A zero-variant enum because
/// rowan only ever uses the type for its `Language` impl — no values
/// are ever constructed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BeancountLanguage {}

impl rowan::Language for BeancountLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        kind_from_raw(raw.0)
            .unwrap_or_else(|| panic!("rowan::SyntaxKind({}) is not a valid SyntaxKind", raw.0))
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

/// Safe u16 → `SyntaxKind` conversion. The workspace forbids `unsafe`
/// (per the `forbid-unsafe-code` invariant verified by the pre-push
/// hook), so the canonical rust-analyzer-style `transmute` isn't an
/// option. A match expression compiles to the same jump table at
/// optimization levels we care about.
///
/// Keep in sync with the [`SyntaxKind`] enum order. The test
/// `rowan_language_round_trip` exercises a representative sample, but
/// a missing arm would silently return `None` and surface as a panic
/// inside rowan if (and only if) a green tree carrying that
/// discriminant were ever decoded. Update this function AND
/// `is_token`'s SOURCE_FILE-boundary check together when adding kinds.
#[allow(clippy::too_many_lines)]
const fn kind_from_raw(raw: u16) -> Option<SyntaxKind> {
    let kind = match raw {
        0 => SyntaxKind::BOM,
        1 => SyntaxKind::WHITESPACE,
        2 => SyntaxKind::NEWLINE,
        3 => SyntaxKind::COMMENT,
        4 => SyntaxKind::PERCENT_COMMENT,
        5 => SyntaxKind::SHEBANG,
        6 => SyntaxKind::EMACS_DIRECTIVE,
        7 => SyntaxKind::INDENT,
        8 => SyntaxKind::DEEP_INDENT,
        9 => SyntaxKind::DATE,
        10 => SyntaxKind::NUMBER,
        11 => SyntaxKind::STRING,
        12 => SyntaxKind::ACCOUNT,
        13 => SyntaxKind::CURRENCY,
        14 => SyntaxKind::TAG,
        15 => SyntaxKind::LINK,
        16 => SyntaxKind::META_KEY,
        17 => SyntaxKind::FLAG,
        18 => SyntaxKind::BOOL_TRUE,
        19 => SyntaxKind::BOOL_FALSE,
        20 => SyntaxKind::NULL_KW,
        21 => SyntaxKind::TXN_KW,
        22 => SyntaxKind::BALANCE_KW,
        23 => SyntaxKind::OPEN_KW,
        24 => SyntaxKind::CLOSE_KW,
        25 => SyntaxKind::COMMODITY_KW,
        26 => SyntaxKind::PAD_KW,
        27 => SyntaxKind::EVENT_KW,
        28 => SyntaxKind::QUERY_KW,
        29 => SyntaxKind::NOTE_KW,
        30 => SyntaxKind::DOCUMENT_KW,
        31 => SyntaxKind::PRICE_KW,
        32 => SyntaxKind::CUSTOM_KW,
        33 => SyntaxKind::OPTION_KW,
        34 => SyntaxKind::INCLUDE_KW,
        35 => SyntaxKind::PLUGIN_KW,
        36 => SyntaxKind::PUSHTAG_KW,
        37 => SyntaxKind::POPTAG_KW,
        38 => SyntaxKind::PUSHMETA_KW,
        39 => SyntaxKind::POPMETA_KW,
        40 => SyntaxKind::PENDING_KW,
        41 => SyntaxKind::L_BRACE,
        42 => SyntaxKind::R_BRACE,
        43 => SyntaxKind::L_DOUBLE_BRACE,
        44 => SyntaxKind::R_DOUBLE_BRACE,
        45 => SyntaxKind::L_BRACE_HASH,
        46 => SyntaxKind::L_PAREN,
        47 => SyntaxKind::R_PAREN,
        48 => SyntaxKind::AT,
        49 => SyntaxKind::AT_AT,
        50 => SyntaxKind::COLON,
        51 => SyntaxKind::COMMA,
        52 => SyntaxKind::TILDE,
        53 => SyntaxKind::PIPE,
        54 => SyntaxKind::PLUS,
        55 => SyntaxKind::MINUS,
        56 => SyntaxKind::STAR,
        57 => SyntaxKind::SLASH,
        58 => SyntaxKind::HASH,
        59 => SyntaxKind::ERROR_TOKEN,
        60 => SyntaxKind::SOURCE_FILE,
        61 => SyntaxKind::DIRECTIVE,
        62 => SyntaxKind::POSTING,
        63 => SyntaxKind::POSTING_LIST,
        64 => SyntaxKind::AMOUNT_NODE,
        65 => SyntaxKind::COST_SPEC,
        66 => SyntaxKind::PRICE_ANNOTATION,
        67 => SyntaxKind::META_ENTRY,
        68 => SyntaxKind::META_BLOCK,
        69 => SyntaxKind::TAG_LINK_LIST,
        70 => SyntaxKind::ERROR_NODE,
        _ => return None,
    };
    Some(kind)
}

/// Type alias for rowan's `SyntaxNode` specialized to `BeancountLanguage`.
pub type SyntaxNode = rowan::SyntaxNode<BeancountLanguage>;
/// Type alias for rowan's `SyntaxToken` specialized to `BeancountLanguage`.
pub type SyntaxToken = rowan::SyntaxToken<BeancountLanguage>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_token_partitions_correctly() {
        // Spot-check the boundary: WHITESPACE is a token, SOURCE_FILE
        // is not, DIRECTIVE (reserved for phase 2) is not.
        assert!(SyntaxKind::WHITESPACE.is_token());
        assert!(SyntaxKind::DATE.is_token());
        assert!(SyntaxKind::ERROR_TOKEN.is_token());
        assert!(!SyntaxKind::SOURCE_FILE.is_token());
        assert!(!SyntaxKind::DIRECTIVE.is_token());
        assert!(!SyntaxKind::ERROR_NODE.is_token());
    }

    #[test]
    fn is_trivia_covers_byte_significant_but_uninteresting_kinds() {
        assert!(SyntaxKind::WHITESPACE.is_trivia());
        assert!(SyntaxKind::NEWLINE.is_trivia());
        assert!(SyntaxKind::COMMENT.is_trivia());
        assert!(SyntaxKind::BOM.is_trivia());
        assert!(!SyntaxKind::DATE.is_trivia());
        assert!(!SyntaxKind::SOURCE_FILE.is_trivia());
    }

    #[test]
    fn rowan_language_round_trip() {
        for kind in [
            SyntaxKind::WHITESPACE,
            SyntaxKind::DATE,
            SyntaxKind::SOURCE_FILE,
            SyntaxKind::ERROR_NODE,
        ] {
            let raw: rowan::SyntaxKind = kind.into();
            let back = <BeancountLanguage as rowan::Language>::kind_from_raw(raw);
            assert_eq!(kind, back);
        }
    }

    /// Exhaustive parity: every variant from BOM (discriminant 0) up
    /// to and including `ERROR_NODE` survives a round-trip through
    /// `kind_from_raw`. Drift between the enum order and the match
    /// table is the most likely failure mode when adding new kinds
    /// (e.g., for phase 2's structural nodes); this test catches it
    /// before any green tree carrying the new discriminant exists.
    #[test]
    fn every_discriminant_round_trips() {
        // The highest valid discriminant is ERROR_NODE. We walk 0..=N
        // and verify each maps back to the kind whose `as u16` equals
        // the raw value.
        let max = SyntaxKind::ERROR_NODE as u16;
        for raw in 0..=max {
            let kind = kind_from_raw(raw).unwrap_or_else(|| {
                panic!("kind_from_raw({raw}) returned None but raw is within ERROR_NODE bound")
            });
            assert_eq!(
                kind as u16, raw,
                "kind_from_raw({raw}) returned {kind:?} (discriminant {})",
                kind as u16,
            );
        }
        // And the boundary: anything above is rejected.
        assert!(
            kind_from_raw(max + 1).is_none(),
            "kind_from_raw({}) should reject out-of-range",
            max + 1,
        );
    }
}
