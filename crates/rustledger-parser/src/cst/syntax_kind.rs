//! `SyntaxKind`: every kind of token or node that can appear in the
//! Beancount CST.
//!
//! Design notes (from the round-1 architecture review of the
//! parallel-crate attempt that preceded this in-place migration):
//!
//! - **No discriminant stability commitment.** Phase 2+ may reorder,
//!   group, or rename freely. There are no committed serialized forms
//!   to keep stable. Reservations are antipatterns.
//! - **Safe u16 conversion via `num_enum::TryFromPrimitive`** instead
//!   of a hand-rolled match table. Adding a new variant is a single
//!   line; the derive enforces parity.
//! - **`is_token` via `matches!` over the actual token variants**, not
//!   a boundary trick on discriminants. A future variant inserted
//!   anywhere is classified correctly.

use num_enum::TryFromPrimitive;

/// Every kind of token or node that can appear in a Beancount CST.
///
/// Tokens carry source bytes; nodes are containers. The Logos lexer
/// produces a stream of tokens; the structured parser (phase 2+) wraps
/// runs of those tokens in nodes.
#[allow(non_camel_case_types)]
// Variant naming follows the rust-analyzer / rowan convention
// (SCREAMING_SNAKE_CASE). Variants without dedicated rustdoc are
// 1:1 mirrors of `logos_lexer::Token` (keywords, punctuation) and
// are documented at the parent enum + lossless_tokens::map_kind.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, TryFromPrimitive)]
#[repr(u16)]
#[non_exhaustive]
pub enum SyntaxKind {
    // ---- Trivia tokens ---------------------------------------------------
    /// 3-byte UTF-8 BOM at the very start of a file. Synthesized by
    /// the CST builder; the Logos lexer never sees BOM bytes because
    /// `bom::strip_leading` runs first.
    BOM,
    /// Horizontal whitespace `[ \t]+`.
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

    // ---- Literal tokens --------------------------------------------------
    /// `YYYY-MM-DD` or `YYYY/M/D`.
    DATE,
    /// Integer or decimal literal.
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
    /// Single-character flag introducing a transaction.
    FLAG,
    /// `TRUE` / `True` / `true`.
    BOOL_TRUE,
    /// `FALSE` / `False` / `false`.
    BOOL_FALSE,
    /// `NULL`.
    NULL_KW,

    // ---- Keyword tokens --------------------------------------------------
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

    // ---- Punctuation tokens ---------------------------------------------
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
    /// into `COMMENT` by the lexer post-processing pass).
    HASH,

    // ---- Error token -----------------------------------------------------
    /// Bytes the lexer could not classify. Preserved in the CST for
    /// round-trip and diagnostics.
    ERROR_TOKEN,

    // ---- Node kinds ------------------------------------------------------
    //
    // Structural node kinds are added at the moment they're first
    // needed. Phase 1 emitted only `SOURCE_FILE` (plus `ERROR_NODE`
    // reserved for phase 2's structured recovery). Phase 2.0 adds
    // `DIRECTIVE` because the trivia-policy regression tests need a
    // wrapper to demonstrate which directive owns which trivia.
    // Phase 2.1 will introduce specific directive kinds
    // (`TRANSACTION`, `OPEN_DIRECTIVE`, ...) alongside `DIRECTIVE`,
    // which remains as the umbrella kind for error-recovery
    // wrappers and any structural test reusable across kinds.
    // `#[non_exhaustive]` + `num_enum`'s derive make new variants
    // safe to add without ABI concerns.
    //
    // **Variant order is observable.** The corpus baseline
    // (`tests/cst_baseline.rs`) hashes `(kind as u16)` per token
    // for every file in the 714-file corpus. APPEND only; reordering
    // invalidates every committed manifest entry in one go and the
    // resulting diff is unreadable. If you must reorder, regenerate
    // the manifest in a SEPARATE commit from any parser change so
    // the diff stays reviewable.
    /// Root node — every byte of the file is reachable under this node.
    SOURCE_FILE,

    /// Generic error-recovery wrapper. Phase 1 doesn't emit this
    /// (lexer errors surface as `ERROR_TOKEN` leaves), but phase 2's
    /// structured parser will wrap partial-directive fragments in
    /// these. Kept here so the kind is available without a follow-up
    /// PR adding it — error recovery is in scope for any parser that
    /// promises to keep going past bad input.
    ERROR_NODE,

    /// Generic structural-directive wrapper. Phase 2.0 introduces it
    /// solely as a regression-test target for the trivia attachment
    /// policy (see `cst::trivia`). Phase 2.1 adds specific kinds
    /// alongside (`TRANSACTION`, `OPEN_DIRECTIVE`, `CLOSE_DIRECTIVE`,
    /// `BALANCE_DIRECTIVE`, ...) when the structured parser starts
    /// emitting them; `DIRECTIVE` remains as (a) the umbrella kind
    /// for error-recovery wrappers around partial-directive
    /// fragments, and (b) the test target for any structural
    /// regression that's the same shape across all directive kinds.
    /// The trivia policy applies UNIFORMLY to every specific kind,
    /// so phase 2.1's tests can use any of them interchangeably.
    DIRECTIVE,
}

impl SyntaxKind {
    /// Returns true if this kind is a leaf token (carries source bytes
    /// directly) rather than a parent node. Uses explicit `matches!`
    /// over the token variants so a future variant inserted anywhere
    /// in the enum is classified correctly.
    #[must_use]
    pub const fn is_token(self) -> bool {
        matches!(
            self,
            Self::BOM
                | Self::WHITESPACE
                | Self::NEWLINE
                | Self::COMMENT
                | Self::PERCENT_COMMENT
                | Self::SHEBANG
                | Self::EMACS_DIRECTIVE
                | Self::DATE
                | Self::NUMBER
                | Self::STRING
                | Self::ACCOUNT
                | Self::CURRENCY
                | Self::TAG
                | Self::LINK
                | Self::META_KEY
                | Self::FLAG
                | Self::BOOL_TRUE
                | Self::BOOL_FALSE
                | Self::NULL_KW
                | Self::TXN_KW
                | Self::BALANCE_KW
                | Self::OPEN_KW
                | Self::CLOSE_KW
                | Self::COMMODITY_KW
                | Self::PAD_KW
                | Self::EVENT_KW
                | Self::QUERY_KW
                | Self::NOTE_KW
                | Self::DOCUMENT_KW
                | Self::PRICE_KW
                | Self::CUSTOM_KW
                | Self::OPTION_KW
                | Self::INCLUDE_KW
                | Self::PLUGIN_KW
                | Self::PUSHTAG_KW
                | Self::POPTAG_KW
                | Self::PUSHMETA_KW
                | Self::POPMETA_KW
                | Self::PENDING_KW
                | Self::L_BRACE
                | Self::R_BRACE
                | Self::L_DOUBLE_BRACE
                | Self::R_DOUBLE_BRACE
                | Self::L_BRACE_HASH
                | Self::L_PAREN
                | Self::R_PAREN
                | Self::AT
                | Self::AT_AT
                | Self::COLON
                | Self::COMMA
                | Self::TILDE
                | Self::PIPE
                | Self::PLUS
                | Self::MINUS
                | Self::STAR
                | Self::SLASH
                | Self::HASH
                | Self::ERROR_TOKEN
        )
    }

    /// Returns true if this kind is trivia (whitespace, newline, BOM,
    /// or a comment variant). Trivia is byte-significant but
    /// semantically uninteresting; typed AST methods skip it.
    /// `ERROR_TOKEN` is NOT trivia: errors must surface.
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
        )
    }
}

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

/// Tag enum for `rowan::Language`. Zero variants — only used as a
/// type-level marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BeancountLanguage {}

impl rowan::Language for BeancountLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        // Defensive: fall back to ERROR_NODE on unknown discriminants
        // rather than panic. Phase 2.0 added the `DIRECTIVE` variant
        // and phase 2.1 will add more; any cross-version GreenNode
        // bytes (LSP cache, incremental persistence, sidecar tooling
        // reading our trees) seen by an older binary would otherwise
        // panic deep inside rowan's tree walk, which is unrecoverable
        // and a hard footgun. Returning `ERROR_NODE` surfaces the
        // skew at the consumer's `kind()` check instead.
        SyntaxKind::try_from(raw.0).unwrap_or(SyntaxKind::ERROR_NODE)
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

/// `rowan::SyntaxNode` specialized to `BeancountLanguage`.
pub type SyntaxNode = rowan::SyntaxNode<BeancountLanguage>;
/// `rowan::SyntaxToken` specialized to `BeancountLanguage`.
pub type SyntaxToken = rowan::SyntaxToken<BeancountLanguage>;
/// `rowan::SyntaxElement` (token-or-node) specialized to `BeancountLanguage`.
pub type SyntaxElement = rowan::SyntaxElement<BeancountLanguage>;

#[cfg(test)]
mod tests {
    use super::*;

    /// `is_token` and "is a node" are complementary: every variant is
    /// exactly one of token or node. A future variant added in the
    /// wrong category (or forgotten in either `matches!` list) would
    /// fail this property.
    #[test]
    fn nodes_are_not_tokens() {
        let node_kinds = [
            SyntaxKind::SOURCE_FILE,
            SyntaxKind::ERROR_NODE,
            SyntaxKind::DIRECTIVE,
        ];
        for kind in node_kinds {
            assert!(
                !kind.is_token(),
                "{kind:?} is a node but is_token() returns true",
            );
        }
    }

    /// Closed-form exhaustiveness check that catches the failure
    /// mode the two hand-maintained lists (`nodes_are_not_tokens`
    /// and `tokens_are_tokens`) miss in isolation: a future variant
    /// added to the enum but forgotten in `is_token`'s `matches!` arm
    /// AND in both hand-maintained test lists.
    ///
    /// We enumerate every valid discriminant via the `num_enum`
    /// `try_from` derive — the same surface `kind_from_raw` uses —
    /// then count how many fall into each category, and compare to
    /// the documented node list. If the counts disagree, a variant
    /// was added without updating the test scaffolding.
    #[test]
    fn every_kind_partitions_token_xor_node() {
        // Search a generous discriminant range. `SyntaxKind` is
        // small (~60 variants in phase 2.0); 256 is comfortable
        // headroom for phase 2.1+ growth.
        let all_kinds: Vec<SyntaxKind> = (0u16..256)
            .filter_map(|d| SyntaxKind::try_from(d).ok())
            .collect();

        // Sanity: we found something (catches a bug where
        // try_from is broken for ALL discriminants).
        assert!(
            !all_kinds.is_empty(),
            "SyntaxKind::try_from rejected every discriminant 0..256",
        );

        // The documented node kinds — must be kept in sync with
        // the `// ---- Node kinds ----` section of the enum above.
        // The exhaustive iteration catches any drift.
        let documented_nodes = [
            SyntaxKind::SOURCE_FILE,
            SyntaxKind::ERROR_NODE,
            SyntaxKind::DIRECTIVE,
        ];
        let observed_nodes: Vec<SyntaxKind> = all_kinds
            .iter()
            .copied()
            .filter(|k| !k.is_token())
            .collect();

        assert_eq!(
            observed_nodes.len(),
            documented_nodes.len(),
            "is_token() says there are {} node kinds but the \
             documented list has {}: observed={observed_nodes:?}, \
             documented={documented_nodes:?}. A new SyntaxKind \
             variant was added without updating is_token's matches! \
             arm AND the documented_nodes list in this test.",
            observed_nodes.len(),
            documented_nodes.len(),
        );
        for kind in documented_nodes {
            assert!(
                observed_nodes.contains(&kind),
                "{kind:?} is documented as a node but is_token() \
                 returns true for it",
            );
        }
    }

    /// Inverse of `nodes_are_not_tokens`: every token kind must satisfy
    /// `is_token()`. Catches a future variant added to the enum but
    /// forgotten in the `matches!` arm of `is_token`, which would
    /// silently misclassify at runtime while passing the
    /// `nodes_are_not_tokens` test.
    #[test]
    fn tokens_are_tokens() {
        let token_kinds = [
            // Trivia
            SyntaxKind::BOM,
            SyntaxKind::WHITESPACE,
            SyntaxKind::NEWLINE,
            SyntaxKind::COMMENT,
            SyntaxKind::PERCENT_COMMENT,
            SyntaxKind::SHEBANG,
            SyntaxKind::EMACS_DIRECTIVE,
            // Literals
            SyntaxKind::DATE,
            SyntaxKind::NUMBER,
            SyntaxKind::STRING,
            SyntaxKind::ACCOUNT,
            SyntaxKind::CURRENCY,
            SyntaxKind::TAG,
            SyntaxKind::LINK,
            SyntaxKind::META_KEY,
            SyntaxKind::FLAG,
            SyntaxKind::BOOL_TRUE,
            SyntaxKind::BOOL_FALSE,
            SyntaxKind::NULL_KW,
            // Keywords
            SyntaxKind::TXN_KW,
            SyntaxKind::BALANCE_KW,
            SyntaxKind::OPEN_KW,
            SyntaxKind::CLOSE_KW,
            SyntaxKind::COMMODITY_KW,
            SyntaxKind::PAD_KW,
            SyntaxKind::EVENT_KW,
            SyntaxKind::QUERY_KW,
            SyntaxKind::NOTE_KW,
            SyntaxKind::DOCUMENT_KW,
            SyntaxKind::PRICE_KW,
            SyntaxKind::CUSTOM_KW,
            SyntaxKind::OPTION_KW,
            SyntaxKind::INCLUDE_KW,
            SyntaxKind::PLUGIN_KW,
            SyntaxKind::PUSHTAG_KW,
            SyntaxKind::POPTAG_KW,
            SyntaxKind::PUSHMETA_KW,
            SyntaxKind::POPMETA_KW,
            SyntaxKind::PENDING_KW,
            // Punctuation
            SyntaxKind::L_BRACE,
            SyntaxKind::R_BRACE,
            SyntaxKind::L_DOUBLE_BRACE,
            SyntaxKind::R_DOUBLE_BRACE,
            SyntaxKind::L_BRACE_HASH,
            SyntaxKind::L_PAREN,
            SyntaxKind::R_PAREN,
            SyntaxKind::AT,
            SyntaxKind::AT_AT,
            SyntaxKind::COLON,
            SyntaxKind::COMMA,
            SyntaxKind::TILDE,
            SyntaxKind::PIPE,
            SyntaxKind::PLUS,
            SyntaxKind::MINUS,
            SyntaxKind::STAR,
            SyntaxKind::SLASH,
            SyntaxKind::HASH,
            // Error
            SyntaxKind::ERROR_TOKEN,
        ];
        for kind in token_kinds {
            assert!(
                kind.is_token(),
                "{kind:?} is a token but is_token() returns false — \
                 likely missing from the matches! arm in is_token",
            );
        }
    }

    #[test]
    fn is_trivia_excludes_error_token() {
        // ERROR_TOKEN is byte-significant but NOT trivia: it represents
        // bytes the lexer couldn't classify, and downstream consumers
        // need to surface them rather than skip them.
        assert!(!SyntaxKind::ERROR_TOKEN.is_trivia());
        assert!(SyntaxKind::ERROR_TOKEN.is_token());
    }

    #[test]
    fn rowan_language_round_trip() {
        // num_enum::TryFromPrimitive ensures the conversion is sound
        // for every defined discriminant. Spot-check a representative
        // sample including the boundaries.
        for kind in [
            SyntaxKind::BOM,
            SyntaxKind::WHITESPACE,
            SyntaxKind::HASH,
            SyntaxKind::ERROR_TOKEN,
            SyntaxKind::SOURCE_FILE,
            SyntaxKind::ERROR_NODE,
        ] {
            let raw: rowan::SyntaxKind = kind.into();
            let back = <BeancountLanguage as rowan::Language>::kind_from_raw(raw);
            assert_eq!(kind, back);
        }
    }
}
