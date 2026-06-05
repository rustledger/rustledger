//! Lossless concrete syntax tree (CST) for Beancount.
//!
//! Phase 1 of the parser-CST migration tracked in #1262. Sits inside
//! `rustledger-parser` (no new crate) — phases 2-5 will move the
//! existing AST-style parser internals to delegate to this module
//! and eventually delete the old code paths.
//!
//! # Phase 1 surface
//!
//! - [`SyntaxKind`]: every token and node kind that can appear in the
//!   tree. `num_enum::TryFromPrimitive` for the u16 → enum conversion.
//! - [`BeancountLanguage`]: the rowan `Language` impl + type aliases
//!   ([`SyntaxNode`], [`SyntaxToken`], [`SyntaxElement`]).
//! - [`lossless_kind_tokens`]: drive the lossless lexer (`tokenize_lossless`)
//!   and recover the leading BOM byte-by-byte.
//! - [`parse_flat`]: produce a flat `SOURCE_FILE` tree that round-trips
//!   byte-identically against the source.
//!
//! # Trivia attachment policy (phase 2.0)
//!
//! Phase 1 emits a flat tree, where trivia attachment is a non-
//! question. Phase 2.1+ introduces structural nodes (`DIRECTIVE`,
//! then `POSTING` / `AMOUNT` / `COST_SPEC` / `META_ENTRY` / ...)
//! that wrap token runs. Phase 2.0 pins the rule for which
//! structural node owns which trivia token: **the Two-Line Rule**.
//!
//! Short version:
//!
//! - **Same-line trailing** trivia attaches to the PRECEDING
//!   directive. An inline `; EOL comment` after an account name
//!   trails its directive.
//! - **Line-crossing leading** trivia attaches to the FOLLOWING
//!   directive. The blank line between two directives leads the
//!   second one.
//! - **File-leading** trivia (before any content) attaches to
//!   `SOURCE_FILE` directly — copyright headers are file-level
//!   metadata, not part of the first directive.
//! - **EOF trailing** trivia (after the last content) has no
//!   following directive, so it stays with the file-final one.
//!
//! Phase 2.0 ships NO production helper for this — the policy is
//! enforced via tree-shape regression tests in `cst::trivia`
//! (private submodule). Phase 2.1's structured parser writes its
//! own streaming, state-aware predicate that produces trees
//! matching those shapes. If the parser drifts from the policy,
//! the regression tests fire. See the `trivia` module rustdoc for
//! the full spec and rationale.

mod lossless_tokens;
mod parser;
mod syntax_kind;
mod trivia;

pub use lossless_tokens::lossless_kind_tokens;
pub use parser::parse_flat;
pub use syntax_kind::{BeancountLanguage, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};
