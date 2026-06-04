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
//! # Deferred design: trivia attachment policy (phase 2)
//!
//! Phase 1 emits a flat tree, so every token (content AND trivia) is
//! a direct child of `SOURCE_FILE`. When phase 2 introduces structural
//! nodes (`DIRECTIVE`, `POSTING`, ...) the question becomes: does the
//! newline between two directives attach to the preceding directive,
//! to the next one, or stay a `SOURCE_FILE`-level child?
//!
//! Phase 2's first PR must pick a policy and pin it with a regression
//! test. The default recommendation (matching rust-analyzer's
//! convention) is: leading trivia attaches to the FOLLOWING non-trivia
//! node; trailing trivia attaches to the PRECEDING node only on the
//! last item before EOF, where there is nothing following. That makes
//! "node enter" the natural visiting point for any consumer that wants
//! to skip trivia (the typed AST surface, validators, the formatter's
//! header walk) while keeping the formatter's full-tree walk lossless.
//!
//! No policy is enforced in phase 1 — the flat tree is policy-neutral.

mod lossless_tokens;
mod parser;
mod syntax_kind;

pub use lossless_tokens::lossless_kind_tokens;
pub use parser::parse_flat;
pub use syntax_kind::{BeancountLanguage, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};
