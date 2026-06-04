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

pub mod lossless_tokens;
pub mod parser;
pub mod syntax_kind;

pub use lossless_tokens::lossless_kind_tokens;
pub use parser::parse_flat;
pub use syntax_kind::{BeancountLanguage, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};
