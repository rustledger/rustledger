//! Lossless concrete syntax tree (CST) for Beancount.
//!
//! Phase 1 of the parser-CST migration tracked in #1262. This crate
//! provides:
//!
//! - [`SyntaxKind`]: every token and node kind in the Beancount grammar.
//! - [`SyntaxNode`] / [`SyntaxToken`]: `rowan` type aliases specialized
//!   to the Beancount language.
//! - [`lossless_tokens::lossless_tokens`]: trivia-preserving adapter
//!   over `rustledger_parser::logos_lexer::tokenize`.
//! - [`parse_flat`]: produce a flat `SOURCE_FILE` rowan tree whose
//!   text round-trips byte-identically with the input.
//!
//! Phase 2 will add structured node kinds (`DIRECTIVE`, `POSTING`,
//! `AMOUNT_NODE`, ...) and a parser that nests tokens under them. The
//! flat phase-1 tree is the foundation: byte-preservation is proved
//! against the full compatibility corpus, and phase 2's structured
//! parser can be developed in parallel against the same primitives.
//!
//! See #1262 for the full plan.

pub mod lossless_tokens;
pub mod parser;
pub mod syntax_kind;

pub use lossless_tokens::lossless_tokens;
pub use parser::parse_flat;
pub use syntax_kind::{BeancountLanguage, SyntaxKind, SyntaxNode, SyntaxToken};
