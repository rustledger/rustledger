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
//! Phase 1 emits a flat tree. Phase 2.0 pins the policy that phase
//! 2.1+ parsers will follow when wrapping token runs in structural
//! nodes. The full spec lives in the `trivia` submodule; the short
//! version:
//!
//! - **Leading attaches forward.** A blank line between two
//!   directives belongs to the SECOND directive.
//! - **EOF is the exception.** Trivia after the last content token
//!   attaches to the PRECEDING directive (nothing follows).
//! - **`SOURCE_FILE` is the parent of last resort.** Trivia before
//!   the first content token stays under `SOURCE_FILE`.
//!
//! Phase 1's `parse_flat` is policy-neutral (flat tree). Phase 2.1
//! calls [`classify_trivia`] when deciding directive boundaries; see
//! [`TriviaAttachment`] for the per-token classification it returns.

mod lossless_tokens;
mod parser;
mod syntax_kind;
mod trivia;

pub use lossless_tokens::lossless_kind_tokens;
pub use parser::parse_flat;
pub use syntax_kind::{BeancountLanguage, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};
pub use trivia::{TriviaAttachment, classify_trivia};
