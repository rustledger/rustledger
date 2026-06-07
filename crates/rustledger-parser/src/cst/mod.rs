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
//! that wrap token runs. Phase 2.0 pins **the
//! Directive-Terminator Rule**: every directive owns its content
//! tokens PLUS its terminating `NEWLINE`.
//!
//! Short version:
//!
//! - **Same-line trailing** trivia (whitespace + EOL comment
//!   before the terminator) lives INSIDE the directive.
//! - **Inter-directive leading** trivia (blank lines, mid-file
//!   comment blocks) lives INSIDE the NEXT directive.
//! - **File-leading** trivia (before the first content token) is
//!   a direct child of `SOURCE_FILE`.
//! - **File-trailing** trivia (after the file-final directive's
//!   terminator) is also a direct child of `SOURCE_FILE`.
//!
//! Fully symmetric: every directive has the same children shape
//! (optional leading + content + optional same-line trailing +
//! terminator `NEWLINE`). No EOF special case.
//!
//! Phase 2.0 ships NO production helper — the policy is enforced
//! via tree-shape regression tests in `cst::trivia` (private
//! submodule). Phase 2.1's structured parser writes its own
//! streaming, state-aware predicate that produces trees matching
//! those shapes. If the parser drifts, the regression tests fire.
//! See the `trivia` module rustdoc for the full spec, rationale,
//! and recursive-application notes for phase 2.1's grammar.

pub mod ast;
mod convert;
mod lossless_tokens;
mod parser;
mod syntax_kind;
mod trivia;

pub use convert::parse_via_cst;
pub use lossless_tokens::lossless_kind_tokens;
pub use parser::{parse_flat, parse_structured};
pub use syntax_kind::{BeancountLanguage, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};
