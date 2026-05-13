//! Pure operations on beancount directives.
//!
//! This crate provides reusable functions for transforming and analyzing
//! collections of beancount directives. All operations are pure — they take
//! directives in and return results out, with no I/O or framework coupling.
//!
//! Analogous to Python beancount's `ops/` module.
//!
//! # Modules
//!
//! - [`fingerprint`] — structural hashing and stable fingerprinting of transactions
//! - [`dedup`] — duplicate detection (structural, fuzzy, and fingerprint-based)
//! - [`categorize`] — rules engine for transaction categorization (substring, regex, exact match)
//! - [`merchants`] — built-in merchant dictionary of common patterns
//! - [`enrichment`] — shared types for operation results (confidence, method, alternatives)
//! - [`reconcile`] — balance reconciliation against statement ending balances
//! - [`ml`] — ML-based categorization (TF-IDF + Naive Bayes via linfa)
//! - [`transfer`] — inter-account transfer detection and linking

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod categorize;
pub mod dedup;
pub mod enrichment;
pub mod fingerprint;
pub mod merchants;
pub mod ml;
pub mod reconcile;
pub mod transfer;
