//! Beancount Query Language (BQL) engine.
//!
//! This crate provides a SQL-like query language for analyzing Beancount ledger data.
//!
//! # Overview
//!
//! BQL is a specialized query language designed for financial data analysis.
//! It operates on transaction postings while respecting double-entry bookkeeping constraints.
//!
//! # Query Types
//!
//! - `SELECT` - General purpose queries with filtering, grouping, and ordering
//! - `JOURNAL` - Shorthand for account statements
//! - `BALANCES` - Shorthand for account balance tables
//! - `PRINT` - Output filtered transactions in Beancount syntax
//!
//! # Example
//!
//! ```
//! use rustledger_query::parse;
//!
//! let query = parse("SELECT account, SUM(position) WHERE account ~ \"Expenses:\" GROUP BY account").unwrap();
//! println!("{:?}", query);
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod ast;
pub mod completions;
pub mod error;
pub mod executor;
pub mod parser;
pub mod price;

// AST types are accessed via `rustledger_query::ast::*` rather than re-exported
// at the crate root. The previous `pub use ast::*;` glob exposed 22 names —
// none used by external crates, and one (`Query`) collided with
// `rustledger_core::Directive::Query`. Power users still reach AST types via
// the `ast` module.
pub use error::{ParseError, QueryError};
pub use executor::{Executor, Interval, IntervalUnit, QueryResult, Value};
pub use parser::parse;
pub use price::PriceDatabase;
