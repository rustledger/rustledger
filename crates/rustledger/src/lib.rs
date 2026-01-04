//! Beancount CLI tools.
//!
//! This crate provides command-line tools for working with Beancount files:
//!
//! - `rledger-check` / `bean-check`: Validate a beancount file
//! - `rledger-format` / `bean-format`: Format a beancount file
//! - `rledger-query` / `bean-query`: Query with BQL
//! - `rledger-report` / `bean-report`: Generate reports
//! - `rledger-doctor` / `bean-doctor`: Debugging tools
//!
//! # Example Usage
//!
//! ```bash
//! rledger-check ledger.beancount
//! rledger-format ledger.beancount
//! rledger-query ledger.beancount "SELECT account, SUM(position)"
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod cmd;
pub mod format;
pub mod report;
