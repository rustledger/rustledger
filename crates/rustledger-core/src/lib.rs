//! Core types for rustledger
//!
//! This crate provides the fundamental types used throughout the rustledger project:
//!
//! - [`Amount`] - A decimal number with a currency
//! - [`Cost`] - Acquisition cost of a position (lot)
//! - [`CostSpec`] - Specification for matching or creating costs
//! - [`Position`] - Units held at a cost
//! - [`Inventory`] - A collection of positions with booking support
//! - [`BookingMethod`] - How to match lots when reducing positions
//! - [`Directive`] - All directive types (Transaction, Balance, Open, etc.)
//!
//! # Example
//!
//! ```
//! use rustledger_core::{Amount, Cost, Position, Inventory, BookingMethod};
//! use rust_decimal_macros::dec;
//! use rustledger_core::NaiveDate;
//!
//! // Create an inventory
//! let mut inv = Inventory::new();
//!
//! // Add a stock position with cost
//! let cost = Cost::new(dec!(150.00), "USD")
//!     .with_date(NaiveDate::from_ymd_opt(2024, 1, 15).unwrap());
//! inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));
//!
//! // Check holdings
//! assert_eq!(inv.units("AAPL"), dec!(10));
//!
//! // Sell some shares using FIFO
//! let result = inv.reduce(
//!     &Amount::new(dec!(-5), "AAPL"),
//!     None,
//!     BookingMethod::Fifo,
//! ).unwrap();
//!
//! assert_eq!(inv.units("AAPL"), dec!(5));
//! assert_eq!(result.cost_basis.unwrap().number, dec!(750.00)); // 5 * 150
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod amount;
pub mod cost;
pub mod date;
pub mod directive;
pub mod display_context;
pub mod extract;
pub mod format;
pub mod intern;
pub mod inventory;
pub mod position;
pub mod synthetic;

// Kani formal verification proofs (only compiled with Kani)
#[cfg(kani)]
mod kani_proofs;

pub use amount::{Amount, IncompleteAmount};
pub use cost::{Cost, CostSpec};
pub use directive::{
    Balance, Close, Commodity, Custom, Directive, DirectivePriority, Document, Event, MetaValue,
    Metadata, Note, Open, Pad, Posting, Price, PriceAnnotation, Query, Transaction,
    sort_directives,
};
pub use display_context::DisplayContext;
pub use extract::{
    DEFAULT_CURRENCIES, extract_accounts, extract_accounts_iter, extract_currencies,
    extract_currencies_iter, extract_payees, extract_payees_iter,
};
pub use format::{FormatConfig, format_directive};
pub use intern::{InternedStr, StringInterner};
pub use inventory::{AccountedBookingError, BookingError, BookingMethod, BookingResult, Inventory};
pub use position::Position;

// Re-export commonly used external types
pub use date::{Duration, Months, NaiveDate, Weekday};
pub use rust_decimal::Decimal;

// Re-export rkyv wrappers when feature is enabled
#[cfg(feature = "rkyv")]
pub use intern::{AsDecimal, AsInternedStr, AsNaiveDate};
