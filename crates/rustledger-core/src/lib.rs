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
//! use chrono::NaiveDate;
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
pub mod directive;
pub mod format;
pub mod intern;
pub mod inventory;
pub mod position;

pub use amount::{Amount, IncompleteAmount};
pub use cost::{Cost, CostSpec};
pub use directive::{
    sort_directives, Balance, Close, Commodity, Custom, Directive, DirectivePriority, Document,
    Event, MetaValue, Metadata, Note, Open, Pad, Posting, Price, PriceAnnotation, Query,
    Transaction,
};
pub use format::{format_directive, FormatConfig};
pub use inventory::{BookingError, BookingMethod, BookingResult, Inventory};
pub use position::Position;

// Re-export commonly used external types
pub use chrono::NaiveDate;
pub use rust_decimal::Decimal;
