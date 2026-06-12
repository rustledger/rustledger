//! Command implementations for CLI tools.
//!
//! Each module contains the full implementation for a command,
//! which can be invoked by thin wrapper binaries.

pub mod add_cmd;
pub mod check;
pub mod compat;
pub mod completions;
pub mod config_cmd;
pub mod doctor;
pub mod extract_cmd;
pub mod format;
pub mod lint;
pub mod loadcache;
pub mod price;
pub mod price_cmd;
pub mod query;
pub mod report_cmd;
