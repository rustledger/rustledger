//! Import framework for rustledger
//!
//! This crate provides the infrastructure for extracting transactions from
//! bank statements, credit card statements, and other financial documents.
//!
//! # Overview
//!
//! The import system is modeled after Python beancount's bean-extract. It uses
//! a trait-based approach where each importer implements the [`Importer`] trait.
//!
//! # Example
//!
//! ```rust,no_run
//! use rustledger_importer::{Importer, ImporterConfig, extract_from_file};
//! use rustledger_core::Directive;
//! use std::path::Path;
//!
//! // Create a CSV importer configuration
//! let config = ImporterConfig::csv()
//!     .account("Assets:Bank:Checking")
//!     .date_column("Date")
//!     .narration_column("Description")
//!     .amount_column("Amount")
//!     .build();
//!
//! // Extract transactions from a file
//! // let directives = extract_from_file(Path::new("bank.csv"), &config)?;
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod config;
pub mod csv_importer;
pub mod ofx_importer;
pub mod registry;

use anyhow::Result;
use rustledger_core::Directive;
use std::path::Path;

pub use config::ImporterConfig;
pub use ofx_importer::OfxImporter;
pub use registry::ImporterRegistry;

/// Result of an import operation.
#[derive(Debug, Clone)]
pub struct ImportResult {
    /// The extracted directives.
    pub directives: Vec<Directive>,
    /// Warnings encountered during import.
    pub warnings: Vec<String>,
}

impl ImportResult {
    /// Create a new import result.
    pub const fn new(directives: Vec<Directive>) -> Self {
        Self {
            directives,
            warnings: Vec::new(),
        }
    }

    /// Create an empty import result.
    pub const fn empty() -> Self {
        Self {
            directives: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Add a warning to the result.
    pub fn with_warning(mut self, warning: impl Into<String>) -> Self {
        self.warnings.push(warning.into());
        self
    }
}

/// Trait for file importers.
///
/// Implementors of this trait can extract beancount directives from various
/// file formats (CSV, OFX, QFX, etc.).
pub trait Importer: Send + Sync {
    /// Returns the name of this importer.
    fn name(&self) -> &str;

    /// Check if this importer can handle the given file.
    ///
    /// This method should be fast - it typically checks file extension,
    /// header patterns, or other quick heuristics.
    fn identify(&self, path: &Path) -> bool;

    /// Extract directives from the given file.
    fn extract(&self, path: &Path) -> Result<ImportResult>;

    /// Returns a description of what this importer handles.
    fn description(&self) -> &str {
        self.name()
    }
}

/// Extract transactions from a file using the given configuration.
pub fn extract_from_file(path: &Path, config: &ImporterConfig) -> Result<ImportResult> {
    config.extract(path)
}

/// Extract transactions from file contents (useful for testing).
pub fn extract_from_string(content: &str, config: &ImporterConfig) -> Result<ImportResult> {
    config.extract_from_string(content)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal::Decimal;
    use rustledger_core::{Amount, Posting, Transaction};
    use std::str::FromStr;

    // ========== ImportResult Tests ==========

    #[test]
    fn test_import_result_new() {
        let directives = vec![];
        let result = ImportResult::new(directives);
        assert!(result.directives.is_empty());
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn test_import_result_empty() {
        let result = ImportResult::empty();
        assert!(result.directives.is_empty());
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn test_import_result_with_warning() {
        let result = ImportResult::empty().with_warning("Test warning");
        assert_eq!(result.warnings.len(), 1);
        assert_eq!(result.warnings[0], "Test warning");
    }

    #[test]
    fn test_import_result_multiple_warnings() {
        let result = ImportResult::empty()
            .with_warning("Warning 1")
            .with_warning("Warning 2");
        assert_eq!(result.warnings.len(), 2);
        assert_eq!(result.warnings[0], "Warning 1");
        assert_eq!(result.warnings[1], "Warning 2");
    }

    #[test]
    fn test_import_result_with_directives() {
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test transaction")
            .with_posting(Posting::new(
                "Assets:Bank",
                Amount::new(Decimal::from_str("100").unwrap(), "USD"),
            ))
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(Decimal::from_str("-100").unwrap(), "USD"),
            ));
        let directives = vec![Directive::Transaction(txn)];
        let result = ImportResult::new(directives);
        assert_eq!(result.directives.len(), 1);
    }

    // ========== extract_from_string Tests ==========

    #[test]
    fn test_extract_from_string_csv() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank:Checking")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build();

        let csv_content = "Date,Description,Amount\n2024-01-15,Coffee,-5.00\n";
        let result = extract_from_string(csv_content, &config).unwrap();
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn test_extract_from_string_empty_csv() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank:Checking")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build();

        let csv_content = "Date,Description,Amount\n";
        let result = extract_from_string(csv_content, &config).unwrap();
        assert!(result.directives.is_empty());
    }

    #[test]
    fn test_import_result_debug() {
        let result = ImportResult::empty();
        let debug_str = format!("{result:?}");
        assert!(debug_str.contains("ImportResult"));
    }

    #[test]
    fn test_import_result_clone() {
        let result = ImportResult::empty().with_warning("Test");
        let cloned = result.clone();
        // Verify both original and clone have the warning
        assert_eq!(result.warnings.len(), 1);
        assert_eq!(cloned.warnings.len(), 1);
    }
}
