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
    pub fn new(directives: Vec<Directive>) -> Self {
        Self {
            directives,
            warnings: Vec::new(),
        }
    }

    /// Create an empty import result.
    pub fn empty() -> Self {
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
