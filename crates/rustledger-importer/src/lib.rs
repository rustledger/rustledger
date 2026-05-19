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
//! use rustledger_importer::{ImporterConfig, ImporterRegistry};
//! use std::path::Path;
//!
//! // Build the per-call config (CSV in this example).
//! let config = ImporterConfig::csv()
//!     .account("Assets:Bank:Checking")
//!     .date_column("Date")
//!     .narration_column("Description")
//!     .amount_column("Amount")
//!     .build()
//!     .unwrap();
//!
//! // Dispatch through the registry — picks OfxImporter for .ofx/.qfx,
//! // CsvImporter for .csv. Returns an error for unknown extensions.
//! let registry = ImporterRegistry::with_builtins();
//! // let result = registry.extract(Path::new("bank.csv"), &config)?;
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod config;
pub mod csv_importer;
pub mod csv_inference;
pub mod ofx_importer;
pub mod registry;
pub mod test_fixtures;
pub mod wasm;

use anyhow::Result;
use rustledger_core::Directive;
use rustledger_ops::enrichment::Enrichment;
use std::path::Path;

pub use config::ImporterConfig;
pub use ofx_importer::OfxImporter;
pub use registry::{ImporterRegistry, WasmDirScanReport};
pub use wasm::{WasmImporter, WasmImporterError, WasmRuntimeConfig};

use rustledger_ops::fingerprint::Fingerprint;

/// Compute an import fingerprint from a directive.
///
/// For transactions, uses the first posting's amount and the payee+narration
/// text. Returns `None` for non-transaction directives.
pub(crate) fn directive_fingerprint(directive: &Directive) -> Option<Fingerprint> {
    let Directive::Transaction(txn) = directive else {
        return None;
    };
    let amount_str = txn.postings.first().and_then(|p| {
        p.units
            .as_ref()
            .and_then(|u| u.number().map(|n| n.to_string()))
    });
    let mut text = String::new();
    if let Some(ref payee) = txn.payee {
        text.push_str(payee.as_str());
        text.push(' ');
    }
    text.push_str(txn.narration.as_str());
    Some(Fingerprint::compute(
        &txn.date.to_string(),
        amount_str.as_deref(),
        &text,
    ))
}

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

/// Result of an enriched import operation.
///
/// Each directive is paired with an [`Enrichment`] that carries metadata about
/// how it was categorized, its confidence score, and a stable fingerprint for
/// deduplication.
#[derive(Debug, Clone)]
pub struct EnrichedImportResult {
    /// Directive–enrichment pairs.
    pub entries: Vec<(Directive, Enrichment)>,
    /// Warnings encountered during import.
    pub warnings: Vec<String>,
}

impl EnrichedImportResult {
    /// Create a new enriched import result.
    pub const fn new(entries: Vec<(Directive, Enrichment)>) -> Self {
        Self {
            entries,
            warnings: Vec::new(),
        }
    }

    /// Create an empty enriched import result.
    pub const fn empty() -> Self {
        Self {
            entries: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Add a warning.
    pub fn with_warning(mut self, warning: impl Into<String>) -> Self {
        self.warnings.push(warning.into());
        self
    }

    /// Convert to a plain [`ImportResult`], discarding enrichment metadata.
    #[must_use]
    pub fn into_import_result(self) -> ImportResult {
        ImportResult {
            directives: self.entries.into_iter().map(|(d, _)| d).collect(),
            warnings: self.warnings,
        }
    }
}

impl From<EnrichedImportResult> for ImportResult {
    fn from(enriched: EnrichedImportResult) -> Self {
        enriched.into_import_result()
    }
}

impl From<ImportResult> for EnrichedImportResult {
    /// Promote an [`ImportResult`] into an [`EnrichedImportResult`] by
    /// attaching a default (uncategorized, no-fingerprint) [`Enrichment`]
    /// to each directive. This is the cheap-default impl used by
    /// [`Importer::extract_enriched`] when an importer does not provide
    /// a custom enrichment path; format-specific importers should
    /// override `extract_enriched` to produce real metadata.
    fn from(result: ImportResult) -> Self {
        let entries = result
            .directives
            .into_iter()
            .enumerate()
            .map(|(i, directive)| {
                let enrichment = Enrichment {
                    directive_index: i,
                    confidence: 0.0,
                    method: rustledger_ops::enrichment::CategorizationMethod::Default,
                    alternatives: vec![],
                    fingerprint: directive_fingerprint(&directive),
                };
                (directive, enrichment)
            })
            .collect();
        let mut enriched = Self::new(entries);
        for warning in result.warnings {
            enriched = enriched.with_warning(warning);
        }
        enriched
    }
}

/// Trait for file importers.
///
/// Implementors of this trait are **stateless** — they describe a file
/// format (OFX, CSV, ...), not a particular import job. Per-call
/// configuration (target account, currency, column mappings) flows in
/// via [`ImporterConfig`]. This lets a single instance live in
/// [`ImporterRegistry`] and serve many imports without per-job
/// construction.
///
/// Implementors should match on `config.importer_type` if they require
/// format-specific config (e.g. `CsvImporter` needs `CsvConfig`), and
/// return an error if the config variant doesn't match what they handle.
pub trait Importer: Send + Sync {
    /// Returns the name of this importer.
    fn name(&self) -> &str;

    /// Check if this importer can handle the given file.
    ///
    /// This method should be fast - it typically checks file extension,
    /// header patterns, or other quick heuristics.
    fn identify(&self, path: &Path) -> bool;

    /// Extract directives from the given file using `config`.
    ///
    /// `config.account` and `config.currency` are common across all
    /// formats; format-specific configuration lives in
    /// `config.importer_type` (e.g. `ImporterType::Csv(CsvConfig)`).
    fn extract(&self, path: &Path, config: &ImporterConfig) -> Result<ImportResult>;

    /// Extract directives with per-directive enrichment metadata
    /// (categorization confidence, method, alternatives, fingerprint).
    ///
    /// Default impl wraps [`Importer::extract`] and produces default
    /// (uncategorized, no-alternative) enrichments with a computed
    /// fingerprint. Importers that know how to produce *real*
    /// categorization confidence (e.g. CSV via its mappings/regex/
    /// merchant-dict rules engine) should override this method.
    ///
    /// Critical: this method exists on the trait — not just as a
    /// concrete-type helper — so that WASM-loaded importers in wave
    /// 2.3 can participate in the enriched pipeline (dedup, import-
    /// suggestion confidence, etc.) without being downcast.
    fn extract_enriched(
        &self,
        path: &Path,
        config: &ImporterConfig,
    ) -> Result<EnrichedImportResult> {
        Ok(EnrichedImportResult::from(self.extract(path, config)?))
    }

    /// Returns a description of what this importer handles.
    fn description(&self) -> &str {
        self.name()
    }
}

/// Auto-extract transactions from a file by inferring its format.
///
/// If the file is OFX/QFX, uses the OFX importer directly. Otherwise,
/// attempts to infer the CSV format from the file content. Returns the
/// enriched result with fingerprints and confidence scores.
///
/// # Errors
///
/// Returns an error if the file can't be read, the format can't be inferred,
/// or extraction fails.
pub fn auto_extract(
    path: &std::path::Path,
    account: &str,
    currency: &str,
) -> Result<EnrichedImportResult> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| anyhow::anyhow!("Failed to read file {}: {e}", path.display()))?;

    // Check for OFX first
    if path
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("ofx") || ext.eq_ignore_ascii_case("qfx"))
    {
        // OFX doesn't care about `importer_type` (its impl doesn't read
        // it); inert Csv variant satisfies the type.
        let cfg = config::ImporterConfig {
            account: account.to_string(),
            currency: Some(currency.to_string()),
            importer_type: config::ImporterType::Csv(config::CsvConfig::default()),
        };
        return ofx_importer::OfxImporter.extract_from_string_enriched(&content, &cfg);
    }

    // Try CSV auto-inference
    let inferred = csv_inference::infer_csv_config(&content)
        .ok_or_else(|| anyhow::anyhow!("Could not infer CSV format from {}", path.display()))?;

    let cfg = config::ImporterConfig {
        account: account.to_string(),
        currency: Some(currency.to_string()),
        importer_type: config::ImporterType::Csv(inferred.to_csv_config()),
    };
    csv_importer::CsvImporter.extract_string_enriched(&content, &cfg)
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
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test transaction")
            .with_synthesized_posting(Posting::new(
                "Assets:Bank",
                Amount::new(Decimal::from_str("100").unwrap(), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
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
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n2024-01-15,Coffee,-5.00\n";
        let result = csv_importer::CsvImporter
            .extract_string(csv_content, &config)
            .unwrap();
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
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n";
        let result = csv_importer::CsvImporter
            .extract_string(csv_content, &config)
            .unwrap();
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

    // ========== EnrichedImportResult Tests ==========

    fn make_test_enrichment(index: usize, confidence: f64) -> Enrichment {
        Enrichment {
            directive_index: index,
            confidence,
            method: rustledger_ops::enrichment::CategorizationMethod::Rule,
            alternatives: vec![],
            fingerprint: None,
        }
    }

    fn make_test_txn_directive() -> Directive {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new(
                "Assets:Bank",
                Amount::new(Decimal::from_str("-50").unwrap(), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(Decimal::from_str("50").unwrap(), "USD"),
            ));
        Directive::Transaction(txn)
    }

    #[test]
    fn test_enriched_import_result_new() {
        let directive = make_test_txn_directive();
        let enrichment = make_test_enrichment(0, 0.95);
        let entries = vec![(directive, enrichment)];
        let result = EnrichedImportResult::new(entries);
        assert_eq!(result.entries.len(), 1);
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn test_enriched_import_result_empty() {
        let result = EnrichedImportResult::empty();
        assert!(result.entries.is_empty());
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn test_enriched_import_result_with_warning() {
        let result = EnrichedImportResult::empty().with_warning("Test warning");
        assert_eq!(result.warnings.len(), 1);
        assert_eq!(result.warnings[0], "Test warning");
    }

    #[test]
    fn test_enriched_import_result_multiple_warnings() {
        let result = EnrichedImportResult::empty()
            .with_warning("Warning 1")
            .with_warning("Warning 2");
        assert_eq!(result.warnings.len(), 2);
    }

    #[test]
    fn test_enriched_into_import_result() {
        let d1 = make_test_txn_directive();
        let d2 = make_test_txn_directive();
        let entries = vec![
            (d1, make_test_enrichment(0, 0.95)),
            (d2, make_test_enrichment(1, 0.3)),
        ];
        let enriched = EnrichedImportResult::new(entries).with_warning("A warning");

        let plain = enriched.into_import_result();
        // Directives preserved, enrichment dropped
        assert_eq!(plain.directives.len(), 2);
        // Warnings preserved
        assert_eq!(plain.warnings.len(), 1);
        assert_eq!(plain.warnings[0], "A warning");
    }

    #[test]
    fn test_enriched_from_into_import_result() {
        let entries = vec![(make_test_txn_directive(), make_test_enrichment(0, 1.0))];
        let enriched = EnrichedImportResult::new(entries);

        // Use the From<EnrichedImportResult> for ImportResult trait
        let plain: ImportResult = enriched.into();
        assert_eq!(plain.directives.len(), 1);
        assert!(plain.warnings.is_empty());
    }

    #[test]
    fn test_enriched_import_result_debug_and_clone() {
        let result = EnrichedImportResult::empty().with_warning("Test");
        let debug_str = format!("{result:?}");
        assert!(debug_str.contains("EnrichedImportResult"));
        let cloned = result;
        assert_eq!(cloned.warnings.len(), 1);
    }

    // ========== directive_fingerprint Tests ==========

    #[test]
    fn test_directive_fingerprint_for_transaction() {
        let directive = make_test_txn_directive();
        let fp = directive_fingerprint(&directive);
        assert!(fp.is_some());
    }

    #[test]
    fn test_directive_fingerprint_none_for_non_transaction() {
        // Use a Balance directive
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let balance = rustledger_core::Balance::new(
            date,
            "Assets:Bank",
            Amount::new(Decimal::from_str("1000").unwrap(), "USD"),
        );
        let directive = Directive::Balance(balance);
        let fp = directive_fingerprint(&directive);
        assert!(fp.is_none());
    }
}
