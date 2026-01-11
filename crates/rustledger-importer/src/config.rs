//! Configuration for importers.

use crate::csv_importer::CsvImporter;
use crate::ImportResult;
use anyhow::Result;
use std::path::Path;

/// Configuration for an importer.
#[derive(Debug, Clone)]
pub struct ImporterConfig {
    /// The target account for imported transactions.
    pub account: String,
    /// The currency for amounts (if not specified in the file).
    pub currency: Option<String>,
    /// The importer type and its specific configuration.
    pub importer_type: ImporterType,
}

/// Type of importer with its specific configuration.
#[derive(Debug, Clone)]
pub enum ImporterType {
    /// CSV file importer.
    Csv(CsvConfig),
}

/// Configuration specific to CSV imports.
#[derive(Debug, Clone)]
pub struct CsvConfig {
    /// The column name or index for the date.
    pub date_column: ColumnSpec,
    /// The date format (strftime-style).
    pub date_format: String,
    /// The column name or index for the narration/description.
    pub narration_column: Option<ColumnSpec>,
    /// The column name or index for the payee.
    pub payee_column: Option<ColumnSpec>,
    /// The column name or index for the amount.
    pub amount_column: Option<ColumnSpec>,
    /// The column name or index for debit amounts (if separate from credit).
    pub debit_column: Option<ColumnSpec>,
    /// The column name or index for credit amounts (if separate from debit).
    pub credit_column: Option<ColumnSpec>,
    /// Whether the CSV has a header row.
    pub has_header: bool,
    /// The field delimiter.
    pub delimiter: char,
    /// Number of rows to skip at the beginning.
    pub skip_rows: usize,
    /// Whether to invert the sign of amounts.
    pub invert_sign: bool,
}

impl Default for CsvConfig {
    fn default() -> Self {
        Self {
            date_column: ColumnSpec::Name("Date".to_string()),
            date_format: "%Y-%m-%d".to_string(),
            narration_column: Some(ColumnSpec::Name("Description".to_string())),
            payee_column: None,
            amount_column: Some(ColumnSpec::Name("Amount".to_string())),
            debit_column: None,
            credit_column: None,
            has_header: true,
            delimiter: ',',
            skip_rows: 0,
            invert_sign: false,
        }
    }
}

/// Specification for a column in the source file.
#[derive(Debug, Clone)]
pub enum ColumnSpec {
    /// Column specified by name (from header).
    Name(String),
    /// Column specified by zero-based index.
    Index(usize),
}

impl ImporterConfig {
    /// Start building a CSV importer configuration.
    pub fn csv() -> CsvConfigBuilder {
        CsvConfigBuilder::new()
    }

    /// Extract transactions from a file.
    pub fn extract(&self, path: &Path) -> Result<ImportResult> {
        match &self.importer_type {
            ImporterType::Csv(csv_config) => {
                let importer = CsvImporter::new(self.clone());
                importer.extract_file(path, csv_config)
            }
        }
    }

    /// Extract transactions from string content.
    pub fn extract_from_string(&self, content: &str) -> Result<ImportResult> {
        match &self.importer_type {
            ImporterType::Csv(csv_config) => {
                let importer = CsvImporter::new(self.clone());
                importer.extract_string(content, csv_config)
            }
        }
    }
}

/// Builder for CSV importer configuration.
pub struct CsvConfigBuilder {
    account: Option<String>,
    currency: Option<String>,
    config: CsvConfig,
}

impl CsvConfigBuilder {
    /// Create a new CSV config builder.
    pub fn new() -> Self {
        Self {
            account: None,
            currency: None,
            config: CsvConfig::default(),
        }
    }

    /// Set the target account.
    pub fn account(mut self, account: impl Into<String>) -> Self {
        self.account = Some(account.into());
        self
    }

    /// Set the currency for amounts.
    pub fn currency(mut self, currency: impl Into<String>) -> Self {
        self.currency = Some(currency.into());
        self
    }

    /// Set the date column by name.
    pub fn date_column(mut self, name: impl Into<String>) -> Self {
        self.config.date_column = ColumnSpec::Name(name.into());
        self
    }

    /// Set the date column by index.
    pub fn date_column_index(mut self, index: usize) -> Self {
        self.config.date_column = ColumnSpec::Index(index);
        self
    }

    /// Set the date format (strftime-style).
    pub fn date_format(mut self, format: impl Into<String>) -> Self {
        self.config.date_format = format.into();
        self
    }

    /// Set the narration/description column by name.
    pub fn narration_column(mut self, name: impl Into<String>) -> Self {
        self.config.narration_column = Some(ColumnSpec::Name(name.into()));
        self
    }

    /// Set the narration column by index.
    pub fn narration_column_index(mut self, index: usize) -> Self {
        self.config.narration_column = Some(ColumnSpec::Index(index));
        self
    }

    /// Set the payee column by name.
    pub fn payee_column(mut self, name: impl Into<String>) -> Self {
        self.config.payee_column = Some(ColumnSpec::Name(name.into()));
        self
    }

    /// Set the payee column by index.
    pub fn payee_column_index(mut self, index: usize) -> Self {
        self.config.payee_column = Some(ColumnSpec::Index(index));
        self
    }

    /// Set the amount column by name.
    pub fn amount_column(mut self, name: impl Into<String>) -> Self {
        self.config.amount_column = Some(ColumnSpec::Name(name.into()));
        self
    }

    /// Set the amount column by index.
    pub fn amount_column_index(mut self, index: usize) -> Self {
        self.config.amount_column = Some(ColumnSpec::Index(index));
        self
    }

    /// Set separate debit column by name.
    pub fn debit_column(mut self, name: impl Into<String>) -> Self {
        self.config.debit_column = Some(ColumnSpec::Name(name.into()));
        self
    }

    /// Set separate credit column by name.
    pub fn credit_column(mut self, name: impl Into<String>) -> Self {
        self.config.credit_column = Some(ColumnSpec::Name(name.into()));
        self
    }

    /// Set whether the CSV has a header row.
    pub const fn has_header(mut self, has_header: bool) -> Self {
        self.config.has_header = has_header;
        self
    }

    /// Set the field delimiter.
    pub const fn delimiter(mut self, delimiter: char) -> Self {
        self.config.delimiter = delimiter;
        self
    }

    /// Set the number of rows to skip.
    pub const fn skip_rows(mut self, count: usize) -> Self {
        self.config.skip_rows = count;
        self
    }

    /// Set whether to invert the sign of amounts.
    pub const fn invert_sign(mut self, invert: bool) -> Self {
        self.config.invert_sign = invert;
        self
    }

    /// Build the importer configuration.
    pub fn build(self) -> ImporterConfig {
        ImporterConfig {
            account: self
                .account
                .unwrap_or_else(|| "Expenses:Unknown".to_string()),
            currency: self.currency,
            importer_type: ImporterType::Csv(self.config),
        }
    }
}

impl Default for CsvConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}
