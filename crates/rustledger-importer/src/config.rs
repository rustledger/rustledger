//! Configuration for importers.

use anyhow::{Context, Result};
use format_num_pattern::{Locale, NumberFormat, NumberSymbols, fmt_to, parse_fmt};
use rust_decimal::Decimal;
use std::{fmt::Display, ops::Neg, str::FromStr};

/// Configuration for an importer.
///
/// Carries the common config (target account, currency) plus a
/// format-specific carrier in `importer_type`. Format-specific
/// configuration (CSV column mappings, amount parser locale, etc.)
/// lives inside `importer_type` so the parent struct stays minimal.
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
///
/// `ImporterType` carries *format-specific* configuration. OFX/QFX
/// extraction doesn't need any format-specific config beyond what's
/// already in [`ImporterConfig`] (target account, currency), so OFX
/// has no variant here — it's identified by `Importer::identify` on
/// path extension and dispatched via the trait. If OFX ever grows
/// format-specific knobs (e.g., balance-assertion emission), add an
/// `Ofx(OfxConfig)` variant.
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
    /// The column name or index for a per-row currency code. When set, each
    /// row's currency is read from this column (falling back to the config
    /// default currency / USD when the cell is blank).
    pub currency_column: Option<ColumnSpec>,
    /// Amount locale, see <https://docs.rs/format_num_pattern/latest/format_num_pattern/index.html>
    pub amount_locale: Option<Locale>,
    /// Amount format, see <https://docs.rs/format_num_pattern/latest/format_num_pattern/index.html>
    pub amount_format: Option<String>,
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
    /// Default expense account for unmatched negative-amount (money out) transactions.
    /// Defaults to "Expenses:Unknown".
    pub default_expense: Option<String>,
    /// Default income account for unmatched positive-amount (money in) transactions.
    /// Defaults to "Income:Unknown".
    pub default_income: Option<String>,
    /// Account mappings: pattern → account name.
    /// Patterns are matched case-insensitively against payee and narration fields.
    /// First match wins.
    pub mappings: Vec<(String, String)>,
    /// Regex-based account mappings: pattern → account name.
    /// Patterns are compiled as case-insensitive regexes.
    pub regex_mappings: Vec<(String, String)>,
    /// Whether to use the built-in merchant dictionary as a fallback.
    /// The dictionary provides common merchant patterns at low priority.
    pub use_merchant_dict: bool,
    /// Whether to drop rows whose amount parses to exactly zero. Defaults to
    /// true for back-compat: most banks emit zero-amount rows for status
    /// markers and importing them as transactions adds noise. Set false to
    /// preserve every source row (matches the user's expectation when
    /// auditing migrated data — see issue #972).
    pub skip_zero_amounts: bool,
}

impl Default for CsvConfig {
    fn default() -> Self {
        Self {
            date_column: ColumnSpec::Name("Date".to_string()),
            date_format: "%Y-%m-%d".to_string(),
            narration_column: Some(ColumnSpec::Name("Description".to_string())),
            payee_column: None,
            amount_column: Some(ColumnSpec::Name("Amount".to_string())),
            currency_column: None,
            amount_locale: Some(Locale::POSIX),
            amount_format: None,
            debit_column: None,
            credit_column: None,
            has_header: true,
            delimiter: ',',
            skip_rows: 0,
            invert_sign: false,
            default_expense: None,
            default_income: None,
            mappings: Vec::new(),
            regex_mappings: Vec::new(),
            use_merchant_dict: false,
            skip_zero_amounts: true,
        }
    }
}

impl CsvConfig {
    /// Compile the user's `amount_format` pattern and `amount_locale`
    /// into a runtime [`AmountFormat`] suitable for `AmountFormat::parse`.
    ///
    /// CSV parsing is locale- and format-sensitive (`"1.234,56"` vs
    /// `"1,234.56"` etc.); this builds the parser from the user's
    /// declarative inputs. Compile once per extract call, not per row.
    ///
    /// # Errors
    ///
    /// Returns an error if `amount_format` is set to an invalid pattern.
    pub fn compile_amount_format(&self) -> Result<AmountFormat> {
        Ok(match (&self.amount_format, &self.amount_locale) {
            (None, None) => AmountFormat::Symbols(NumberSymbols::monetary(Locale::POSIX)),
            (None, Some(locale)) => AmountFormat::Symbols(NumberSymbols::monetary(*locale)),
            (Some(fmt), None) => AmountFormat::Format(
                NumberFormat::new(fmt).with_context(|| "invalid amount_format")?,
            ),
            (Some(fmt), Some(locale)) => AmountFormat::Format(
                NumberFormat::news(fmt, NumberSymbols::monetary(*locale))
                    .with_context(|| "invalid number format")?,
            ),
        })
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

/// Localized/custom amount parsing
#[derive(Debug, Clone)]
pub enum AmountFormat {
    /// Override only symbols.
    Symbols(NumberSymbols),
    /// Override format.
    Format(NumberFormat),
}

// Do not replace with `format_num_pattern::core::parse_sym`: its `clean_num` strips post-decimal
// leading zeros, so "0.00" fails and "0.01" silently parses as 0.1. See issue #972.
fn parse_with_symbols(s: &str, sym: &NumberSymbols) -> Result<Decimal, rust_decimal::Error> {
    let mut buf = String::with_capacity(s.len());
    for c in s.chars() {
        if c.is_ascii_digit() {
            buf.push(c);
        } else if c == sym.negative_sym || c == '-' {
            // Always accept ASCII '-' even if the locale's negative_sym differs (e.g. U+2212): otherwise the sign silently flips.
            buf.push('-');
        } else if c == sym.decimal_sep {
            buf.push('.');
        } else if c == sym.exponent_lower_sym || c == sym.exponent_upper_sym {
            buf.push('e');
        }
    }
    Decimal::from_str(&buf)
}

impl AmountFormat {
    /// Attempt to parse a string using the given format.
    pub fn parse(&self, amount: &str) -> Result<Decimal> {
        let trimmed = amount.trim();

        // Trailing-minus negative convention ("50.00-"), emitted by some bank
        // and mainframe CSV exports. Strip the trailing sign and negate after
        // parsing, since the underlying numeric parsers reject a trailing '-'.
        // Parens negation (handled below) is mutually exclusive and takes
        // precedence, so don't treat a ")-"-style string as trailing-minus.
        let trailing_neg = trimmed.len() > 1 && trimmed.ends_with('-') && !trimmed.starts_with('(');
        let to_parse = if trailing_neg {
            &trimmed[..trimmed.len() - 1]
        } else {
            amount
        };

        // Reject a value carrying BOTH a leading and a trailing minus
        // (e.g. "-50.00-"): the sign is ambiguous, and silently negating the
        // already-negative magnitude to a positive would be surprising.
        if trailing_neg {
            let body = to_parse.trim_start();
            if body.starts_with('-') || body.starts_with('\u{2212}') {
                anyhow::bail!(
                    "ambiguous amount sign (both leading and trailing minus): {amount:?}"
                );
            }
        }

        let value: Decimal = match self {
            Self::Symbols(number_symbols) => parse_with_symbols(to_parse, number_symbols)
                .with_context(|| format!("unable to parse using symbols: {number_symbols:?}"))?,
            Self::Format(number_format) => parse_fmt(to_parse, number_format)
                .with_context(|| format!("unable to parse using given format: {number_format}"))?,
        };

        // Parens negation and trailing-minus are mutually exclusive (the latter
        // excludes a leading '('), so either one negates the parsed magnitude.
        let parens_neg = trimmed.starts_with('(') && trimmed.ends_with(')');
        if parens_neg || trailing_neg {
            Ok(value.neg())
        } else {
            Ok(value)
        }
    }

    /// Apply formatting to a decimal amount, making it printable.
    pub const fn apply(&self, amount: Decimal) -> FormattedAmount<'_> {
        FormattedAmount {
            amount,
            formatter: self,
        }
    }

    fn fmt_into<W: core::fmt::Write>(&self, amount: Decimal, writer: &mut W) {
        match self {
            Self::Symbols(number_symbols) => fmt_to(
                amount,
                &NumberFormat::news("###,##0.##", *number_symbols).unwrap(),
                writer,
            ),
            Self::Format(number_format) => fmt_to(amount, number_format, writer),
        }
    }
}

/// Formatted wrapper around a decimal, making it printable.
#[derive(Debug, Clone)]
pub struct FormattedAmount<'a> {
    amount: Decimal,
    formatter: &'a AmountFormat,
}

impl Display for FormattedAmount<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.formatter.fmt_into(self.amount, f);
        Ok(())
    }
}

impl Default for AmountFormat {
    fn default() -> Self {
        Self::Symbols(NumberSymbols::monetary(Locale::POSIX))
    }
}

impl ImporterConfig {
    /// Start building a CSV importer configuration.
    pub fn csv() -> CsvConfigBuilder {
        CsvConfigBuilder::new()
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

    /// Set the amount locale
    pub fn amount_locale(mut self, locale: impl Into<Locale>) -> Self {
        self.config.amount_locale = Some(locale.into());
        self
    }

    /// Set the amount format
    pub fn amount_format(mut self, format: impl Into<String>) -> Self {
        self.config.amount_format = Some(format.into());
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

    /// Set the per-row currency column by name.
    pub fn currency_column(mut self, name: impl Into<String>) -> Self {
        self.config.currency_column = Some(ColumnSpec::Name(name.into()));
        self
    }

    /// Set the per-row currency column by index.
    pub fn currency_column_index(mut self, index: usize) -> Self {
        self.config.currency_column = Some(ColumnSpec::Index(index));
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

    /// Set the default expense account for unmatched negative-amount (money out) transactions.
    pub fn default_expense(mut self, account: impl Into<String>) -> Self {
        self.config.default_expense = Some(account.into());
        self
    }

    /// Set the default income account for unmatched positive-amount (money in) transactions.
    pub fn default_income(mut self, account: impl Into<String>) -> Self {
        self.config.default_income = Some(account.into());
        self
    }

    /// Add account mappings for automatic categorization.
    ///
    /// Each mapping is a `(pattern, account)` pair. Patterns are matched
    /// case-insensitively against payee and narration fields. First match wins.
    /// Patterns are lowercased at build time for efficient matching.
    pub fn mappings(mut self, mappings: Vec<(String, String)>) -> Self {
        self.config.mappings = mappings
            .into_iter()
            .map(|(pattern, account)| (pattern.to_lowercase(), account))
            .collect();
        self
    }

    /// Set regex-based account mappings: pattern → account name.
    pub fn regex_mappings(mut self, mappings: Vec<(String, String)>) -> Self {
        self.config.regex_mappings = mappings;
        self
    }

    /// Enable the built-in merchant dictionary as a fallback.
    pub const fn use_merchant_dict(mut self, enable: bool) -> Self {
        self.config.use_merchant_dict = enable;
        self
    }

    /// Set whether to drop rows whose amount parses to zero. Default: true.
    /// Pass `false` to preserve every source row, matching auditor expectations
    /// when migrating from another tool (issue #972).
    pub const fn skip_zero_amounts(mut self, skip: bool) -> Self {
        self.config.skip_zero_amounts = skip;
        self
    }

    /// Build the importer configuration. Validates the amount-format
    /// pattern eagerly so misconfigured patterns surface at config
    /// build time rather than per-row at extract time.
    pub fn build(self) -> Result<ImporterConfig> {
        // Validate the amount-format pattern by attempting to compile it.
        // Discard the result; the importer recomputes it at extract time
        // from the CsvConfig inputs.
        let _ = self.config.compile_amount_format()?;
        Ok(ImporterConfig {
            account: self
                .account
                .unwrap_or_else(|| "Expenses:Unknown".to_string()),
            currency: self.currency,
            importer_type: ImporterType::Csv(self.config),
        })
    }
}

impl Default for CsvConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========== CsvConfig Default Tests ==========

    #[test]
    fn test_csv_config_default() {
        let config = CsvConfig::default();
        assert!(matches!(config.date_column, ColumnSpec::Name(ref s) if s == "Date"));
        assert_eq!(config.date_format, "%Y-%m-%d");
        assert!(config.narration_column.is_some());
        assert!(config.payee_column.is_none());
        assert!(config.amount_column.is_some());
        assert!(config.has_header);
        assert_eq!(config.delimiter, ',');
        assert_eq!(config.skip_rows, 0);
        assert!(!config.invert_sign);
    }

    // ========== CsvConfigBuilder Tests ==========

    #[test]
    fn test_csv_config_builder_new() {
        let builder = CsvConfigBuilder::new();
        assert!(builder.account.is_none());
        assert!(builder.currency.is_none());
    }

    #[test]
    fn test_csv_config_builder_default() {
        let builder = CsvConfigBuilder::default();
        assert!(builder.account.is_none());
    }

    #[test]
    fn test_csv_config_builder_account() {
        let config = CsvConfigBuilder::new()
            .account("Assets:Bank:Checking")
            .build()
            .unwrap();
        assert_eq!(config.account, "Assets:Bank:Checking");
    }

    #[test]
    fn test_csv_config_builder_default_account() {
        let config = CsvConfigBuilder::new().build().unwrap();
        assert_eq!(config.account, "Expenses:Unknown");
    }

    #[test]
    fn test_csv_config_builder_currency() {
        let config = CsvConfigBuilder::new().currency("EUR").build().unwrap();
        assert_eq!(config.currency, Some("EUR".to_string()));
    }

    #[test]
    fn test_csv_config_builder_date_column() {
        let config = CsvConfigBuilder::new()
            .date_column("TransactionDate")
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(
            matches!(csv_config.date_column, ColumnSpec::Name(ref s) if s == "TransactionDate")
        );
    }

    #[test]
    fn test_csv_config_builder_date_column_index() {
        let config = CsvConfigBuilder::new()
            .date_column_index(0)
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(matches!(csv_config.date_column, ColumnSpec::Index(0)));
    }

    #[test]
    fn test_csv_config_builder_date_format() {
        let config = CsvConfigBuilder::new()
            .date_format("%m/%d/%Y")
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert_eq!(csv_config.date_format, "%m/%d/%Y");
    }

    #[test]
    fn test_csv_config_builder_narration_column() {
        let config = CsvConfigBuilder::new()
            .narration_column("Memo")
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(
            matches!(csv_config.narration_column, Some(ColumnSpec::Name(ref s)) if s == "Memo")
        );
    }

    #[test]
    fn test_csv_config_builder_narration_column_index() {
        let config = CsvConfigBuilder::new()
            .narration_column_index(2)
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(matches!(
            csv_config.narration_column,
            Some(ColumnSpec::Index(2))
        ));
    }

    #[test]
    fn test_csv_config_builder_payee_column() {
        let config = CsvConfigBuilder::new()
            .payee_column("Merchant")
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(
            matches!(csv_config.payee_column, Some(ColumnSpec::Name(ref s)) if s == "Merchant")
        );
    }

    #[test]
    fn test_csv_config_builder_payee_column_index() {
        let config = CsvConfigBuilder::new()
            .payee_column_index(3)
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(matches!(
            csv_config.payee_column,
            Some(ColumnSpec::Index(3))
        ));
    }

    #[test]
    fn test_csv_config_builder_amount_column() {
        let config = CsvConfigBuilder::new()
            .amount_column("Value")
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(matches!(csv_config.amount_column, Some(ColumnSpec::Name(ref s)) if s == "Value"));
    }

    #[test]
    fn test_csv_config_builder_amount_column_index() {
        let config = CsvConfigBuilder::new()
            .amount_column_index(4)
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(matches!(
            csv_config.amount_column,
            Some(ColumnSpec::Index(4))
        ));
    }

    #[test]
    fn test_csv_config_builder_debit_credit_columns() {
        let config = CsvConfigBuilder::new()
            .debit_column("Debit")
            .credit_column("Credit")
            .build()
            .unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(matches!(csv_config.debit_column, Some(ColumnSpec::Name(ref s)) if s == "Debit"));
        assert!(matches!(csv_config.credit_column, Some(ColumnSpec::Name(ref s)) if s == "Credit"));
    }

    #[test]
    fn test_csv_config_builder_has_header() {
        let config = CsvConfigBuilder::new().has_header(false).build().unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(!csv_config.has_header);
    }

    #[test]
    fn test_csv_config_builder_delimiter() {
        let config = CsvConfigBuilder::new().delimiter(';').build().unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert_eq!(csv_config.delimiter, ';');
    }

    #[test]
    fn test_csv_config_builder_skip_rows() {
        let config = CsvConfigBuilder::new().skip_rows(3).build().unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert_eq!(csv_config.skip_rows, 3);
    }

    #[test]
    fn test_csv_config_builder_invert_sign() {
        let config = CsvConfigBuilder::new().invert_sign(true).build().unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(csv_config.invert_sign);
    }

    #[test]
    fn test_csv_config_builder_full_chain() {
        let config = CsvConfigBuilder::new()
            .account("Assets:Bank:Checking")
            .currency("USD")
            .date_column("Date")
            .date_format("%Y/%m/%d")
            .narration_column("Description")
            .payee_column("Payee")
            .amount_column("Amount")
            .has_header(true)
            .delimiter(',')
            .skip_rows(1)
            .invert_sign(false)
            .build()
            .unwrap();

        assert_eq!(config.account, "Assets:Bank:Checking");
        assert_eq!(config.currency, Some("USD".to_string()));

        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert!(matches!(csv_config.date_column, ColumnSpec::Name(ref s) if s == "Date"));
        assert_eq!(csv_config.date_format, "%Y/%m/%d");
        assert!(csv_config.narration_column.is_some());
        assert!(csv_config.payee_column.is_some());
        assert!(csv_config.amount_column.is_some());
        assert!(csv_config.has_header);
        assert_eq!(csv_config.delimiter, ',');
        assert_eq!(csv_config.skip_rows, 1);
        assert!(!csv_config.invert_sign);
    }

    // ========== ImporterConfig Tests ==========

    #[test]
    fn test_importer_config_csv() {
        let builder = ImporterConfig::csv();
        let config = builder.build().unwrap();
        assert!(matches!(config.importer_type, ImporterType::Csv(_)));
    }

    #[test]
    fn test_importer_config_extract_from_string() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv = "Date,Description,Amount\n2024-01-15,Test,-10.00\n";
        let result = crate::csv_importer::CsvImporter
            .extract_string(csv, &config)
            .unwrap();
        assert_eq!(result.directives.len(), 1);
    }

    // ========== ColumnSpec Tests ==========

    #[test]
    fn test_column_spec_name() {
        let spec = ColumnSpec::Name("Amount".to_string());
        assert!(matches!(spec, ColumnSpec::Name(ref s) if s == "Amount"));
    }

    #[test]
    fn test_column_spec_index() {
        let spec = ColumnSpec::Index(5);
        assert!(matches!(spec, ColumnSpec::Index(5)));
    }

    // ========== AmountFormat::parse Tests (regression for #972) ==========

    fn assert_matches_oracle(s: &str) {
        let ours = AmountFormat::default()
            .parse(s)
            .unwrap_or_else(|e| panic!("default parser rejected {s:?}: {e:?}"));
        let oracle = Decimal::from_str(s)
            .unwrap_or_else(|e| panic!("oracle Decimal::from_str rejected {s:?}: {e:?}"));
        assert_eq!(
            ours, oracle,
            "default parser disagreed with Decimal::from_str on {s:?}"
        );
    }

    #[test]
    fn parse_default_matches_decimal_from_str_oracle() {
        for s in [
            "0",
            "0.0",
            "0.00",
            "0.000",
            "0.1",
            "0.01",
            "0.001",
            "0.0001",
            "0.10",
            "0.05",
            "0.50",
            "-0",
            "-0.0",
            "-0.00",
            "-0.1",
            "-0.01",
            "-0.001",
            "1",
            "1.0",
            "1.00",
            "1.23",
            "1.230",
            "10",
            "100",
            "1234",
            "1234.56",
            "-1",
            "-1.00",
            "-1.23",
            "-1234.56",
            "1234567890.1234567890",
        ] {
            assert_matches_oracle(s);
        }
    }

    #[test]
    fn parse_default_zero_amount_succeeds() {
        // Direct regression for issue #972 reporter's case.
        assert_eq!(
            AmountFormat::default().parse("0.00").unwrap(),
            Decimal::ZERO
        );
    }

    #[test]
    fn parse_default_one_cent_is_not_ten_cents() {
        // The silent-corruption case: the buggy parser returned 0.1 for "0.01".
        let v = AmountFormat::default().parse("0.01").unwrap();
        assert_eq!(v, Decimal::from_str("0.01").unwrap());
        assert_ne!(v, Decimal::from_str("0.1").unwrap());
    }

    #[test]
    fn parse_default_negative_one_cent() {
        let v = AmountFormat::default().parse("-0.01").unwrap();
        assert_eq!(v, Decimal::from_str("-0.01").unwrap());
    }

    #[test]
    fn parse_default_sub_cent() {
        let v = AmountFormat::default().parse("0.001").unwrap();
        assert_eq!(v, Decimal::from_str("0.001").unwrap());
    }

    #[test]
    fn parse_default_parens_as_negative() {
        // Accountancy convention: (123.45) means -123.45.
        let v = AmountFormat::default().parse("(0.01)").unwrap();
        assert_eq!(v, Decimal::from_str("-0.01").unwrap());
    }

    #[test]
    fn parse_default_trailing_minus_as_negative() {
        // Trailing-minus convention ("50.00-") from some bank/mainframe exports.
        let f = AmountFormat::default();
        assert_eq!(
            f.parse("50.00-").unwrap(),
            Decimal::from_str("-50.00").unwrap()
        );
        assert_eq!(
            f.parse("1,234.56-").unwrap(),
            Decimal::from_str("-1234.56").unwrap()
        );
        // A lone "-" is not a number.
        assert!(f.parse("-").is_err());
        // Leading minus still works and isn't double-negated.
        assert_eq!(
            f.parse("-50.00").unwrap(),
            Decimal::from_str("-50.00").unwrap()
        );
        // Plain positive unaffected.
        assert_eq!(
            f.parse("50.00").unwrap(),
            Decimal::from_str("50.00").unwrap()
        );
        // Both leading and trailing minus is ambiguous → rejected, not flipped
        // to positive.
        assert!(f.parse("-50.00-").is_err());
        assert!(f.parse("\u{2212}50.00-").is_err());
    }

    #[test]
    fn parse_default_drops_currency_symbols_and_grouping() {
        // POSIX symbols set decimal_sep='.', positive_sym=' '. Group separator and
        // any unrecognized chars (currency, whitespace) are silently dropped.
        let v = AmountFormat::default().parse("$1,234.56").unwrap();
        assert_eq!(v, Decimal::from_str("1234.56").unwrap());
    }

    #[test]
    fn parse_german_locale_swaps_decimal_and_grouping() {
        // de_DE uses ',' as decimal separator and '.' as grouping. "1.234,56" -> 1234.56.
        let f = AmountFormat::Symbols(NumberSymbols::monetary(Locale::de_DE));
        let v = f.parse("1.234,56").unwrap();
        assert_eq!(v, Decimal::from_str("1234.56").unwrap());
    }

    #[test]
    fn parse_german_locale_sub_cent() {
        // The same bug class would corrupt sub-unit German amounts: "0,01" must not become 0,1.
        let f = AmountFormat::Symbols(NumberSymbols::monetary(Locale::de_DE));
        let v = f.parse("0,01").unwrap();
        assert_eq!(v, Decimal::from_str("0.01").unwrap());
    }

    #[test]
    fn parse_ascii_minus_honored_when_locale_uses_unicode_minus() {
        // If the configured locale's negative_sym is U+2212 but the CSV emits ASCII '-' (the
        // common real-world case), the sign must not be silently dropped. Regression for
        // Copilot's review on PR #974.
        let mut sym = NumberSymbols::monetary(Locale::POSIX);
        sym.negative_sym = '\u{2212}';
        let f = AmountFormat::Symbols(sym);
        let v = f.parse("-0.01").unwrap();
        assert_eq!(v, Decimal::from_str("-0.01").unwrap());
    }

    proptest::proptest! {
        #[test]
        fn parse_default_round_trips_through_display(
            mantissa in i64::MIN..=i64::MAX,
            scale in 0u32..=9
        ) {
            let original = Decimal::new(mantissa, scale);
            let s = original.to_string();
            let parsed = AmountFormat::default().parse(&s).unwrap();
            proptest::prop_assert_eq!(parsed, original);
        }
    }
}
