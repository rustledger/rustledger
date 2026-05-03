//! CSV file importer.

use crate::config::{ColumnSpec, CsvConfig, ImporterConfig};
use crate::{EnrichedImportResult, ImportResult};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_ops::enrichment::{CategorizationMethod, Enrichment};
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;

/// CSV file importer.
pub struct CsvImporter {
    config: ImporterConfig,
}

impl CsvImporter {
    /// Create a new CSV importer with the given configuration.
    pub const fn new(config: ImporterConfig) -> Self {
        Self { config }
    }

    /// Extract transactions from a file.
    pub fn extract_file(&self, path: &Path, csv_config: &CsvConfig) -> Result<ImportResult> {
        let file =
            File::open(path).with_context(|| format!("Failed to open file: {}", path.display()))?;
        let mut reader = BufReader::new(file);
        let mut content = String::new();
        reader.read_to_string(&mut content)?;
        self.extract_string(&content, csv_config)
    }

    /// Extract transactions from string content.
    pub fn extract_string(&self, content: &str, csv_config: &CsvConfig) -> Result<ImportResult> {
        let mut reader = csv::ReaderBuilder::new()
            .has_headers(csv_config.has_header)
            .delimiter(csv_config.delimiter as u8)
            .from_reader(content.as_bytes());

        // Build column name to index map from headers
        let header_map: HashMap<String, usize> = if csv_config.has_header {
            reader
                .headers()?
                .iter()
                .enumerate()
                .map(|(i, h)| (h.to_string(), i))
                .collect()
        } else {
            HashMap::new()
        };

        let mut directives = Vec::new();
        let mut warnings = Vec::new();
        let mut row_num = csv_config.skip_rows;

        for result in reader.records().skip(csv_config.skip_rows) {
            row_num += 1;
            let record = match result {
                Ok(r) => r,
                Err(e) => {
                    warnings.push(format!("Row {row_num}: parse error: {e}"));
                    continue;
                }
            };

            match self.parse_row(&record, csv_config, &header_map, row_num) {
                Ok(Some(txn)) => directives.push(Directive::Transaction(txn)),
                Ok(None) => {} // Skip empty rows
                Err(e) => {
                    warnings.push(format!("Row {row_num}: {e}"));
                }
            }
        }

        let mut result = ImportResult::new(directives);
        for warning in warnings {
            result = result.with_warning(warning);
        }
        Ok(result)
    }

    /// Extract transactions from a file with enrichment metadata.
    ///
    /// Each transaction is paired with an [`Enrichment`] that includes a
    /// stable fingerprint and categorization confidence.
    pub fn extract_file_enriched(
        &self,
        path: &Path,
        csv_config: &CsvConfig,
    ) -> Result<EnrichedImportResult> {
        let file =
            File::open(path).with_context(|| format!("Failed to open file: {}", path.display()))?;
        let mut reader = BufReader::new(file);
        let mut content = String::new();
        reader.read_to_string(&mut content)?;
        self.extract_string_enriched(&content, csv_config)
    }

    /// Extract transactions from string content with enrichment metadata.
    ///
    /// Builds a [`rustledger_ops::categorize::RulesEngine`] from the config's mappings, regex mappings,
    /// and optionally the merchant dictionary. Each directive is enriched with
    /// categorization confidence, method, and a stable fingerprint.
    pub fn extract_string_enriched(
        &self,
        content: &str,
        csv_config: &CsvConfig,
    ) -> Result<EnrichedImportResult> {
        let result = self.extract_string(content, csv_config)?;

        // Build the rules engine once for all directives
        let mut engine = rustledger_ops::categorize::RulesEngine::new();
        engine.load_from_mappings(&csv_config.mappings);
        if !csv_config.regex_mappings.is_empty() {
            engine.load_from_regex_mappings(&csv_config.regex_mappings);
        }
        if csv_config.use_merchant_dict {
            engine.load_merchant_dict();
        }

        let entries = result
            .directives
            .into_iter()
            .enumerate()
            .map(|(i, directive)| {
                let enrichment = Self::enrich_directive(&directive, &engine, i);
                (directive, enrichment)
            })
            .collect();

        let mut enriched = EnrichedImportResult::new(entries);
        for warning in result.warnings {
            enriched = enriched.with_warning(warning);
        }
        Ok(enriched)
    }

    /// Build enrichment metadata for a single imported directive.
    fn enrich_directive(
        directive: &Directive,
        engine: &rustledger_ops::categorize::RulesEngine,
        index: usize,
    ) -> Enrichment {
        let (confidence, method) = if let Directive::Transaction(txn) = directive {
            let payee = txn.payee.as_ref().map(rustledger_core::InternedStr::as_str);
            if let Some(rule_match) = engine.categorize(payee, txn.narration.as_str()) {
                (rule_match.confidence, rule_match.method)
            } else {
                (0.0, CategorizationMethod::Default)
            }
        } else {
            (1.0, CategorizationMethod::Manual)
        };

        let fingerprint = crate::directive_fingerprint(directive);

        Enrichment {
            directive_index: index,
            confidence,
            method,
            alternatives: vec![],
            fingerprint,
        }
    }

    fn parse_row(
        &self,
        record: &csv::StringRecord,
        csv_config: &CsvConfig,
        header_map: &HashMap<String, usize>,
        row_num: usize,
    ) -> Result<Option<Transaction>> {
        // Get date
        let date_str = self
            .get_column(record, &csv_config.date_column, header_map)
            .with_context(|| format!("Row {row_num}: missing date column"))?;

        if date_str.trim().is_empty() {
            return Ok(None); // Skip empty rows
        }

        let date = jiff::fmt::strtime::parse(&csv_config.date_format, date_str.trim())
            .and_then(|tm| tm.to_date())
            .with_context(|| {
                format!(
                    "Row {}: failed to parse date '{}' with format '{}'",
                    row_num, date_str, csv_config.date_format
                )
            })?;

        // Get narration
        let narration = csv_config
            .narration_column
            .as_ref()
            .and_then(|col| self.get_column(record, col, header_map).ok())
            .map(|s| s.trim().to_string())
            .unwrap_or_default();

        // Get payee
        let payee = csv_config
            .payee_column
            .as_ref()
            .and_then(|col| self.get_column(record, col, header_map).ok())
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty());

        // Get amount
        let amount = self.parse_amount(record, csv_config, header_map)?;

        // Skip zero-amount rows by default. Users can opt out via
        // `skip_zero_amounts(false)` to preserve every source row (issue #972).
        if csv_config.skip_zero_amounts && amount == Decimal::ZERO {
            return Ok(None);
        }

        let final_amount = if csv_config.invert_sign {
            -amount
        } else {
            amount
        };

        let currency = self
            .config
            .currency
            .clone()
            .unwrap_or_else(|| "USD".to_string());

        // Create the transaction posting
        let amount = Amount::new(final_amount, &currency);
        let posting = Posting::new(&self.config.account, amount);

        // Create balancing posting (auto-interpolated)
        // Negative amounts = money leaving account = expenses
        // Positive amounts = money entering account = income
        let default_contra = if final_amount < Decimal::ZERO {
            csv_config
                .default_expense
                .as_deref()
                .unwrap_or("Expenses:Unknown")
        } else {
            csv_config
                .default_income
                .as_deref()
                .unwrap_or("Income:Unknown")
        };
        let contra_account = self
            .match_mapping(csv_config, payee.as_deref(), &narration)
            .unwrap_or(default_contra);
        let contra_posting = Posting::auto(contra_account);

        // Build the transaction
        let mut txn = Transaction::new(date, &narration)
            .with_flag('*')
            .with_posting(posting)
            .with_posting(contra_posting);

        if let Some(p) = payee {
            txn = txn.with_payee(p);
        }

        Ok(Some(txn))
    }

    /// Match payee/narration against configured mappings.
    /// Returns the mapped account name if a pattern matches, or None.
    /// Patterns are pre-lowercased at build time, so only the input fields
    /// need to be lowercased here.
    fn match_mapping<'a>(
        &self,
        csv_config: &'a CsvConfig,
        payee: Option<&str>,
        narration: &str,
    ) -> Option<&'a str> {
        if csv_config.mappings.is_empty() {
            return None;
        }

        let payee_lower = payee.map(str::to_lowercase);
        let narration_lower = narration.to_lowercase();

        for (pattern, account) in &csv_config.mappings {
            // Match against payee first, then narration
            if let Some(ref p) = payee_lower
                && p.contains(pattern.as_str())
            {
                return Some(account);
            }
            if narration_lower.contains(pattern.as_str()) {
                return Some(account);
            }
        }

        None
    }

    fn get_column<'a>(
        &self,
        record: &'a csv::StringRecord,
        spec: &ColumnSpec,
        header_map: &HashMap<String, usize>,
    ) -> Result<&'a str> {
        let index = match spec {
            ColumnSpec::Index(i) => *i,
            ColumnSpec::Name(name) => *header_map
                .get(name)
                .with_context(|| format!("Column '{name}' not found in header"))?,
        };

        record
            .get(index)
            .with_context(|| format!("Column index {index} out of bounds"))
    }

    fn parse_amount(
        &self,
        record: &csv::StringRecord,
        csv_config: &CsvConfig,
        header_map: &HashMap<String, usize>,
    ) -> Result<Decimal> {
        // If we have separate debit/credit columns
        if csv_config.debit_column.is_some() || csv_config.credit_column.is_some() {
            let mut amount = Decimal::ZERO;
            // Track whether ANY non-blank cell failed to parse. A blank cell
            // is normal (banks leave one of debit/credit blank), but a non-
            // blank cell that won't parse is a malformed row — surface it
            // instead of silently importing 0 (which becomes a real 0.00
            // transaction once `--include-zero-amounts` is set).
            let mut any_parse_failure = false;

            if let Some(debit_col) = &csv_config.debit_column
                && let Ok(debit_str) = self.get_column(record, debit_col, header_map)
                && !debit_str.trim().is_empty()
            {
                match self.config.amount_format.parse(debit_str) {
                    Ok(val) => amount -= val, // Debits are negative
                    Err(_) => any_parse_failure = true,
                }
            }

            if let Some(credit_col) = &csv_config.credit_column
                && let Ok(credit_str) = self.get_column(record, credit_col, header_map)
                && !credit_str.trim().is_empty()
            {
                match self.config.amount_format.parse(credit_str) {
                    Ok(val) => amount += val, // Credits are positive
                    Err(_) => any_parse_failure = true,
                }
            }

            // Strict: any non-blank cell that fails to parse is a malformed
            // row, regardless of what the other side produced. Returning a
            // half-credit value would silently mask the error (e.g. typo'd
            // debit "abc" + credit "100" would import as +100, dropping the
            // true debit).
            if any_parse_failure {
                anyhow::bail!("Failed to parse debit/credit amount");
            }

            return Ok(amount);
        }

        // Single amount column
        let amount_col = csv_config
            .amount_column
            .as_ref()
            .context("No amount column configured")?;

        let amount_str = self.get_column(record, amount_col, header_map)?;

        self.config
            .amount_format
            .parse(amount_str)
            .context("Failed to parse amount")
    }
}

#[cfg(test)]
mod tests {
    use format_num_pattern::{Locale, NumberFormat};

    use super::*;
    use crate::config::{AmountFormat, ImporterType};
    use std::str::FromStr;

    #[test]
    fn test_parse_money_string() {
        let amount_format = AmountFormat::default();

        assert_eq!(amount_format.parse("100.00").unwrap(), Decimal::from(100));
        assert_eq!(amount_format.parse("$100.00").unwrap(), Decimal::from(100));
        assert_eq!(
            amount_format.parse("1,234.56").unwrap(),
            Decimal::from_str("1234.56").unwrap()
        );
        assert_eq!(amount_format.parse("-50.00").unwrap(), Decimal::from(-50));
        assert_eq!(amount_format.parse("(50.00)").unwrap(), Decimal::from(-50));
        assert!(amount_format.parse("").is_err());
        assert!(amount_format.parse("N/A").is_err());
    }

    #[test]
    fn test_parse_custom_format() {
        let amount_format = AmountFormat::Format(NumberFormat::new("0,0,0,0.0").unwrap());

        assert_eq!(
            amount_format.parse("1,2,3,4.0").unwrap(),
            Decimal::from(1234)
        );

        assert_eq!(amount_format.parse("1,2,3,4").unwrap(), Decimal::from(1234));
        assert_eq!(amount_format.parse("1,2,3").unwrap(), Decimal::from(123));
        assert!(amount_format.parse("1,2,3.0").is_err(),);
    }

    #[test]
    fn test_csv_import_basic() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank:Checking")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .date_format("%m/%d/%Y")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
01/15/2024,Coffee Shop,-4.50
01/16/2024,Salary Deposit,2500.00
01/17/2024,Grocery Store,-85.23
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 3);
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn test_csv_import_debit_credit_columns() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank:Checking")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .debit_column("Debit")
            .credit_column("Credit")
            .date_format("%Y-%m-%d")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Debit,Credit
2024-01-15,Coffee Shop,4.50,
2024-01-16,Salary Deposit,,2500.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);

        // First transaction should be a debit (negative)
        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from_str("-4.50").unwrap());
        }

        // Second transaction should be a credit (positive)
        if let Directive::Transaction(txn) = &result.directives[1] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from_str("2500.00").unwrap());
        }
    }

    #[test]
    fn test_csv_import_malformed_debit_or_credit_warns() {
        // Per Copilot review on PR #982: a non-blank debit/credit cell that
        // fails to parse should surface as a warning, not silently become a
        // 0.00 (or half-valued) transaction. Blank cells remain normal.
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .debit_column("Debit")
            .credit_column("Credit")
            .build()
            .unwrap();

        // Both sides non-blank: debit malformed, credit valid. The credit-only
        // path would silently import +100 and drop the typo'd debit; we want
        // the row rejected with a warning instead.
        let csv = "Date,Description,Debit,Credit\n2024-01-15,Bad debit,abc,100.00\n";
        let result = config.extract_from_string(csv).unwrap();
        assert!(
            result.directives.is_empty(),
            "malformed debit must not produce a transaction"
        );
        assert_eq!(result.warnings.len(), 1);
        assert!(
            result.warnings[0].contains("parse"),
            "warning should mention parse failure: {}",
            result.warnings[0]
        );

        // Both blank: no warning (skipped as zero by default).
        let csv_blank = "Date,Description,Debit,Credit\n2024-01-15,Empty,,\n";
        let result = config.extract_from_string(csv_blank).unwrap();
        assert!(result.directives.is_empty());
        assert!(result.warnings.is_empty(), "blank cells must not warn");
    }

    #[test]
    fn test_csv_import_skip_rows() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .skip_rows(2)
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
Some header info
More info
2024-01-15,Coffee,-5.00
2024-01-16,Lunch,-10.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);
    }

    #[test]
    fn test_csv_import_invert_sign() {
        let config = ImporterConfig::csv()
            .account("Liabilities:CreditCard")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .invert_sign(true)
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Purchase,50.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from_str("-50.00").unwrap());
        }
    }

    #[test]
    fn test_csv_import_semicolon_delimiter() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("EUR")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .delimiter(';')
            .build()
            .unwrap();

        let csv_content = r"Date;Description;Amount
2024-01-15;Coffee;-5.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn test_csv_import_column_by_index() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column_index(0)
            .narration_column_index(1)
            .amount_column_index(2)
            .has_header(false)
            .build()
            .unwrap();

        let csv_content = r"2024-01-15,Coffee,-5.00
2024-01-16,Lunch,-10.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);
    }

    #[test]
    fn test_csv_import_with_payee() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .payee_column("Payee")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Payee,Description,Amount
2024-01-15,Coffee Shop,Morning coffee,-5.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.payee.as_deref(), Some("Coffee Shop"));
            assert_eq!(txn.narration.as_str(), "Morning coffee");
        }
    }

    #[test]
    fn test_csv_import_empty_csv() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n";

        let result = config.extract_from_string(csv_content).unwrap();
        assert!(result.directives.is_empty());
    }

    #[test]
    fn test_csv_import_with_currency_symbol() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Purchase,$100.00
2024-01-16,Refund,-$25.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from(100));
        }
    }

    #[test]
    fn test_csv_import_with_special_locale() {
        // da_DK locale uses '.' for thousands separation and ',' for decimals.
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .amount_locale(Locale::da_DK)
            .delimiter(';')
            .build()
            .unwrap();

        let csv_content = r"Date;Description;Amount
2024-01-15;Purchase;1.000,00
2024-01-16;Refund;-25.000.000,00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from(1000));
        }

        if let Directive::Transaction(txn) = &result.directives[1] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from(-25_000_000));
        }
    }

    #[test]
    fn test_csv_import_parentheses_negative() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Withdrawal,(50.00)
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from(-50));
        }
    }

    #[test]
    fn test_csv_import_comma_thousands() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r#"Date,Description,Amount
2024-01-15,Large deposit,"1,234.56"
"#;

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from_str("1234.56").unwrap());
        }
    }

    #[test]
    fn test_csv_importer_new() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .build()
            .unwrap();
        let importer = CsvImporter::new(config);
        // Verify construction succeeds by using the importer
        let empty_result = importer.extract_string("Date,Amount\n", &CsvConfig::default());
        assert!(empty_result.is_ok());
    }

    #[test]
    fn test_parse_money_string_edge_cases() {
        let amount_format = AmountFormat::default();
        // Whitespace
        assert_eq!(
            amount_format.parse("  100.00  ").unwrap(),
            Decimal::from(100)
        );
        // Empty after strip
        assert!(amount_format.parse("   ").is_err());
        // Just currency symbol
        assert!(amount_format.parse("$").is_err());
        // Negative with currency
        assert_eq!(
            amount_format.parse("-$100.00").unwrap(),
            Decimal::from(-100)
        );
    }

    #[test]
    fn test_csv_import_invalid_date_generates_warning() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
not-a-date,Coffee,-5.00
2024-01-15,Valid,-10.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        // Only the valid row should be imported
        assert_eq!(result.directives.len(), 1);
        // Should have a warning about the invalid date
        assert_eq!(result.warnings.len(), 1);
        assert!(result.warnings[0].contains("failed to parse date"));
    }

    #[test]
    fn test_csv_import_empty_date_skips_row() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
,Empty date row,-5.00
2024-01-15,Valid,-10.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        // Empty date row should be silently skipped
        assert_eq!(result.directives.len(), 1);
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn test_csv_import_zero_amount_skips_row() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Zero amount,0.00
2024-01-16,Valid,-10.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        // Zero amount row should be skipped
        assert_eq!(result.directives.len(), 1);
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.narration.as_str(), "Valid");
        }
    }

    #[test]
    fn test_csv_import_zero_amount_preserved_when_opted_in() {
        // Issue #972 follow-up: skip_zero_amounts(false) keeps the row.
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .skip_zero_amounts(false)
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Zero balance marker,0.00
2024-01-16,Normal,-10.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2, "both rows should be kept");
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.narration.as_str(), "Zero balance marker");
        }
    }

    #[test]
    fn test_csv_import_default_currency() {
        // No currency specified - should default to USD
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Coffee,-5.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.currency.as_str(), "USD");
        }
    }

    #[test]
    fn test_csv_import_income_contra_account() {
        // Negative amount = money out = expense, positive = money in = income
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Salary,2500.00
2024-01-16,Coffee,-5.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);

        // Positive amount (money in) -> Income:Unknown contra
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Income:Unknown");
        }

        // Negative amount (money out) -> Expenses:Unknown contra
        if let Directive::Transaction(txn) = &result.directives[1] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Unknown");
        }
    }

    #[test]
    fn test_csv_import_empty_payee_filtered() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .payee_column("Payee")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Payee,Description,Amount
2024-01-15,,Empty payee,-5.00
2024-01-16,  ,Whitespace payee,-10.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);

        // Empty payee should be None
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert!(txn.payee.is_none());
        }

        // Whitespace-only payee should also be None after trim
        if let Directive::Transaction(txn) = &result.directives[1] {
            assert!(txn.payee.is_none());
        }
    }

    #[test]
    fn test_csv_import_missing_column_error() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("NonExistentColumn")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Coffee,-5.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        // Row should fail with a warning
        assert!(result.directives.is_empty());
        assert_eq!(result.warnings.len(), 1);
        // The error propagates the "missing date column" context
        assert!(result.warnings[0].contains("missing date column"));
    }

    #[test]
    fn test_csv_import_column_index_out_of_bounds() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column_index(0)
            .narration_column_index(1)
            .amount_column_index(99) // Out of bounds
            .has_header(false)
            .build().unwrap();

        let csv_content = r"2024-01-15,Coffee,-5.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        // Row should fail with a warning
        assert!(result.directives.is_empty());
        assert_eq!(result.warnings.len(), 1);
        assert!(result.warnings[0].contains("out of bounds"));
    }

    #[test]
    fn test_csv_import_no_amount_column_error() {
        // Build manually to avoid default amount_column
        let csv_config = CsvConfig {
            date_column: ColumnSpec::Name("Date".to_string()),
            date_format: "%Y-%m-%d".to_string(),
            narration_column: Some(ColumnSpec::Name("Description".to_string())),
            payee_column: None,
            amount_column: None,
            amount_format: None,
            amount_locale: None,
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
        };

        let importer = CsvImporter::new(ImporterConfig {
            account: "Assets:Bank".to_string(),
            amount_format: AmountFormat::default(),
            currency: Some("USD".to_string()),
            importer_type: ImporterType::Csv(csv_config.clone()),
        });

        let csv_content = r"Date,Description
2024-01-15,Coffee
";

        let result = importer.extract_string(csv_content, &csv_config).unwrap();
        // Should have warning about no amount column
        assert!(result.directives.is_empty());
        assert_eq!(result.warnings.len(), 1);
        assert!(result.warnings[0].contains("No amount column"));
    }

    #[test]
    fn test_csv_import_debit_only_column() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .debit_column("Debit")
            // No credit column
            .build().unwrap();

        let csv_content = r"Date,Description,Debit
2024-01-15,Withdrawal,100.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            // Debit should be negative
            assert_eq!(amount.number, Decimal::from_str("-100.00").unwrap());
        }
    }

    #[test]
    fn test_csv_import_credit_only_column() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .credit_column("Credit")
            // No debit column
            .build().unwrap();

        let csv_content = r"Date,Description,Credit
2024-01-15,Deposit,100.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            // Credit should be positive
            assert_eq!(amount.number, Decimal::from_str("100.00").unwrap());
        }
    }

    #[test]
    fn test_csv_import_empty_debit_credit() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .debit_column("Debit")
            .credit_column("Credit")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Debit,Credit
2024-01-15,Empty both,,
";

        let result = config.extract_from_string(csv_content).unwrap();
        // Zero amount should be skipped
        assert!(result.directives.is_empty());
    }

    #[test]
    fn test_csv_import_with_positive_amount_sign() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let csv_content = r"Date,Description,Amount
2024-01-15,Deposit,+100.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from(100));
        }
    }

    #[test]
    fn test_csv_import_with_mappings() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .mappings(vec![
                ("WHOLE FOODS".to_string(), "Expenses:Groceries".to_string()),
                ("NETFLIX".to_string(), "Expenses:Entertainment".to_string()),
            ])
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n\
            2024-01-15,WHOLE FOODS MARKET #123,-50.00\n\
            2024-01-16,NETFLIX SUBSCRIPTION,-15.99\n\
            2024-01-17,RANDOM STORE,-25.00\n";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 3);

        // First transaction should map to Expenses:Groceries
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Groceries");
        } else {
            panic!("Expected transaction");
        }

        // Second should map to Expenses:Entertainment
        if let Directive::Transaction(txn) = &result.directives[1] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Entertainment");
        } else {
            panic!("Expected transaction");
        }

        // Third should fall back to Expenses:Unknown (negative = money out = expense)
        if let Directive::Transaction(txn) = &result.directives[2] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Unknown");
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_csv_import_mappings_case_insensitive() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .mappings(vec![(
                "amazon".to_string(),
                "Expenses:Shopping".to_string(),
            )])
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n\
            2024-01-15,AMAZON MARKETPLACE,-30.00\n";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Shopping");
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_csv_import_mappings_payee_priority() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .payee_column("Payee")
            .narration_column("Description")
            .amount_column("Amount")
            .mappings(vec![(
                "WALMART".to_string(),
                "Expenses:Shopping".to_string(),
            )])
            .build()
            .unwrap();

        let csv_content = "Date,Payee,Description,Amount\n\
            2024-01-15,Walmart,STORE #1234 PURCHASE,-75.00\n";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Shopping");
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_csv_import_custom_default_expense() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .default_expense("Expenses:Uncategorized")
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n\
            2024-01-15,Coffee Shop,-5.00\n";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        // Negative amount (money out) → expense side → should use custom default_expense
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Uncategorized");
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_csv_import_custom_default_income() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .default_income("Income:Other")
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n\
            2024-01-15,Deposit,100.00\n";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        // Positive amount (money in) → income side → should use custom default_income
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Income:Other");
        } else {
            panic!("Expected transaction");
        }
    }

    // ===== Enriched extraction tests =====

    #[test]
    fn test_enriched_extraction_basic() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let ImporterType::Csv(csv_config) = &config.importer_type;
        let csv_config = csv_config.clone();
        let importer = CsvImporter::new(config);

        let csv_content =
            "Date,Description,Amount\n2024-01-15,Coffee Shop,-5.00\n2024-01-16,Salary,2500.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &csv_config)
            .unwrap();
        assert_eq!(result.entries.len(), 2);

        // Each entry should have a directive and enrichment
        for (directive, enrichment) in &result.entries {
            assert!(matches!(
                directive,
                rustledger_core::Directive::Transaction(_)
            ));
            // Fingerprint should be present for transactions
            assert!(enrichment.fingerprint.is_some());
        }
    }

    #[test]
    fn test_enriched_confidence_mapping_match_vs_default() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .mappings(vec![("coffee".to_string(), "Expenses:Dining".to_string())])
            .build()
            .unwrap();

        let ImporterType::Csv(csv_config) = &config.importer_type;
        let csv_config = csv_config.clone();
        let importer = CsvImporter::new(config);

        let csv_content = "Date,Description,Amount\n2024-01-15,Coffee Shop,-5.00\n2024-01-16,Random Store,-10.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &csv_config)
            .unwrap();
        assert_eq!(result.entries.len(), 2);

        // First entry matches "coffee" rule → confidence 1.0
        let (_, enrichment0) = &result.entries[0];
        assert!((enrichment0.confidence - 1.0).abs() < f64::EPSILON);
        assert_eq!(
            enrichment0.method,
            rustledger_ops::enrichment::CategorizationMethod::Rule
        );

        // Second entry has no match → confidence 0.0, method Default
        let (_, enrichment1) = &result.entries[1];
        assert!((enrichment1.confidence - 0.0).abs() < f64::EPSILON);
        assert_eq!(
            enrichment1.method,
            rustledger_ops::enrichment::CategorizationMethod::Default
        );
    }

    #[test]
    fn test_enriched_merchant_dict_categorization() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .use_merchant_dict(true)
            .build()
            .unwrap();

        let ImporterType::Csv(csv_config) = &config.importer_type;
        let csv_config = csv_config.clone();
        let importer = CsvImporter::new(config);

        // Use a well-known merchant name that should be in the merchant dict
        let csv_content = "Date,Description,Amount\n2024-01-15,AMAZON,-50.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &csv_config)
            .unwrap();
        assert_eq!(result.entries.len(), 1);

        let (_, enrichment) = &result.entries[0];
        // If merchant dict has "amazon", confidence should be 1.0 and method MerchantDict.
        // If not, it falls back to Default with 0.0. Either way the enrichment is populated.
        assert!(enrichment.fingerprint.is_some());
        assert!(enrichment.confidence >= 0.0 && enrichment.confidence <= 1.0);
    }

    #[test]
    fn test_enriched_warnings_propagated() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();

        let ImporterType::Csv(csv_config) = &config.importer_type;
        let csv_config = csv_config.clone();
        let importer = CsvImporter::new(config);

        let csv_content =
            "Date,Description,Amount\nnot-a-date,Coffee,-5.00\n2024-01-15,Valid,-10.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &csv_config)
            .unwrap();
        // One valid entry, one warning
        assert_eq!(result.entries.len(), 1);
        assert_eq!(result.warnings.len(), 1);
        assert!(result.warnings[0].contains("failed to parse date"));
    }

    #[test]
    fn test_csv_import_empty_mappings() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .mappings(vec![])
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount\n\
            2024-01-15,Test,-10.00\n";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 1);

        // Should fall back to default (negative = expense)
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Unknown");
        } else {
            panic!("Expected transaction");
        }
    }
}
