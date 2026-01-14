//! CSV file importer.

use crate::config::{ColumnSpec, CsvConfig, ImporterConfig};
use crate::ImportResult;
use anyhow::{Context, Result};
use chrono::NaiveDate;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;
use std::str::FromStr;

#[allow(unused_imports)]
use rustledger_core::InternedStr;

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

        let date = NaiveDate::parse_from_str(date_str.trim(), &csv_config.date_format)
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

        // Skip zero amount transactions
        if amount == Decimal::ZERO {
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
        let contra_account = if final_amount < Decimal::ZERO {
            "Income:Unknown"
        } else {
            "Expenses:Unknown"
        };
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

            if let Some(debit_col) = &csv_config.debit_column {
                if let Ok(debit_str) = self.get_column(record, debit_col, header_map) {
                    if let Some(val) = parse_money_string(debit_str) {
                        amount -= val; // Debits are negative
                    }
                }
            }

            if let Some(credit_col) = &csv_config.credit_column {
                if let Ok(credit_str) = self.get_column(record, credit_col, header_map) {
                    if let Some(val) = parse_money_string(credit_str) {
                        amount += val; // Credits are positive
                    }
                }
            }

            return Ok(amount);
        }

        // Single amount column
        let amount_col = csv_config
            .amount_column
            .as_ref()
            .context("No amount column configured")?;

        let amount_str = self.get_column(record, amount_col, header_map)?;
        parse_money_string(amount_str).context("Failed to parse amount")
    }
}

/// Parse a money string, handling currency symbols, parentheses for negatives, etc.
fn parse_money_string(s: &str) -> Option<Decimal> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }

    // Check for parentheses indicating negative
    let (is_negative, s) = if s.starts_with('(') && s.ends_with(')') {
        (true, &s[1..s.len() - 1])
    } else {
        (false, s)
    };

    // Remove currency symbols and commas
    let cleaned: String = s
        .chars()
        .filter(|c| c.is_ascii_digit() || *c == '.' || *c == '-' || *c == '+')
        .collect();

    if cleaned.is_empty() {
        return None;
    }

    let value = Decimal::from_str(&cleaned).ok()?;

    if is_negative {
        Some(-value)
    } else {
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::ImporterType;

    #[test]
    fn test_parse_money_string() {
        assert_eq!(parse_money_string("100.00"), Some(Decimal::from(100)));
        assert_eq!(parse_money_string("$100.00"), Some(Decimal::from(100)));
        assert_eq!(
            parse_money_string("1,234.56"),
            Some(Decimal::from_str("1234.56").unwrap())
        );
        assert_eq!(parse_money_string("-50.00"), Some(Decimal::from(-50)));
        assert_eq!(parse_money_string("(50.00)"), Some(Decimal::from(-50)));
        assert_eq!(parse_money_string(""), None);
        assert_eq!(parse_money_string("N/A"), None);
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
            .build();

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
            .build();

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
    fn test_csv_import_skip_rows() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .skip_rows(2)
            .build();

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
            .build();

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
            .build();

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
            .build();

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
            .build();

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
            .build();

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
            .build();

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
    fn test_csv_import_parentheses_negative() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build();

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
            .build();

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
        let config = ImporterConfig::csv().account("Assets:Bank").build();
        let importer = CsvImporter::new(config);
        // Verify construction succeeds by using the importer
        let empty_result = importer.extract_string("Date,Amount\n", &CsvConfig::default());
        assert!(empty_result.is_ok());
    }

    #[test]
    fn test_parse_money_string_edge_cases() {
        // Whitespace
        assert_eq!(parse_money_string("  100.00  "), Some(Decimal::from(100)));
        // Empty after strip
        assert_eq!(parse_money_string("   "), None);
        // Just currency symbol
        assert_eq!(parse_money_string("$"), None);
        // Negative with currency
        assert_eq!(parse_money_string("-$100.00"), Some(Decimal::from(-100)));
    }

    #[test]
    fn test_csv_import_invalid_date_generates_warning() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build();

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
            .build();

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
            .build();

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
    fn test_csv_import_default_currency() {
        // No currency specified - should default to USD
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build();

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
        // Negative final amount should use Income:Unknown as contra
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build();

        let csv_content = r"Date,Description,Amount
2024-01-15,Salary,2500.00
2024-01-16,Coffee,-5.00
";

        let result = config.extract_from_string(csv_content).unwrap();
        assert_eq!(result.directives.len(), 2);

        // Positive amount -> Expenses:Unknown contra
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Unknown");
        }

        // Negative amount -> Income:Unknown contra
        if let Directive::Transaction(txn) = &result.directives[1] {
            assert_eq!(txn.postings[1].account.as_str(), "Income:Unknown");
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
            .build();

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
            .build();

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
            .build();

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
            debit_column: None,
            credit_column: None,
            has_header: true,
            delimiter: ',',
            skip_rows: 0,
            invert_sign: false,
        };

        let importer = CsvImporter::new(ImporterConfig {
            account: "Assets:Bank".to_string(),
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
            .build();

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
            .build();

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
            .build();

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
            .build();

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
}
