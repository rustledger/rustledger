//! CSV file importer.

use crate::ImportResult;
use crate::config::{ColumnSpec, CsvConfig, ImporterConfig};
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

        let csv_content = r#"Date,Description,Amount
01/15/2024,Coffee Shop,-4.50
01/16/2024,Salary Deposit,2500.00
01/17/2024,Grocery Store,-85.23
"#;

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

        let csv_content = r#"Date,Description,Debit,Credit
2024-01-15,Coffee Shop,4.50,
2024-01-16,Salary Deposit,,2500.00
"#;

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
}
