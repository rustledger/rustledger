//! CSV file importer.

use crate::config::{AmountFormat, ColumnSpec, CsvConfig, ImporterConfig, ImporterType};
use crate::{EnrichedImportResult, ImportResult, Importer};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustc_hash::FxHashMap as HashMap;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_ops::enrichment::{CategorizationMethod, Enrichment};
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;

/// CSV file importer.
///
/// True unit struct — all parser state derives from the [`CsvConfig`]
/// passed to each helper or to [`Importer::extract`]. The compiled
/// [`AmountFormat`] (locale-and-pattern derived) is produced on the
/// fly from `CsvConfig::compile_amount_format()` at the start of each
/// extract call; per-row parse uses that compiled value.
///
/// The trait's [`Importer::extract_enriched`] is overridden here to
/// produce real categorization confidence via the rules engine, rather
/// than the cheap-default enrichment from the trait fallback.
// `Copy` is intentionally NOT derived: the trait `Importer` takes
// `&self` and clippy's `trivially_copy_pass_by_ref` would fire on
// every method. The struct has no fields anyway, so `Clone` is the
// useful capability.
#[derive(Debug, Default, Clone)]
pub struct CsvImporter;

impl Importer for CsvImporter {
    fn name(&self) -> &'static str {
        "CSV"
    }

    fn description(&self) -> &'static str {
        "Comma-separated values (CSV) file importer with configurable column mappings"
    }

    fn identify(&self, path: &Path) -> bool {
        path.extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("csv"))
    }

    fn extract(&self, path: &Path, config: &ImporterConfig) -> Result<ImportResult> {
        self.extract_file(path, config)
    }

    fn extract_enriched(
        &self,
        path: &Path,
        config: &ImporterConfig,
    ) -> Result<EnrichedImportResult> {
        self.extract_file_enriched(path, config)
    }
}

impl CsvImporter {
    /// Extract transactions from a file using the given importer config.
    pub fn extract_file(&self, path: &Path, config: &ImporterConfig) -> Result<ImportResult> {
        let file =
            File::open(path).with_context(|| format!("Failed to open file: {}", path.display()))?;
        let mut reader = BufReader::new(file);
        let mut content = String::new();
        reader.read_to_string(&mut content)?;
        self.extract_string(&content, config)
    }

    /// Extract transactions from string content using the given importer config.
    pub fn extract_string(&self, content: &str, config: &ImporterConfig) -> Result<ImportResult> {
        let ImporterType::Csv(csv_config) = &config.importer_type;
        // Build the categorization engine once and share it with the row loop —
        // the single source also used by the enriched path. `extract_string_enriched`
        // builds it once and reuses it for enrichment too, so the engine (which
        // compiles the merchant regexes) is never constructed twice per call.
        let engine = Self::build_rules_engine(csv_config);
        self.extract_string_with_engine(content, config, &engine)
    }

    /// Row-extraction core shared by [`Self::extract_string`] and
    /// [`Self::extract_string_enriched`], parameterized on a pre-built rules
    /// engine so it is constructed exactly once per extract call.
    fn extract_string_with_engine(
        &self,
        content: &str,
        config: &ImporterConfig,
        engine: &rustledger_ops::categorize::RulesEngine,
    ) -> Result<ImportResult> {
        // Irrefutable today because `ImporterType` has a single variant.
        // If a new variant is added the compiler will catch this as
        // refutable — that's intentional load-bearing safety; do NOT
        // "fix" it with `unreachable!()`. Return a typed error or
        // exhaustive match instead.
        let ImporterType::Csv(csv_config) = &config.importer_type;
        // Compile the amount parser once for the whole file. `NumberFormat::new`
        // is non-trivial and parse_row runs per row, so we'd repeat the
        // compile thousands of times if we did it inside the loop.
        let amount_format = csv_config.compile_amount_format()?;

        // Refuse up front rather than once per row: with no `currency` and no
        // `currency_column`, no row can say what it is denominated in.
        if config.currency.is_none() && csv_config.currency_column.is_none() {
            anyhow::bail!(
                "no currency configured: set `currency` on the importer (or a \
                 `currency_column`); there is no default currency"
            );
        }

        let mut reader = Self::reader(content, csv_config);

        // Build column name to index map from headers
        let header_map: HashMap<String, usize> = Self::read_header(&mut reader, csv_config)?
            .unwrap_or_default()
            .into_iter()
            .enumerate()
            .map(|(i, h)| (h, i))
            .collect();

        if let Some(id_col) = &csv_config.transaction_id_column {
            Self::check_transaction_id_column(id_col, csv_config, &header_map)?;
        }

        let mut directives = Vec::new();
        let mut warnings = Vec::new();
        let mut row_num = csv_config.skip_rows;
        // Rows per id link, to catch a `transaction_id_column` whose values
        // repeat. Dedup treats an equal id (with equal money) as the same
        // transaction on any date, so a column that is not unique per
        // transaction (a category, a type, a date) would make it match the
        // wrong rows.
        let mut id_rows: HashMap<String, Vec<usize>> = HashMap::default();

        for result in reader.records().skip(csv_config.skip_rows) {
            row_num += 1;
            let record = match result {
                Ok(r) => r,
                Err(e) => {
                    warnings.push(format!("Row {row_num}: parse error: {e}"));
                    continue;
                }
            };

            match self.parse_row(
                &record,
                config,
                csv_config,
                &amount_format,
                &header_map,
                engine,
            ) {
                Ok(Some(txn)) => {
                    if csv_config.transaction_id_column.is_some()
                        && let Some(link) = txn.links.iter().find(|l| {
                            l.as_str()
                                .starts_with(rustledger_ops::dedup::CSV_ID_LINK_PREFIX)
                        })
                    {
                        id_rows
                            .entry(link.as_str().to_string())
                            .or_default()
                            .push(row_num);
                    }
                    directives.push(Directive::Transaction(txn));
                }
                Ok(None) => {} // Skip empty rows
                Err(e) => {
                    warnings.push(format!("Row {row_num}: {e}"));
                }
            }
        }

        let mut repeated: Vec<(String, Vec<usize>)> = id_rows
            .into_iter()
            .filter(|(_, rows)| rows.len() > 1)
            .collect();
        if !repeated.is_empty() {
            repeated.sort_by_key(|(_, rows)| rows[0]);
            let (link, rows) = &repeated[0];
            let rows: Vec<String> = rows.iter().take(5).map(ToString::to_string).collect();
            warnings.push(format!(
                "{} transaction id(s) appear on more than one row (e.g. ^{link} on rows {}); \
                 `transaction_id_column` should name a column that is unique per \
                 transaction, or `extract --existing` may match the wrong rows",
                repeated.len(),
                rows.join(", "),
            ));
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
        config: &ImporterConfig,
    ) -> Result<EnrichedImportResult> {
        let file =
            File::open(path).with_context(|| format!("Failed to open file: {}", path.display()))?;
        let mut reader = BufReader::new(file);
        let mut content = String::new();
        reader.read_to_string(&mut content)?;
        self.extract_string_enriched(&content, config)
    }

    /// Extract transactions from string content with enrichment metadata.
    ///
    /// Builds a [`rustledger_ops::categorize::RulesEngine`] from the config's mappings, regex mappings,
    /// and optionally the merchant dictionary. Each directive is enriched with
    /// categorization confidence, method, and a stable fingerprint.
    pub fn extract_string_enriched(
        &self,
        content: &str,
        config: &ImporterConfig,
    ) -> Result<EnrichedImportResult> {
        let ImporterType::Csv(csv_config) = &config.importer_type;

        // Build the rules engine ONCE and use it for both row extraction and
        // enrichment, instead of building it inside `extract_string` and again
        // here (the engine compiles the merchant regexes).
        let engine = Self::build_rules_engine(csv_config);
        let result = self.extract_string_with_engine(content, config, &engine)?;

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
        config: &ImporterConfig,
        csv_config: &CsvConfig,
        amount_format: &AmountFormat,
        header_map: &HashMap<String, usize>,
        engine: &rustledger_ops::categorize::RulesEngine,
    ) -> Result<Option<Transaction>> {
        // Get date. No `Row N:` prefix on these errors: `parse_row`'s caller
        // already wraps every error it returns with `Row {row_num}: {e}`, so
        // prefixing here too produced a doubled `Row 1: Row 1: ...`.
        let date_str = self
            .get_column(record, &csv_config.date_column, header_map)
            .with_context(|| "missing date column".to_string())?;

        if date_str.trim().is_empty() {
            return Ok(None); // Skip empty rows
        }

        let date = jiff::fmt::strtime::parse(&csv_config.date_format, date_str.trim())
            .and_then(|tm| tm.to_date())
            .with_context(|| {
                format!(
                    "failed to parse date '{}' with format '{}'",
                    date_str, csv_config.date_format
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
        let amount = self.parse_amount(record, csv_config, amount_format, header_map)?;

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

        // Per-row currency from a currency column (e.g. multi-currency
        // exports). A configured column that can't be read is a config error
        // (wrong name/index) — surface it rather than silently falling back,
        // which would reintroduce the "multi-currency becomes mono-currency"
        // bug. A blank cell is legitimate and falls back to the default.
        //
        // There is no built-in default currency. One used to be `USD`, which
        // booked every row of a euro account's statement in dollars without a
        // word when the config named no currency (#2464). A row whose currency
        // nothing states is refused instead.
        let default_currency = || {
            config
                .currency
                .clone()
                .context("no currency: the row has none and the importer config sets no `currency`")
        };
        let currency = match &csv_config.currency_column {
            Some(col) => {
                let cell = self
                    .get_column(record, col, header_map)
                    .context("failed to read configured currency column")?;
                let cell = cell.trim();
                if cell.is_empty() {
                    default_currency()?
                } else {
                    cell.to_string()
                }
            }
            None => default_currency()?,
        };

        // Create the transaction posting
        let amount = Amount::new(final_amount, &currency);
        let posting = Posting::new(&config.account, amount);

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
        // Borrow the matched account (or the default) as `&str` — no per-row
        // `String` allocation when a rule doesn't match.
        let rule_match = engine.categorize(payee.as_deref(), &narration);
        let contra_account = rule_match
            .as_ref()
            .map_or(default_contra, |m| m.account.as_str());
        let contra_posting = Posting::auto(contra_account);

        // Build the transaction
        let mut txn = Transaction::new(date, &narration)
            .with_flag('*')
            .with_synthesized_posting(posting)
            .with_synthesized_posting(contra_posting);

        if let Some(p) = payee {
            txn = txn.with_payee(p);
        }

        // Preserve a second date column (e.g. a value date alongside the
        // booking date) as transaction metadata so the timestamp isn't dropped
        // (#1623). A missing/unparseable secondary value is skipped silently
        // rather than failing the row — it is supplementary, not the txn date.
        if let Some(sd) = &csv_config.secondary_date
            && let Ok(raw) = self.get_column(record, &sd.column, header_map)
        {
            let raw = raw.trim();
            if !raw.is_empty()
                && let Some(d) = jiff::fmt::strtime::parse(&sd.format, raw)
                    .ok()
                    .and_then(|tm| tm.to_date().ok())
            {
                txn.meta
                    .insert(sd.meta_key.clone(), rustledger_core::MetaValue::Date(d));
            }
        }

        // A source-assigned transaction id becomes a `^csv-<id>` link (#2387),
        // the CSV counterpart of OFX's `^ofx-<FITID>`: dedup trusts an equal
        // id link as identity. A configured column that cannot be read is a
        // config error, like `currency_column`; a blank cell adds no link.
        if let Some(col) = &csv_config.transaction_id_column {
            let cell = self
                .get_column(record, col, header_map)
                .context("failed to read configured transaction id column")?;
            if let Some(link) =
                rustledger_ops::dedup::id_link(rustledger_ops::dedup::CSV_ID_LINK_PREFIX, cell)
            {
                txn = txn.with_link(link);
            }
        }

        Ok(Some(txn))
    }

    /// The CSV reader every pass over a file uses, so the header that
    /// [`Self::header`] reports is the header extraction reads.
    fn reader<'a>(content: &'a str, csv_config: &CsvConfig) -> csv::Reader<&'a [u8]> {
        csv::ReaderBuilder::new()
            .has_headers(csv_config.has_header)
            .delimiter(csv_config.delimiter as u8)
            .from_reader(content.as_bytes())
    }

    /// The header row's column names, in order, or `None` for a headerless
    /// config.
    fn read_header(
        reader: &mut csv::Reader<&[u8]>,
        csv_config: &CsvConfig,
    ) -> Result<Option<Vec<String>>> {
        if !csv_config.has_header {
            return Ok(None);
        }
        Ok(Some(
            reader.headers()?.iter().map(ToString::to_string).collect(),
        ))
    }

    /// The column names of `content`'s header row as extraction would read
    /// them under `csv_config` (its delimiter and `has_header`; `skip_rows`
    /// skips data rows after the header, so it does not move the header), or
    /// `None` when the config says the file has no header.
    ///
    /// For choosing between importer entries by the columns a file has
    /// (#2295): it shares the reader with extraction, so a column this
    /// reports is one a column name in the config will find.
    ///
    /// # Errors
    ///
    /// Returns an error when the header row is not valid CSV.
    pub fn header(content: &str, csv_config: &CsvConfig) -> Result<Option<Vec<String>>> {
        Self::read_header(&mut Self::reader(content, csv_config), csv_config)
    }

    /// Misconfigurations of `transaction_id_column` caught once, up front,
    /// with a message naming the key, rather than as one context-free warning
    /// per row followed by "no transactions were extracted" (or, worse, as
    /// links that make `extract --existing` match the wrong rows):
    ///
    /// - a name the header lacks, with a hint when it differs from a header
    ///   only in case or surrounding whitespace;
    /// - an index past the header's last column;
    /// - the same column as one the importer already reads for something else
    ///   (`amount_column`, `date_column`, ...): those values are not unique per
    ///   transaction, and id dedup trusts an equal id with equal money as the
    ///   same transaction on any date.
    fn check_transaction_id_column(
        id_col: &ColumnSpec,
        csv_config: &CsvConfig,
        header_map: &HashMap<String, usize>,
    ) -> Result<()> {
        if !csv_config.has_header {
            return Ok(());
        }
        let mut columns: Vec<(&String, &usize)> = header_map.iter().collect();
        columns.sort_by_key(|(_, i)| **i);
        let names: Vec<&str> = columns.iter().map(|(n, _)| n.as_str()).collect();
        let index = match id_col {
            ColumnSpec::Name(name) => {
                let Some(i) = header_map.get(name) else {
                    let close = names
                        .iter()
                        .find(|h| h.trim().eq_ignore_ascii_case(name.trim()));
                    let hint = close.map_or(String::new(), |h| format!("; did you mean {h:?}?"));
                    anyhow::bail!(
                        "transaction_id_column {name:?} is not a column of this file \
                         (its columns: {}){hint}",
                        names.join(", ")
                    );
                };
                *i
            }
            ColumnSpec::Index(i) => {
                if *i >= names.len() {
                    anyhow::bail!(
                        "transaction_id_column {i} is past the last column of this file \
                         (it has {} columns, numbered from 0)",
                        names.len()
                    );
                }
                *i
            }
        };
        let resolve = |spec: &ColumnSpec| match spec {
            ColumnSpec::Name(n) => header_map.get(n).copied(),
            ColumnSpec::Index(i) => Some(*i),
        };
        let others = [
            ("date_column", Some(&csv_config.date_column)),
            ("amount_column", csv_config.amount_column.as_ref()),
            ("debit_column", csv_config.debit_column.as_ref()),
            ("credit_column", csv_config.credit_column.as_ref()),
            ("narration_column", csv_config.narration_column.as_ref()),
            ("payee_column", csv_config.payee_column.as_ref()),
            ("currency_column", csv_config.currency_column.as_ref()),
            (
                "secondary_date_column",
                csv_config.secondary_date.as_ref().map(|s| &s.column),
            ),
        ];
        for (key, spec) in others {
            if spec.and_then(resolve) == Some(index) {
                anyhow::bail!(
                    "transaction_id_column names the same column as `{key}` ({:?}); \
                     it must be a column whose value is unique per transaction",
                    names[index]
                );
            }
        }
        Ok(())
    }

    /// Build the categorization [`rustledger_ops::categorize::RulesEngine`] from
    /// a CSV config — the single source consulted by BOTH the plain
    /// (`extract`/`extract_string`) and enriched (`extract_string_enriched`)
    /// paths. Loads, in priority order: the config's exact mappings (substring,
    /// lowercased), its regex mappings, and the built-in merchant dictionary
    /// (when `use_merchant_dict`). Previously the plain path used a bespoke
    /// matcher that silently skipped `regex_mappings`.
    fn build_rules_engine(csv_config: &CsvConfig) -> rustledger_ops::categorize::RulesEngine {
        let mut engine = rustledger_ops::categorize::RulesEngine::new();
        engine.load_from_mappings(&csv_config.mappings);
        if !csv_config.regex_mappings.is_empty() {
            engine.load_from_regex_mappings(&csv_config.regex_mappings);
        }
        if csv_config.use_merchant_dict {
            engine.load_merchant_dict();
        }
        engine
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
        amount_format: &AmountFormat,
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
                match amount_format.parse(debit_str) {
                    Ok(val) => amount -= val, // Debits are negative
                    Err(_) => any_parse_failure = true,
                }
            }

            if let Some(credit_col) = &csv_config.credit_column
                && let Ok(credit_str) = self.get_column(record, credit_col, header_map)
                && !credit_str.trim().is_empty()
            {
                match amount_format.parse(credit_str) {
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

        amount_format
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

    /// `header` reads the header row with the config's delimiter, and is
    /// `None` for a headerless config.
    #[test]
    fn header_reads_the_row_extraction_reads() {
        let semicolons = CsvConfig {
            delimiter: ';',
            ..CsvConfig::default()
        };
        assert_eq!(
            CsvImporter::header("Date;Amount (EUR)\n2024-01-01;1\n", &semicolons).unwrap(),
            Some(vec!["Date".to_string(), "Amount (EUR)".to_string()])
        );
        let headerless = CsvConfig {
            has_header: false,
            ..CsvConfig::default()
        };
        assert_eq!(
            CsvImporter::header("2024-01-01,1\n", &headerless).unwrap(),
            None
        );
    }

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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        assert_eq!(result.directives.len(), 3);
        assert!(result.warnings.is_empty());
    }

    #[test]
    fn test_csv_import_preserves_secondary_date() {
        // A statement with both a booking date and a value date: the booking
        // date is the directive date, the value date is preserved as metadata
        // instead of being silently dropped (#1623).
        let config = ImporterConfig::csv()
            .account("Assets:Bank:Checking")
            .currency("USD")
            .date_column("Booking Date")
            .narration_column("Description")
            .amount_column("Amount")
            .date_format("%Y-%m-%d")
            .secondary_date("Value Date", "%Y-%m-%d", "value_date")
            .build()
            .unwrap();

        let csv_content = r"Booking Date,Description,Value Date,Amount
2024-01-15,Coffee Shop,2024-01-17,-4.50
";
        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        assert_eq!(result.directives.len(), 1);
        let Directive::Transaction(txn) = &result.directives[0] else {
            panic!("expected a transaction");
        };
        assert_eq!(txn.date.to_string(), "2024-01-15");
        match txn.meta.get("value_date") {
            Some(rustledger_core::MetaValue::Date(d)) => assert_eq!(d.to_string(), "2024-01-17"),
            other => panic!("expected value_date metadata, got {other:?}"),
        }
    }

    /// #2464: there is no built-in currency. A config naming none, with no
    /// currency column, is refused; a blank currency cell with no default is
    /// a row error. Neither becomes USD.
    #[test]
    fn test_csv_import_without_a_currency_is_refused() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap();
        let csv = "Date,Description,Amount\n2024-01-15,Coffee,-4.50\n";
        let err = CsvImporter.extract_string(csv, &config).unwrap_err();
        assert!(err.to_string().contains("no currency configured"), "{err}");

        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .currency_column("Ccy")
            .build()
            .unwrap();
        let csv =
            "Date,Description,Amount,Ccy\n2024-01-15,Coffee,-4.50,EUR\n2024-01-16,Tea,-2.00,\n";
        let result = CsvImporter.extract_string(csv, &config).unwrap();
        assert_eq!(result.directives.len(), 1);
        assert!(
            result.warnings[0].contains("no currency"),
            "{:?}",
            result.warnings
        );
    }

    #[test]
    fn test_csv_import_transaction_id_becomes_a_link() {
        // #2387: the id column becomes a `^csv-` link, sanitized to the link
        // charset; a blank cell adds none.
        let config = ImporterConfig::csv()
            .account("Assets:Monzo")
            .currency("GBP")
            .transaction_id_column("Transaction ID")
            .build()
            .unwrap();
        let csv_content = "Transaction ID,Date,Description,Amount\n\
                           tx_00A1,2024-01-15,Coffee,-4.50\n\
                           a b:c,2024-01-15,Tea,-2.00\n\
                           ,2024-01-16,Cake,-3.00\n";
        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        let links: Vec<Vec<String>> = result
            .directives
            .iter()
            .map(|d| match d {
                Directive::Transaction(t) => {
                    t.links.iter().map(|l| l.as_str().to_string()).collect()
                }
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(
            links,
            vec![
                vec!["csv-tx_00A1".to_string()],
                vec!["csv-a-b-c".to_string()],
                vec![]
            ]
        );

        // A configured column the file does not have is a config error, not
        // a silent "no ids" (see the up-front check's own test).
        let csv_content = "Date,Description,Amount\n2024-01-15,Coffee,-4.50\n";
        assert!(CsvImporter.extract_string(csv_content, &config).is_err());
    }

    /// A CSV saved on Windows (CRLF line ends, a stray trailing space) still
    /// yields clean id links: no `\r` and no separator leaks into the link.
    #[test]
    fn test_csv_import_transaction_id_survives_crlf() {
        let config = ImporterConfig::csv()
            .account("Assets:Monzo")
            .currency("GBP")
            .transaction_id_column("Id")
            .build()
            .unwrap();
        let csv_content = "Id,Date,Description,Amount\r\ntx_1,2024-01-15,Coffee,-4.50\r\ntx_2 ,2024-01-15,Tea,-2.00\r\n";
        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        let links: Vec<String> = result
            .directives
            .iter()
            .filter_map(|d| match d {
                Directive::Transaction(t) => t.links.first().map(|l| l.as_str().to_string()),
                _ => None,
            })
            .collect();
        assert_eq!(links, ["csv-tx_1", "csv-tx_2"]);
    }

    /// A `transaction_id_column` the header lacks fails once, naming the
    /// column and the file's columns, instead of one warning per row.
    #[test]
    fn test_csv_import_missing_transaction_id_column_fails_up_front() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("EUR")
            .transaction_id_column("Id")
            .build()
            .unwrap();
        let csv = "Date,Description,Amount\n2024-01-15,Coffee,-4.50\n2024-01-16,Tea,-2.00\n";
        let err = CsvImporter
            .extract_string(csv, &config)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("transaction_id_column \"Id\" is not a column of this file (its columns: Date, Description, Amount)"),
            "{err}"
        );
    }

    /// Misconfigured id columns fail once with a message naming the key: a
    /// near-miss name gets a hint, an index past the end is caught, and a
    /// column already read for something else is refused.
    #[test]
    fn test_csv_import_misconfigured_transaction_id_column() {
        let csv = "Id,Date,Description,Amount\nt1,2024-01-15,Coffee,-4.50\n";
        let err = |col: ColumnSpec| {
            let mut config = ImporterConfig::csv()
                .account("Assets:Bank")
                .currency("EUR")
                .build()
                .unwrap();
            let ImporterType::Csv(c) = &mut config.importer_type;
            c.transaction_id_column = Some(col);
            CsvImporter
                .extract_string(csv, &config)
                .unwrap_err()
                .to_string()
        };
        let e = err(ColumnSpec::Name(" id".into()));
        assert!(e.ends_with("; did you mean \"Id\"?"), "{e}");
        let e = err(ColumnSpec::Index(9));
        assert!(
            e.contains(
                "transaction_id_column 9 is past the last column of this file (it has 4 columns"
            ),
            "{e}"
        );
        let e = err(ColumnSpec::Name("Amount".into()));
        assert!(
            e.contains(
                "transaction_id_column names the same column as `amount_column` (\"Amount\")"
            ),
            "{e}"
        );
        let e = err(ColumnSpec::Index(1));
        assert!(
            e.contains("the same column as `date_column` (\"Date\")"),
            "{e}"
        );
    }

    /// Ids that repeat within one statement are reported: a column that is
    /// not unique per transaction would make id dedup match the wrong rows.
    #[test]
    fn test_csv_import_warns_on_repeated_transaction_ids() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("EUR")
            .transaction_id_column("Kind")
            .build()
            .unwrap();
        let csv = "Kind,Date,Description,Amount\nfood,2024-01-15,Coffee,-4.50\nrent,2024-01-15,Rent,-900\n\
                   food,2024-01-16,Tea,-2.00\nrent,2024-02-15,Rent,-900\nx1,2024-02-16,Cake,-3\n";
        let result = CsvImporter.extract_string(csv, &config).unwrap();
        assert_eq!(result.directives.len(), 5);
        assert_eq!(result.warnings.len(), 1, "{:?}", result.warnings);
        assert!(
            result.warnings[0].starts_with(
                "2 transaction id(s) appear on more than one row (e.g. ^csv-food on rows 1, 3)"
            ),
            "{:?}",
            result.warnings
        );

        // Unique ids, and blank cells, warn about nothing.
        let csv = "Kind,Date,Description,Amount\na,2024-01-15,Coffee,-4.50\n,2024-01-16,Tea,-2.00\n,2024-01-17,Cake,-3\n";
        assert!(
            CsvImporter
                .extract_string(csv, &config)
                .unwrap()
                .warnings
                .is_empty()
        );
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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
        let result = CsvImporter.extract_string(csv, &config).unwrap();
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
        let result = CsvImporter.extract_string(csv_blank, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        assert_eq!(result.directives.len(), 2);

        if let Directive::Transaction(txn) = &result.directives[0] {
            let amount = txn.postings[0].amount().unwrap();
            assert_eq!(amount.number, Decimal::from(100));
        }
    }

    #[test]
    fn test_csv_import_per_row_currency_column() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .currency_column("Currency")
            .build()
            .unwrap();

        // Row 3 has a blank currency cell → falls back to the config default.
        let csv_content = "Date,Description,Amount,Currency\n\
2024-01-02,Coffee,-5.00,EUR\n\
2024-01-05,Salary,2000.00,USD\n\
2024-01-08,NoCcy,1.00,\n";

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        assert_eq!(result.directives.len(), 3);
        let ccy = |i: usize| match &result.directives[i] {
            Directive::Transaction(txn) => txn.postings[0].amount().unwrap().currency.clone(),
            _ => panic!("expected transaction"),
        };
        assert_eq!(ccy(0), "EUR");
        assert_eq!(ccy(1), "USD");
        assert_eq!(ccy(2), "USD", "blank currency cell falls back to default");
    }

    #[test]
    fn test_csv_import_missing_currency_column_warns_not_silent() {
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .currency_column("Nonexistent")
            .build()
            .unwrap();

        let csv_content = "Date,Description,Amount,Currency\n2024-01-02,Coffee,-5.00,EUR\n";
        let result = CsvImporter.extract_string(csv_content, &config).unwrap();

        // A misconfigured currency column must NOT silently fall back to the
        // default currency; the row is rejected with a warning instead.
        assert!(result.directives.is_empty());
        assert!(
            result
                .warnings
                .iter()
                .any(|w| w.to_lowercase().contains("currency")),
            "expected a currency-column warning, got {:?}",
            result.warnings
        );
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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
            .currency("USD")
            .build()
            .unwrap();
        let importer = CsvImporter;
        // Verify construction succeeds by using the importer
        let empty_result = importer.extract_string("Date,Amount\n", &config);
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        assert_eq!(result.directives.len(), 2, "both rows should be kept");
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.narration.as_str(), "Zero balance marker");
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        // Row should fail with a warning
        assert!(result.directives.is_empty());
        assert_eq!(result.warnings.len(), 1);
        // The error propagates the "missing date column" context
        assert!(result.warnings[0].contains("missing date column"));
        // ...with exactly one `Row N:` prefix, not the doubled
        // `Row 1: Row 1: ...` the inner+outer prefixes used to produce.
        assert_eq!(
            result.warnings[0].matches("Row ").count(),
            1,
            "row prefix must not be doubled: {:?}",
            result.warnings[0]
        );
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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
            currency_column: None,
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
            secondary_date: None,
            transaction_id_column: None,
        };

        let importer = CsvImporter;
        let config = ImporterConfig {
            account: "Assets:Bank".to_string(),
            currency: Some("USD".to_string()),
            importer_type: ImporterType::Csv(csv_config),
        };

        let csv_content = r"Date,Description
2024-01-15,Coffee
";

        let result = importer.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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
    fn test_merchant_dict_categorizes_account_when_enabled() {
        // Regression for OUTSTANDING #20: with use_merchant_dict, the regular
        // extract path (used by the CLI) must apply the dictionary's account,
        // not leave a known merchant at the default expense account.
        let account_for = |description: &str, enable: bool| -> String {
            let config = ImporterConfig::csv()
                .account("Assets:Bank")
                .currency("USD")
                .date_column("Date")
                .narration_column("Description")
                .amount_column("Amount")
                .use_merchant_dict(enable)
                .build()
                .unwrap();
            let csv = format!("Date,Description,Amount\n2024-03-08,{description},-15.99\n");
            let result = CsvImporter.extract_string(&csv, &config).unwrap();
            match &result.directives[0] {
                Directive::Transaction(txn) => txn.postings[1].account.as_str().to_string(),
                _ => panic!("expected transaction"),
            }
        };
        assert_eq!(
            account_for("NETFLIX.COM", false),
            "Expenses:Unknown",
            "disabled stays default"
        );
        assert_eq!(
            account_for("NETFLIX.COM", true),
            "Expenses:Subscriptions:Streaming",
            "enabled: NETFLIX maps to the merchant-dict account"
        );
        // An `AMAZON|AMZN`-style alternation pattern must match too — a plain
        // substring match would miss the second alternative entirely.
        assert_eq!(
            account_for("AMZN MKTP US", true),
            "Expenses:Shopping:Amazon",
            "enabled: AMZN matches the AMAZON|AMZN alternation pattern"
        );
    }

    #[test]
    fn test_regex_mappings_categorize_on_plain_path_and_match_enriched() {
        // Regression: the plain `extract`/`extract_string` path (used by the
        // CLI) previously ignored `regex_mappings` entirely — a regex-matched
        // row landed at the default account instead of its mapped one — while
        // the enriched path honored them. Both now share one RulesEngine and
        // must agree.
        let config = ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .regex_mappings(vec![(
                "STARBUCKS|SBUX".to_string(),
                "Expenses:Coffee".to_string(),
            )])
            .build()
            .unwrap();
        // "SBUX" matches only the regex alternation, not a plain substring of
        // "STARBUCKS" — the exact case the plain path used to drop.
        let csv = "Date,Description,Amount\n2024-03-08,SBUX STORE #123,-4.50\n";

        let plain = CsvImporter.extract_string(csv, &config).unwrap();
        let plain_account = match &plain.directives[0] {
            Directive::Transaction(txn) => txn.postings[1].account.as_str().to_string(),
            _ => panic!("expected transaction"),
        };
        assert_eq!(
            plain_account, "Expenses:Coffee",
            "plain path must honor regex_mappings (SBUX -> Expenses:Coffee)"
        );

        let enriched = CsvImporter.extract_string_enriched(csv, &config).unwrap();
        let enriched_account = match &enriched.entries[0].0 {
            Directive::Transaction(txn) => txn.postings[1].account.as_str().to_string(),
            _ => panic!("expected transaction"),
        };
        assert_eq!(
            plain_account, enriched_account,
            "plain and enriched contra-accounts must agree"
        );
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
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
        let importer = CsvImporter;

        let csv_content =
            "Date,Description,Amount\n2024-01-15,Coffee Shop,-5.00\n2024-01-16,Salary,2500.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &config)
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
        let importer = CsvImporter;

        let csv_content = "Date,Description,Amount\n2024-01-15,Coffee Shop,-5.00\n2024-01-16,Random Store,-10.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &config)
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
        let importer = CsvImporter;

        // Use a well-known merchant name that should be in the merchant dict
        let csv_content = "Date,Description,Amount\n2024-01-15,AMAZON,-50.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &config)
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
        let importer = CsvImporter;

        let csv_content =
            "Date,Description,Amount\nnot-a-date,Coffee,-5.00\n2024-01-15,Valid,-10.00\n";

        let result = importer
            .extract_string_enriched(csv_content, &config)
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

        let result = CsvImporter.extract_string(csv_content, &config).unwrap();
        assert_eq!(result.directives.len(), 1);

        // Should fall back to default (negative = expense)
        if let Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Unknown");
        } else {
            panic!("Expected transaction");
        }
    }
}
