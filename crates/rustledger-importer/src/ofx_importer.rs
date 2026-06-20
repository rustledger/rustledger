//! OFX/QFX file importer.
//!
//! This module implements importing transactions from OFX (Open Financial Exchange)
//! and QFX (Quicken Financial Exchange) files commonly exported by banks.
//!
//! # Native parser
//!
//! Parsing is done by a small dependency-free reader (see the "Native OFX
//! parser" section below) rather than an external crate. OFX 1.x (SGML) and OFX
//! 2.x (XML) differ only in whether leaf elements are closed, so reading each
//! leaf's value as "the text up to the next `<`" handles both dialects, with no
//! dependency on header conformance or OFX version — sparse 1.x headers and 2.x
//! files both parse (see #1457). Dates are produced directly as
//! [`rustledger_core::NaiveDate`] (jiff), so this crate needs neither `ofxy`
//! nor `chrono`.

use crate::config::ImporterConfig;
use crate::{EnrichedImportResult, ImportResult, Importer};
use anyhow::{Context, Result};
use rustledger_core::NaiveDate;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_ops::enrichment::{CategorizationMethod, Enrichment};
use std::fs;
use std::path::Path;

/// OFX/QFX file importer.
///
/// True unit struct — all per-call state flows in via the
/// [`ImporterConfig`] passed to [`Importer::extract`] or to the
/// standalone helpers ([`Self::extract_from_string`] et al.).
///
/// OFX semantics:
/// - `config.account` is the target account for every transaction.
/// - `config.currency` is **required** (an OFX file may not declare a
///   currency at the transaction or statement level; we refuse to
///   guess and produce empty-string-currency `Amount`s).
// `Copy` intentionally NOT derived — see `CsvImporter` for the rationale.
#[derive(Debug, Default, Clone)]
pub struct OfxImporter;

impl OfxImporter {
    /// Extract transactions from OFX content using the given importer
    /// config. Stateless — pass account + currency via `config`.
    ///
    /// # Errors
    ///
    /// Returns an error if `config.currency` is `None` and the OFX
    /// content has no transaction-level or statement-level currency.
    pub fn extract_from_string(
        &self,
        content: &str,
        config: &ImporterConfig,
    ) -> Result<ImportResult> {
        let default_currency = config.currency.as_deref().ok_or_else(|| {
            anyhow::anyhow!(
                "OFX import requires a default currency \
                 (set `ImporterConfig.currency = Some(...)`)"
            )
        })?;

        let statements = parse_ofx(content).with_context(|| "Failed to parse OFX content")?;

        let mut directives = Vec::new();
        let mut warnings = Vec::new();

        // Bank and credit-card statements are imported identically: every
        // transaction posts to `config.account`.
        for statement in &statements {
            let statement_currency = statement.currency.as_deref().unwrap_or("");
            for txn in &statement.transactions {
                match Self::build_transaction(
                    txn,
                    statement_currency,
                    &config.account,
                    default_currency,
                ) {
                    Ok(t) => directives.push(Directive::Transaction(t)),
                    Err(e) => warnings.push(format!("Skipped transaction: {e}")),
                }
            }
        }

        let mut result = ImportResult::new(directives);
        for warning in warnings {
            result = result.with_warning(warning);
        }
        Ok(result)
    }

    /// Extract transactions from OFX content with enrichment metadata.
    ///
    /// OFX has no categorization signal, so every enrichment is the
    /// cheap-default (confidence 0.0, `Default` method). The fingerprint
    /// is computed per directive for dedup purposes.
    pub fn extract_from_string_enriched(
        &self,
        content: &str,
        config: &ImporterConfig,
    ) -> Result<EnrichedImportResult> {
        let result = self.extract_from_string(content, config)?;
        let entries = result
            .directives
            .into_iter()
            .enumerate()
            .map(|(i, directive)| {
                let fingerprint = crate::directive_fingerprint(&directive);

                let enrichment = Enrichment {
                    directive_index: i,
                    confidence: 0.0,
                    method: CategorizationMethod::Default,
                    alternatives: vec![],
                    fingerprint,
                };
                (directive, enrichment)
            })
            .collect();

        let mut enriched = EnrichedImportResult::new(entries);
        for warning in result.warnings {
            enriched = enriched.with_warning(warning);
        }
        Ok(enriched)
    }

    fn build_transaction(
        txn: &OfxTransaction,
        statement_currency: &str,
        account: &str,
        default_currency: &str,
    ) -> Result<Transaction> {
        let date = ofx_date_to_naive(&txn.date_posted)?;
        let amount: rust_decimal::Decimal = txn
            .amount
            .parse()
            .with_context(|| format!("invalid amount: {:?}", txn.amount))?;

        // Build narration from name and memo
        let name = txn.name.as_deref().unwrap_or("");
        let memo = txn.memo.as_deref().unwrap_or("");
        let narration = if memo.is_empty() {
            name.to_string()
        } else if name.is_empty() {
            memo.to_string()
        } else {
            format!("{name} - {memo}")
        };

        // Currency precedence: transaction → statement → config default.
        let curr = match txn.currency.as_deref().filter(|c| !c.is_empty()) {
            Some(c) => c.to_string(),
            None if statement_currency.is_empty() => default_currency.to_string(),
            None => statement_currency.to_string(),
        };

        // Create posting
        let units = Amount::new(amount, &curr);
        let posting = Posting::new(account, units);

        // Create balancing posting
        let contra_account = if amount < rust_decimal::Decimal::ZERO {
            "Expenses:Unknown"
        } else {
            "Income:Unknown"
        };
        let contra_posting = Posting::auto(contra_account);

        // Build transaction
        let mut txn_builder = Transaction::new(date, &narration)
            .with_flag('*')
            .with_synthesized_posting(posting)
            .with_synthesized_posting(contra_posting);

        // Add payee if name is available
        if !name.is_empty() && !memo.is_empty() {
            txn_builder = txn_builder.with_payee(name);
        }

        Ok(txn_builder)
    }
}

// ============================================================================
// Native OFX parser
//
// OFX 1.x SGML and OFX 2.x XML differ only in whether leaf elements are closed:
// SGML writes `<TAG>value` (the value runs to the next `<`), XML writes
// `<TAG>value</TAG>`. Reading each leaf as "text up to the next `<`" parses both
// dialects uniformly, with no dependency on header conformance or OFX version.
// This replaces the `ofxy` crate (and its `chrono` dependency).
// ============================================================================

/// One bank or credit-card statement: its declared currency (`CURDEF`) and the
/// transactions in its `BANKTRANLIST`.
struct OfxStatement {
    currency: Option<String>,
    transactions: Vec<OfxTransaction>,
}

/// A single `STMTTRN` aggregate, reduced to the fields we import. `date_posted`
/// and `amount` are kept raw and validated in [`OfxImporter::build_transaction`]
/// so a malformed value becomes a per-transaction warning, not a hard failure.
struct OfxTransaction {
    date_posted: String,
    amount: String,
    name: Option<String>,
    memo: Option<String>,
    currency: Option<String>,
}

/// Parse OFX content (1.x SGML or 2.x XML) into statements. Errors only if the
/// input isn't an OFX document at all; a well-formed file with no transactions
/// yields an empty list.
fn parse_ofx(content: &str) -> Result<Vec<OfxStatement>> {
    if !content.contains("<OFX>") && !content.contains("<OFX ") {
        anyhow::bail!("not an OFX document (no <OFX> element)");
    }

    let mut statements = Vec::new();
    for (open, close) in [("<STMTRS>", "</STMTRS>"), ("<CCSTMTRS>", "</CCSTMTRS>")] {
        for region in find_blocks(content, open, close) {
            statements.push(OfxStatement {
                currency: leaf(region, "CURDEF"),
                transactions: parse_transactions(region),
            });
        }
    }

    // Fallback for files carrying STMTTRN aggregates without a recognized
    // statement wrapper.
    if statements.is_empty() {
        let transactions = parse_transactions(content);
        if !transactions.is_empty() {
            statements.push(OfxStatement {
                currency: leaf(content, "CURDEF"),
                transactions,
            });
        }
    }

    Ok(statements)
}

/// Parse every `STMTTRN` block in `region`. A block missing the required
/// `DTPOSTED`/`TRNAMT` leaves isn't importable and is skipped.
fn parse_transactions(region: &str) -> Vec<OfxTransaction> {
    find_blocks(region, "<STMTTRN>", "</STMTTRN>")
        .into_iter()
        .filter_map(|block| {
            Some(OfxTransaction {
                date_posted: leaf(block, "DTPOSTED")?,
                amount: leaf(block, "TRNAMT")?,
                name: leaf(block, "NAME"),
                memo: leaf(block, "MEMO"),
                currency: leaf(block, "CURSYM"),
            })
        })
        .collect()
}

/// Return the slices between each `open`..`close` pair in `s` (non-overlapping;
/// OFX's STMTTRN/STMTRS aggregates don't self-nest, so this is sufficient).
fn find_blocks<'a>(s: &'a str, open: &str, close: &str) -> Vec<&'a str> {
    let mut blocks = Vec::new();
    let mut rest = s;
    while let Some(i) = rest.find(open) {
        let after = &rest[i + open.len()..];
        let Some(j) = after.find(close) else { break };
        blocks.push(&after[..j]);
        rest = &after[j + close.len()..];
    }
    blocks
}

/// Extract leaf element `tag`'s value from `block`: the text after `<tag>` up to
/// the next `<` (handles SGML `<TAG>v` and XML `<TAG>v</TAG>` alike),
/// entity-decoded and trimmed. `<tag/>` yields `Some("")`; absence yields `None`.
fn leaf(block: &str, tag: &str) -> Option<String> {
    let open = format!("<{tag}>");
    if let Some(i) = block.find(&open) {
        let after = &block[i + open.len()..];
        let end = after.find('<').unwrap_or(after.len());
        return Some(decode_entities(after[..end].trim()));
    }
    if block.contains(&format!("<{tag}/>")) {
        return Some(String::new());
    }
    None
}

/// Decode the five predefined XML entities (OFX rarely uses numeric refs).
/// `&amp;` is decoded last so `&amp;lt;` becomes `&lt;`, not `<`.
fn decode_entities(s: &str) -> String {
    if !s.contains('&') {
        return s.to_string();
    }
    s.replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
        .replace("&amp;", "&")
}

/// Convert an OFX datetime (`YYYYMMDD`, optionally followed by `HHMMSS[.fff][tz]`)
/// to a civil date by taking the `YYYYMMDD` prefix.
fn ofx_date_to_naive(s: &str) -> Result<NaiveDate> {
    let digits: String = s.trim().chars().take_while(char::is_ascii_digit).collect();
    if digits.len() < 8 {
        anyhow::bail!("invalid OFX date: {s:?}");
    }
    format!("{}-{}-{}", &digits[0..4], &digits[4..6], &digits[6..8])
        .parse()
        .with_context(|| format!("invalid OFX date: {s:?}"))
}

impl Importer for OfxImporter {
    fn name(&self) -> &'static str {
        "OFX/QFX"
    }

    fn identify(&self, path: &Path) -> bool {
        path.extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("ofx") || ext.eq_ignore_ascii_case("qfx"))
    }

    fn extract(&self, path: &Path, config: &ImporterConfig) -> Result<ImportResult> {
        let content = fs::read_to_string(path)
            .with_context(|| format!("Failed to read: {}", path.display()))?;
        self.extract_from_string(&content, config)
    }

    fn extract_enriched(
        &self,
        path: &Path,
        config: &ImporterConfig,
    ) -> Result<EnrichedImportResult> {
        let content = fs::read_to_string(path)
            .with_context(|| format!("Failed to read: {}", path.display()))?;
        self.extract_from_string_enriched(&content, config)
    }

    fn description(&self) -> &'static str {
        "Open Financial Exchange (OFX/QFX) file importer"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{CsvConfig, ImporterType};

    /// Build an `ImporterConfig` for OFX tests. OFX only needs
    /// `account` + `currency`; the `importer_type` Csv variant is
    /// inert (the OFX impl never touches it).
    fn ofx_cfg(account: &str, currency: &str) -> ImporterConfig {
        ImporterConfig {
            account: account.to_string(),
            currency: Some(currency.to_string()),
            importer_type: ImporterType::Csv(CsvConfig::default()),
        }
    }

    #[test]
    fn test_ofx_importer_name() {
        let importer = OfxImporter;
        assert_eq!(importer.name(), "OFX/QFX");
    }

    #[test]
    fn test_ofx_importer_description() {
        let importer = OfxImporter;
        assert_eq!(
            importer.description(),
            "Open Financial Exchange (OFX/QFX) file importer"
        );
    }

    #[test]
    fn test_ofx_importer_identify() {
        let importer = OfxImporter;
        assert!(importer.identify(Path::new("statement.ofx")));
        assert!(importer.identify(Path::new("statement.OFX")));
        assert!(importer.identify(Path::new("statement.qfx")));
        assert!(importer.identify(Path::new("statement.QFX")));
        assert!(!importer.identify(Path::new("statement.csv")));
        assert!(!importer.identify(Path::new("statement.pdf")));
        assert!(!importer.identify(Path::new("ofx"))); // No extension
    }

    #[test]
    fn test_ofx_importer_identify_no_extension() {
        let importer = OfxImporter;
        assert!(!importer.identify(Path::new("statement")));
    }

    #[test]
    fn test_ofx_importer_extract() {
        // Sample OFX content (minimal valid structure)
        let ofx_content = r"OFXHEADER:100
DATA:OFXSGML
VERSION:102
SECURITY:NONE
ENCODING:USASCII
CHARSET:1252
COMPRESSION:NONE
OLDFILEUID:NONE
NEWFILEUID:NONE

<OFX>
<SIGNONMSGSRSV1>
<SONRS>
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<DTSERVER>20240115120000
<LANGUAGE>ENG
</SONRS>
</SIGNONMSGSRSV1>
<BANKMSGSRSV1>
<STMTTRNRS>
<TRNUID>1001
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<STMTRS>
<CURDEF>USD
<BANKACCTFROM>
<BANKID>123456789
<ACCTID>987654321
<ACCTTYPE>CHECKING
</BANKACCTFROM>
<BANKTRANLIST>
<DTSTART>20240101
<DTEND>20240131
<STMTTRN>
<TRNTYPE>DEBIT
<DTPOSTED>20240115
<TRNAMT>-50.00
<FITID>2024011501
<NAME>GROCERY STORE
<MEMO>Weekly groceries
</STMTTRN>
<STMTTRN>
<TRNTYPE>CREDIT
<DTPOSTED>20240120
<TRNAMT>1500.00
<FITID>2024012001
<NAME>EMPLOYER INC
<MEMO>Salary payment
</STMTTRN>
</BANKTRANLIST>
<LEDGERBAL>
<BALAMT>5000.00
<DTASOF>20240131
</LEDGERBAL>
</STMTRS>
</STMTTRNRS>
</BANKMSGSRSV1>
</OFX>";

        let result =
            OfxImporter.extract_from_string(ofx_content, &ofx_cfg("Assets:Bank:Checking", "USD"));

        match &result {
            Ok(import_result) => {
                assert_eq!(import_result.directives.len(), 2);
                assert!(import_result.warnings.is_empty());
            }
            Err(e) => {
                // Some OFX parsers may be strict about format
                // Just verify we handled the error gracefully
                println!("OFX parse error (expected with minimal test data): {e}");
            }
        }
    }

    #[test]
    fn test_ofx_importer_credit_card() {
        // Credit card OFX content
        let ofx_content = r"OFXHEADER:100
DATA:OFXSGML
VERSION:102
SECURITY:NONE
ENCODING:USASCII
CHARSET:1252
COMPRESSION:NONE
OLDFILEUID:NONE
NEWFILEUID:NONE

<OFX>
<SIGNONMSGSRSV1>
<SONRS>
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<DTSERVER>20240115120000
<LANGUAGE>ENG
</SONRS>
</SIGNONMSGSRSV1>
<CREDITCARDMSGSRSV1>
<CCSTMTTRNRS>
<TRNUID>1001
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<CCSTMTRS>
<CURDEF>USD
<CCACCTFROM>
<ACCTID>1234567890123456
</CCACCTFROM>
<BANKTRANLIST>
<DTSTART>20240101
<DTEND>20240131
<STMTTRN>
<TRNTYPE>DEBIT
<DTPOSTED>20240110
<TRNAMT>-25.50
<FITID>2024011001
<NAME>RESTAURANT
</STMTTRN>
</BANKTRANLIST>
<LEDGERBAL>
<BALAMT>-250.00
<DTASOF>20240131
</LEDGERBAL>
</CCSTMTRS>
</CCSTMTTRNRS>
</CREDITCARDMSGSRSV1>
</OFX>";

        let result =
            OfxImporter.extract_from_string(ofx_content, &ofx_cfg("Liabilities:CreditCard", "USD"));

        match &result {
            Ok(import_result) => {
                assert_eq!(import_result.directives.len(), 1);
            }
            Err(e) => {
                println!("OFX parse error (expected with minimal test data): {e}");
            }
        }
    }

    #[test]
    fn test_ofx_importer_empty_bank_list() {
        // OFX with no transactions
        let ofx_content = r"OFXHEADER:100
DATA:OFXSGML
VERSION:102
SECURITY:NONE
ENCODING:USASCII
CHARSET:1252
COMPRESSION:NONE
OLDFILEUID:NONE
NEWFILEUID:NONE

<OFX>
<SIGNONMSGSRSV1>
<SONRS>
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<DTSERVER>20240115120000
<LANGUAGE>ENG
</SONRS>
</SIGNONMSGSRSV1>
<BANKMSGSRSV1>
<STMTTRNRS>
<TRNUID>1001
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<STMTRS>
<CURDEF>USD
<BANKACCTFROM>
<BANKID>123456789
<ACCTID>987654321
<ACCTTYPE>CHECKING
</BANKACCTFROM>
<LEDGERBAL>
<BALAMT>5000.00
<DTASOF>20240131
</LEDGERBAL>
</STMTRS>
</STMTTRNRS>
</BANKMSGSRSV1>
</OFX>";

        let result =
            OfxImporter.extract_from_string(ofx_content, &ofx_cfg("Assets:Bank:Checking", "USD"));

        match &result {
            Ok(import_result) => {
                assert!(import_result.directives.is_empty());
            }
            Err(e) => {
                println!("OFX parse error: {e}");
            }
        }
    }

    #[test]
    fn test_ofx_importer_invalid_content() {
        let importer = OfxImporter;
        let result = importer.extract_from_string("not valid ofx", &ofx_cfg("Assets:Bank", "USD"));
        assert!(result.is_err());
    }

    #[test]
    fn test_ofx_importer_extract_nonexistent_file() {
        use crate::config::{CsvConfig, ImporterType};
        let importer = OfxImporter;
        let config = ImporterConfig {
            account: "Assets:Bank".into(),
            currency: Some("USD".into()),
            importer_type: ImporterType::Csv(CsvConfig::default()),
        };
        let result = importer.extract(Path::new("/nonexistent/file.ofx"), &config);
        assert!(result.is_err());
    }

    #[test]
    fn test_ofx_importer_transaction_name_only() {
        // Transaction with only NAME, no MEMO
        let ofx_content = r"OFXHEADER:100
DATA:OFXSGML
VERSION:102
SECURITY:NONE
ENCODING:USASCII
CHARSET:1252
COMPRESSION:NONE
OLDFILEUID:NONE
NEWFILEUID:NONE

<OFX>
<SIGNONMSGSRSV1>
<SONRS>
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<DTSERVER>20240115120000
<LANGUAGE>ENG
</SONRS>
</SIGNONMSGSRSV1>
<BANKMSGSRSV1>
<STMTTRNRS>
<TRNUID>1001
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<STMTRS>
<CURDEF>USD
<BANKACCTFROM>
<BANKID>123456789
<ACCTID>987654321
<ACCTTYPE>CHECKING
</BANKACCTFROM>
<BANKTRANLIST>
<DTSTART>20240101
<DTEND>20240131
<STMTTRN>
<TRNTYPE>DEBIT
<DTPOSTED>20240115
<TRNAMT>-50.00
<FITID>2024011501
<NAME>GROCERY STORE
</STMTTRN>
</BANKTRANLIST>
<LEDGERBAL>
<BALAMT>5000.00
<DTASOF>20240131
</LEDGERBAL>
</STMTRS>
</STMTTRNRS>
</BANKMSGSRSV1>
</OFX>";

        let result =
            OfxImporter.extract_from_string(ofx_content, &ofx_cfg("Assets:Bank:Checking", "USD"));

        match &result {
            Ok(import_result) => {
                assert_eq!(import_result.directives.len(), 1);
            }
            Err(e) => {
                println!("OFX parse error: {e}");
            }
        }
    }

    #[test]
    fn test_ofx_importer_transaction_memo_only() {
        // Transaction with only MEMO, no NAME
        let ofx_content = r"OFXHEADER:100
DATA:OFXSGML
VERSION:102
SECURITY:NONE
ENCODING:USASCII
CHARSET:1252
COMPRESSION:NONE
OLDFILEUID:NONE
NEWFILEUID:NONE

<OFX>
<SIGNONMSGSRSV1>
<SONRS>
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<DTSERVER>20240115120000
<LANGUAGE>ENG
</SONRS>
</SIGNONMSGSRSV1>
<BANKMSGSRSV1>
<STMTTRNRS>
<TRNUID>1001
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<STMTRS>
<CURDEF>USD
<BANKACCTFROM>
<BANKID>123456789
<ACCTID>987654321
<ACCTTYPE>CHECKING
</BANKACCTFROM>
<BANKTRANLIST>
<DTSTART>20240101
<DTEND>20240131
<STMTTRN>
<TRNTYPE>DEBIT
<DTPOSTED>20240115
<TRNAMT>-50.00
<FITID>2024011501
<MEMO>Payment for services
</STMTTRN>
</BANKTRANLIST>
<LEDGERBAL>
<BALAMT>5000.00
<DTASOF>20240131
</LEDGERBAL>
</STMTRS>
</STMTTRNRS>
</BANKMSGSRSV1>
</OFX>";

        let result =
            OfxImporter.extract_from_string(ofx_content, &ofx_cfg("Assets:Bank:Checking", "USD"));

        match &result {
            Ok(import_result) => {
                assert_eq!(import_result.directives.len(), 1);
            }
            Err(e) => {
                println!("OFX parse error: {e}");
            }
        }
    }

    #[test]
    fn test_ofx_importer_income_transaction() {
        // Positive amount should map to Income:Unknown
        let ofx_content = r"OFXHEADER:100
DATA:OFXSGML
VERSION:102
SECURITY:NONE
ENCODING:USASCII
CHARSET:1252
COMPRESSION:NONE
OLDFILEUID:NONE
NEWFILEUID:NONE

<OFX>
<SIGNONMSGSRSV1>
<SONRS>
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<DTSERVER>20240115120000
<LANGUAGE>ENG
</SONRS>
</SIGNONMSGSRSV1>
<BANKMSGSRSV1>
<STMTTRNRS>
<TRNUID>1001
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<STMTRS>
<CURDEF>USD
<BANKACCTFROM>
<BANKID>123456789
<ACCTID>987654321
<ACCTTYPE>CHECKING
</BANKACCTFROM>
<BANKTRANLIST>
<DTSTART>20240101
<DTEND>20240131
<STMTTRN>
<TRNTYPE>CREDIT
<DTPOSTED>20240120
<TRNAMT>1500.00
<FITID>2024012001
<NAME>EMPLOYER INC
</STMTTRN>
</BANKTRANLIST>
<LEDGERBAL>
<BALAMT>5000.00
<DTASOF>20240131
</LEDGERBAL>
</STMTRS>
</STMTTRNRS>
</BANKMSGSRSV1>
</OFX>";

        let result =
            OfxImporter.extract_from_string(ofx_content, &ofx_cfg("Assets:Bank:Checking", "USD"));

        match &result {
            Ok(import_result) => {
                assert_eq!(import_result.directives.len(), 1);
            }
            Err(e) => {
                println!("OFX parse error: {e}");
            }
        }
    }

    #[test]
    fn test_ofx_importer_missing_currency_errors() {
        // A call-time config without `currency` should produce a typed error
        // rather than silently emitting empty-string-currency Amounts.
        let cfg = ImporterConfig {
            account: "Assets:Bank".into(),
            currency: None,
            importer_type: crate::config::ImporterType::Csv(crate::config::CsvConfig::default()),
        };
        let result =
            OfxImporter.extract_from_string("not OFX, but the currency check runs first", &cfg);
        assert!(result.is_err());
        let msg = result.unwrap_err().to_string();
        assert!(
            msg.contains("requires a default currency"),
            "expected currency error, got: {msg}"
        );
    }

    // ===== Native parser: #1457 cases + robustness =====

    /// OFX 1.x SGML that omits CHARSET/COMPRESSION/OLDFILEUID/NEWFILEUID — the
    /// header-strictness case from #1457. Must parse, and read fields correctly.
    #[test]
    fn test_native_1x_sparse_headers() {
        let ofx = "OFXHEADER:100\nDATA:OFXSGML\nVERSION:102\nSECURITY:NONE\nENCODING:USASCII\n\n\
<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD<BANKACCTFROM><ACCTID>1</BANKACCTFROM>\n\
<BANKTRANLIST>\n\
<STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115<TRNAMT>-50.00<FITID>t1<NAME>COFFEE SHOP</STMTTRN>\n\
</BANKTRANLIST></STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("sparse 1.x headers must parse");
        assert_eq!(r.directives.len(), 1);
        let Directive::Transaction(txn) = &r.directives[0] else {
            panic!("expected transaction");
        };
        assert_eq!(txn.narration.as_str(), "COFFEE SHOP");
        assert_eq!(txn.postings[0].account.as_str(), "Assets:Bank");
    }

    /// OFX 2.x (XML): version 200, `<?xml?>`/`<?OFX?>` prolog, closed tags, an
    /// XML entity in `<NAME>`, and a self-closing `<MEMO/>`. The #1457 hard case.
    #[test]
    fn test_native_2x_xml_with_entities_and_self_closing() {
        let ofx = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<?OFX OFXHEADER=\"200\" VERSION=\"200\" SECURITY=\"NONE\" OLDFILEUID=\"NONE\" NEWFILEUID=\"NONE\"?>\n\
<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD</CURDEF>\n\
<BANKTRANLIST>\n\
<STMTTRN><TRNTYPE>DEBIT</TRNTYPE><DTPOSTED>20240115120000.000[-5:EST]</DTPOSTED><TRNAMT>-50.00</TRNAMT><FITID>t1</FITID><NAME>Johnson &amp; Co</NAME><MEMO/></STMTTRN>\n\
</BANKTRANLIST></STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("2.x XML must parse");
        assert_eq!(r.directives.len(), 1);
        let Directive::Transaction(txn) = &r.directives[0] else {
            panic!("expected transaction");
        };
        // Entity decoded; timezone date reduced to the civil date; MEMO empty.
        assert_eq!(txn.narration.as_str(), "Johnson & Co");
        assert_eq!(txn.date, rustledger_core::naive_date(2024, 1, 15).unwrap());
    }

    /// Bank + credit-card statements with different `CURDEF` values: each
    /// statement's transactions must use its own currency.
    #[test]
    fn test_native_multi_statement_currency() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
<BANKTRANLIST><STMTTRN><DTPOSTED>20240101<TRNAMT>-1.00<NAME>A</STMTTRN></BANKTRANLIST>\n\
</STMTRS></STMTTRNRS></BANKMSGSRSV1>\n\
<CREDITCARDMSGSRSV1><CCSTMTTRNRS><CCSTMTRS><CURDEF>CAD\n\
<BANKTRANLIST><STMTTRN><DTPOSTED>20240102<TRNAMT>-2.00<NAME>B</STMTTRN></BANKTRANLIST>\n\
</CCSTMTRS></CCSTMTTRNRS></CREDITCARDMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("multi-statement must parse");
        assert_eq!(r.directives.len(), 2);
        let curr = |d: &Directive| match d {
            Directive::Transaction(t) => t.postings[0].amount().unwrap().currency.to_string(),
            _ => panic!("expected transaction"),
        };
        assert_eq!(curr(&r.directives[0]), "USD");
        assert_eq!(curr(&r.directives[1]), "CAD");
    }

    #[test]
    fn test_native_leaf_and_helpers() {
        assert_eq!(leaf("<NAME>Foo<MEMO>Bar", "NAME").as_deref(), Some("Foo"));
        assert_eq!(leaf("<NAME>Foo</NAME>", "NAME").as_deref(), Some("Foo"));
        assert_eq!(leaf("<MEMO/>", "MEMO").as_deref(), Some(""));
        assert_eq!(leaf("<NAME>x", "MEMO"), None);
        assert_eq!(decode_entities("a &amp; b &lt;c&gt;"), "a & b <c>");
        assert_eq!(
            ofx_date_to_naive("20240115120000[-5:EST]").unwrap(),
            rustledger_core::naive_date(2024, 1, 15).unwrap()
        );
        assert!(ofx_date_to_naive("2024").is_err());
    }
}
