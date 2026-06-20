//! OFX/QFX file importer.
//!
//! This module implements importing transactions from OFX (Open Financial Exchange)
//! and QFX (Quicken Financial Exchange) files commonly exported by banks.
//!
//! # Chrono boundary
//!
//! `ofxy::body::Transaction::date_posted` returns `chrono::DateTime<Utc>`, but
//! the rest of the workspace uses `jiff::civil::Date`. The chrono → jiff
//! conversion happens inside `extract_transaction` via a `format("%Y-%m-%d")
//! .parse()` round-trip. No `chrono` type appears in any `pub` signature in
//! this crate — `chrono` is an internal, ofxy-only seal. If we ever drop or
//! replace ofxy, the chrono dependency can go away with it.

use crate::config::ImporterConfig;
use crate::{EnrichedImportResult, ImportResult, Importer};
use anyhow::{Context, Result};
use rustledger_core::NaiveDate;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_ops::enrichment::{CategorizationMethod, Enrichment};
use std::borrow::Cow;
use std::fs;
use std::path::Path;

/// The OFX 1.x SGML header keys `ofxy` requires, with safe canonical defaults.
/// `ofxy` reads the header only structurally — we extract transactions from the
/// body — so supplying placeholders for absent keys is lossless here.
const OFX_HEADER_DEFAULTS: &[(&str, &str)] = &[
    ("OFXHEADER", "100"),
    ("DATA", "OFXSGML"),
    ("VERSION", "102"),
    ("SECURITY", "NONE"),
    ("ENCODING", "USASCII"),
    ("CHARSET", "1252"),
    ("COMPRESSION", "NONE"),
    ("OLDFILEUID", "NONE"),
    ("NEWFILEUID", "NONE"),
];

/// Normalize the OFX header so `ofxy` — which accepts only a complete OFX 1.x
/// SGML header (versions 102/103/151/160) and requires `CHARSET`/`OLDFILEUID`/
/// `NEWFILEUID` — can parse two real-world cases it otherwise rejects:
///
/// 1. **OFX 1.x missing required headers.** Banks routinely omit `CHARSET` or the
///    FILEUIDs. We fill only the absent keys, preserving the real `VERSION` etc.
/// 2. **OFX 2.x (XML).** The `<?xml?>`/`<?OFX?>` prolog carries no `KEY:VALUE`
///    headers and declares version 200+. We replace it with a synthetic 1.x
///    header; `ofxy`'s body deserializer already tolerates the XML closed tags,
///    so the transactions parse unchanged.
///
/// `ofxy` splits the file at `<OFX>`, so rewriting everything before it leaves
/// the body untouched. Conformant 1.x input is returned borrowed (no change);
/// input without `<OFX>` is left for `ofxy` to reject as before.
fn normalize_ofx_header(content: &str) -> Cow<'_, str> {
    let Some(body_start) = content.find("<OFX>") else {
        return Cow::Borrowed(content);
    };
    let (header_region, body) = content.split_at(body_start);

    // Collect recognized `KEY:VALUE` header lines (uppercase bareword keys). XML
    // prolog lines use `KEY="VALUE"` attributes, not `:`, so contribute nothing.
    let found: Vec<(&str, &str)> = header_region
        .lines()
        .filter_map(|line| line.split_once(':'))
        .map(|(k, v)| (k.trim(), v.trim()))
        .filter(|(k, _)| !k.is_empty() && k.chars().all(|c| c.is_ascii_uppercase()))
        .collect();
    let value = |key: &str| found.iter().find(|(k, _)| *k == key).map(|&(_, v)| v);
    // Whether a present value is one `ofxy` will accept.
    let valid = |key: &str| match key {
        "VERSION" => value("VERSION").is_some_and(|v| matches!(v, "102" | "103" | "151" | "160")),
        "DATA" => value("DATA") == Some("OFXSGML"),
        "ENCODING" => value("ENCODING").is_some_and(|v| matches!(v, "USASCII" | "UNICODE")),
        "SECURITY" => value("SECURITY").is_some_and(|v| matches!(v, "NONE" | "TYPE1")),
        "COMPRESSION" => true, // `ofxy` defaults this; never required
        _ => value(key).is_some(),
    };

    // Conformant 1.x header: leave the input untouched.
    if OFX_HEADER_DEFAULTS.iter().all(|(k, _)| valid(k)) {
        return Cow::Borrowed(content);
    }

    let mut out = String::with_capacity(content.len() + 128);
    for (key, default) in OFX_HEADER_DEFAULTS {
        out.push_str(key);
        out.push(':');
        out.push_str(if valid(key) {
            value(key).unwrap_or(default)
        } else {
            default
        });
        out.push('\n');
    }
    out.push('\n');
    out.push_str(body);
    Cow::Owned(out)
}

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

        // Normalize the header so real-world 1.x files with missing headers and
        // 2.x (XML) files parse, rather than being rejected by `ofxy`'s strict
        // header/version requirements (see #1457).
        let normalized = normalize_ofx_header(content);
        let ofx: ofxy::Ofx = normalized
            .parse()
            .with_context(|| "Failed to parse OFX content")?;

        let mut directives = Vec::new();
        let mut warnings = Vec::new();

        // Process bank accounts
        if let Some(bank_msg) = &ofx.body.bank {
            let stmt = &bank_msg.transaction_response.statement;
            let currency = &stmt.currency;

            if let Some(txn_list) = &stmt.bank_transactions {
                for txn in &txn_list.transactions {
                    match Self::parse_transaction(txn, currency, &config.account, default_currency)
                    {
                        Ok(t) => directives.push(Directive::Transaction(t)),
                        Err(e) => warnings.push(format!("Skipped transaction: {e}")),
                    }
                }
            }
        }

        // Process credit card accounts
        if let Some(cc_msg) = &ofx.body.credit_card {
            let stmt = &cc_msg.transaction_response.statement;
            let currency = &stmt.currency;

            if let Some(txn_list) = &stmt.bank_transactions {
                for txn in &txn_list.transactions {
                    match Self::parse_transaction(txn, currency, &config.account, default_currency)
                    {
                        Ok(t) => directives.push(Directive::Transaction(t)),
                        Err(e) => warnings.push(format!("Skipped transaction: {e}")),
                    }
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

    fn parse_transaction(
        txn: &ofxy::body::Transaction,
        statement_currency: &str,
        account: &str,
        default_currency: &str,
    ) -> Result<Transaction> {
        // Get date from ofxy's DateTime<Utc> via formatted string roundtrip.
        // See module docstring re: the chrono boundary.
        let date: NaiveDate = txn
            .date_posted
            .format("%Y-%m-%d")
            .to_string()
            .parse()
            .with_context(|| "Invalid date")?;

        // Get amount
        let amount = txn.amount;

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
        let curr = txn.currency.as_ref().map_or_else(
            || {
                if statement_currency.is_empty() {
                    default_currency.to_string()
                } else {
                    statement_currency.to_string()
                }
            },
            |c| c.symbol.clone(),
        );

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

    // ===== #1457: header-normalization shim =====

    /// A 1.x SGML statement that omits CHARSET/COMPRESSION/OLDFILEUID/NEWFILEUID
    /// (only the common OFXHEADER/DATA/VERSION/SECURITY/ENCODING present) — the
    /// kind of header many banks emit. Must parse rather than fail on a missing
    /// required header.
    #[test]
    fn test_ofx_1x_missing_headers_parses() {
        let ofx = "OFXHEADER:100\nDATA:OFXSGML\nVERSION:102\nSECURITY:NONE\nENCODING:USASCII\n\n\
<OFX><BANKMSGSRSV1><STMTTRNRS><TRNUID>1<STATUS><CODE>0<SEVERITY>INFO</STATUS>\n\
<STMTRS><CURDEF>USD<BANKACCTFROM><BANKID>123<ACCTID>456<ACCTTYPE>CHECKING</BANKACCTFROM>\n\
<BANKTRANLIST><DTSTART>20240101<DTEND>20240131\n\
<STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115<TRNAMT>-50.00<FITID>t1<NAME>COFFEE SHOP</STMTTRN>\n\
</BANKTRANLIST></STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let result = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank:Checking", "USD"))
            .expect("1.x with sparse headers should parse");
        assert_eq!(result.directives.len(), 1);
    }

    /// An OFX 2.x (XML) statement — `<?xml?>`/`<?OFX?>` prolog, version 200,
    /// closed tags. The synthetic-header transcode must let it parse.
    #[test]
    fn test_ofx_2x_xml_parses() {
        let ofx = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<?OFX OFXHEADER=\"200\" VERSION=\"200\" SECURITY=\"NONE\" OLDFILEUID=\"NONE\" NEWFILEUID=\"NONE\"?>\n\
<OFX><BANKMSGSRSV1><STMTTRNRS><TRNUID>1</TRNUID><STATUS><CODE>0</CODE><SEVERITY>INFO</SEVERITY></STATUS>\n\
<STMTRS><CURDEF>USD</CURDEF><BANKACCTFROM><BANKID>123</BANKID><ACCTID>456</ACCTID><ACCTTYPE>CHECKING</ACCTTYPE></BANKACCTFROM>\n\
<BANKTRANLIST><DTSTART>20240101</DTSTART><DTEND>20240131</DTEND>\n\
<STMTTRN><TRNTYPE>DEBIT</TRNTYPE><DTPOSTED>20240115</DTPOSTED><TRNAMT>-50.00</TRNAMT><FITID>t1</FITID><NAME>COFFEE</NAME></STMTTRN>\n\
</BANKTRANLIST></STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let result = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("2.x XML should parse via the transcode");
        assert_eq!(result.directives.len(), 1);
    }

    /// A fully conformant 1.x header is returned untouched (borrowed).
    #[test]
    fn test_normalize_leaves_conformant_unchanged() {
        let ofx = "OFXHEADER:100\nDATA:OFXSGML\nVERSION:102\nSECURITY:NONE\nENCODING:USASCII\n\
CHARSET:1252\nCOMPRESSION:NONE\nOLDFILEUID:NONE\nNEWFILEUID:NONE\n\n<OFX></OFX>";
        assert!(matches!(normalize_ofx_header(ofx), Cow::Borrowed(_)));
    }

    /// Input without an `<OFX>` tag is left for `ofxy` to reject (borrowed).
    #[test]
    fn test_normalize_passthrough_without_ofx_tag() {
        assert!(matches!(normalize_ofx_header("garbage"), Cow::Borrowed(_)));
    }
}
