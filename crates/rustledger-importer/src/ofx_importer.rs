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

        let transactions = parse_ofx(content).with_context(|| "Failed to parse OFX content")?;

        let mut directives = Vec::new();
        let mut warnings = Vec::new();

        // Bank and credit-card transactions are imported identically: every
        // transaction posts to `config.account`.
        for txn in &transactions {
            let statement_currency = txn.statement_currency.as_deref().unwrap_or("");
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
// OFX 1.x SGML and OFX 2.x XML differ only in whether elements are closed: SGML
// writes `<TAG>value` (the value runs to the next `<`) and may omit end tags on
// aggregates too, while XML writes `<TAG>value</TAG>`. Reading each leaf as
// "text up to the next `<`", and bounding each `STMTTRN` by the next sibling /
// list-close / end-of-input rather than requiring `</STMTTRN>`, parses both
// dialects (and end-tag-less SGML) with no dependency on header conformance or
// OFX version. This replaces the `ofxy` crate (and its `chrono` dependency).
//
// Dates use the bank-stated civil date (the `YYYYMMDD` prefix of `DTPOSTED`),
// not a UTC-shifted date — a transaction stamped late evening with a timezone
// offset stays on the date the statement shows it, which is what an accounting
// import wants. (`ofxy` converted to UTC, which could move it a day.)
// ============================================================================

/// A single `STMTTRN`, reduced to the fields we import, plus the statement
/// currency (nearest preceding `CURDEF`) it belongs to. `date_posted` and
/// `amount` are kept raw and validated in [`OfxImporter::build_transaction`] so
/// a malformed or absent value becomes a per-transaction warning, not a silent
/// drop or a hard failure of the whole import.
struct OfxTransaction {
    date_posted: String,
    amount: String,
    name: Option<String>,
    memo: Option<String>,
    currency: Option<String>,
    statement_currency: Option<String>,
}

/// Parse OFX content (1.x SGML or 2.x XML) into transactions. Errors only if the
/// input isn't an OFX document at all; a well-formed file with no transactions
/// yields an empty list.
fn parse_ofx(content: &str) -> Result<Vec<OfxTransaction>> {
    // The `<OFX>` root may carry attributes or wrap onto the next line, so match
    // `<OFX` followed by `>` or any whitespace rather than the two literal forms.
    let has_ofx_root = content.match_indices("<OFX").any(|(i, _)| {
        content[i + 4..]
            .chars()
            .next()
            .is_some_and(|c| c == '>' || c.is_whitespace())
    });
    if !has_ofx_root {
        anyhow::bail!("not an OFX document (no <OFX> element)");
    }

    // `CURDEF` positions in document order, so each transaction can take the
    // currency of the statement it sits in (single forward pass — no per-txn
    // rescan, keeping the parser linear).
    let mut curdefs: Vec<(usize, String)> = Vec::new();
    let mut scan = 0;
    while let Some(rel) = content[scan..].find("<CURDEF>") {
        let i = scan + rel;
        if let Some(v) = leaf(&content[i..], "CURDEF") {
            curdefs.push((i, v));
        }
        scan = i + "<CURDEF>".len();
    }

    let mut transactions = Vec::new();
    let mut cd = 0;
    let mut statement_currency: Option<String> = None;
    let mut scan = 0;
    while let Some(rel) = content[scan..].find("<STMTTRN>") {
        let start = scan + rel;
        let after = start + "<STMTTRN>".len();
        // Advance the statement currency to the last CURDEF before this txn.
        while cd < curdefs.len() && curdefs[cd].0 < start {
            statement_currency = Some(curdefs[cd].1.clone());
            cd += 1;
        }
        // The block runs to the next STMTTRN open, the txn-list close, or end —
        // whichever comes first — so a missing/whitespaced `</STMTTRN>` is fine.
        let rest = &content[after..];
        let end = ["<STMTTRN>", "</STMTTRN>", "</BANKTRANLIST>"]
            .iter()
            .filter_map(|m| rest.find(m))
            .min()
            .unwrap_or(rest.len());
        let block = &rest[..end];
        transactions.push(OfxTransaction {
            date_posted: leaf(block, "DTPOSTED").unwrap_or_default(),
            amount: leaf(block, "TRNAMT").unwrap_or_default(),
            name: leaf(block, "NAME"),
            memo: leaf(block, "MEMO"),
            currency: transaction_currency(block),
            statement_currency: statement_currency.clone(),
        });
        scan = after;
    }

    Ok(transactions)
}

/// A transaction's own currency: the `<CURSYM>` inside its `<CURRENCY>`
/// aggregate. Deliberately ignores `<ORIGCURRENCY>` (the pre-conversion
/// currency), whose `CURSYM` must not be mistaken for the posted amount's.
fn transaction_currency(block: &str) -> Option<String> {
    // `<ORIGCURRENCY>` does not contain the literal `<CURRENCY>`, so this only
    // matches the real `<CURRENCY>` aggregate.
    let i = block.find("<CURRENCY>")?;
    leaf(&block[i..], "CURSYM")
}

/// Extract leaf element `tag`'s value from `block`: the text after the start tag
/// up to the next `<` (handles SGML `<TAG>v` and XML `<TAG>v</TAG>` alike),
/// entity-decoded and trimmed. All start-tag forms are recognized — `<TAG>`,
/// `<TAG/>`, `<TAG />`, and `<TAG attr="…">` / `<TAG attr="…"/>` — with the
/// self-closing forms yielding `Some("")`. Absence yields `None`. The next
/// character after `<tag` must be `>`, `/`, or whitespace, so `<TAG>` never
/// matches a longer sibling like `<TAGEXTRA>`.
fn leaf(block: &str, tag: &str) -> Option<String> {
    let prefix = format!("<{tag}");
    let mut from = 0;
    loop {
        let i = from + block[from..].find(&prefix)?;
        let rest = &block[i + prefix.len()..];
        match rest.chars().next() {
            // `<TAG>value…`
            Some('>') => {
                let after = &rest['>'.len_utf8()..];
                let end = after.find('<').unwrap_or(after.len());
                return Some(decode_entities(after[..end].trim()));
            }
            // `<TAG/>`, `<TAG />`, `<TAG attr=…>`, `<TAG attr=…/>`
            Some('/' | ' ' | '\t' | '\r' | '\n') => {
                let gt = rest.find('>')?;
                if rest[..gt].ends_with('/') {
                    return Some(String::new()); // self-closing
                }
                let after = &rest[gt + 1..];
                let end = after.find('<').unwrap_or(after.len());
                return Some(decode_entities(after[..end].trim()));
            }
            // Not this tag (e.g. `<TAGEXTRA>`); keep searching.
            _ => from = i + prefix.len(),
        }
    }
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
    let s = s.trim();
    // The civil date is the leading `YYYYMMDD`; slice it directly (the bytes are
    // ASCII, so byte and char indices coincide) rather than allocating.
    if s.len() < 8 || !s.as_bytes()[..8].iter().all(u8::is_ascii_digit) {
        anyhow::bail!("invalid OFX date: {s:?}");
    }
    format!("{}-{}-{}", &s[0..4], &s[4..6], &s[6..8])
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

        let import_result = result.expect("OFX content should parse");
        assert_eq!(import_result.directives.len(), 2);
        assert!(import_result.warnings.is_empty());
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

        let import_result = result.expect("OFX content should parse");
        assert_eq!(import_result.directives.len(), 1);
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

        let import_result = result.expect("OFX content should parse");
        assert!(import_result.directives.is_empty());
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

        let import_result = result.expect("OFX content should parse");
        assert_eq!(import_result.directives.len(), 1);
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

        let import_result = result.expect("OFX content should parse");
        assert_eq!(import_result.directives.len(), 1);
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

        let import_result = result.expect("OFX content should parse");
        assert_eq!(import_result.directives.len(), 1);
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
        // All XML start-tag forms (whitespace self-close, attributes).
        assert_eq!(leaf("<MEMO />", "MEMO").as_deref(), Some(""));
        assert_eq!(leaf("<MEMO x=\"1\"/>", "MEMO").as_deref(), Some(""));
        assert_eq!(leaf("<NAME id=\"1\">Foo<", "NAME").as_deref(), Some("Foo"));
        // A longer sibling must not be matched by a shorter tag.
        assert_eq!(
            leaf("<NAMEEXTRA>Z<NAME>Foo", "NAME").as_deref(),
            Some("Foo")
        );
        assert_eq!(decode_entities("a &amp; b &lt;c&gt;"), "a & b <c>");
        assert_eq!(
            ofx_date_to_naive("20240115120000[-5:EST]").unwrap(),
            rustledger_core::naive_date(2024, 1, 15).unwrap()
        );
        assert!(ofx_date_to_naive("2024").is_err());
    }

    /// Helper: the currency of the first extracted transaction's primary posting.
    fn first_posting_currency(r: &ImportResult) -> String {
        match &r.directives[0] {
            Directive::Transaction(t) => t.postings[0].amount().unwrap().currency.to_string(),
            _ => panic!("expected transaction"),
        }
    }

    /// A transaction-level `<CURRENCY><CURSYM>` overrides the statement `CURDEF`.
    #[test]
    fn test_native_transaction_cursym_overrides_statement() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
<BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>-50.00<NAME>X\n\
<CURRENCY><CURRATE>1.1<CURSYM>EUR</CURRENCY></STMTTRN></BANKTRANLIST>\n\
</STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("must parse");
        assert_eq!(first_posting_currency(&r), "EUR");
    }

    /// `<ORIGCURRENCY>` (pre-conversion currency) must NOT be used for the posted
    /// amount — it stays the statement currency. Regression for the review bug
    /// where `CURSYM` was captured from anywhere in the block.
    #[test]
    fn test_native_origcurrency_does_not_override() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
<BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>-50.00<NAME>FOREIGN\n\
<ORIGCURRENCY><CURRATE>0.8<CURSYM>GBP</ORIGCURRENCY></STMTTRN></BANKTRANLIST>\n\
</STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("must parse");
        assert_eq!(first_posting_currency(&r), "USD");
    }

    /// OFX 1.x SGML that omits the `</STMTTRN>` aggregate close tags must still
    /// yield every transaction (bounded by the next `<STMTTRN>` / list close).
    #[test]
    fn test_native_sgml_without_aggregate_close_tags() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
<BANKTRANLIST>\n\
<STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115<TRNAMT>-50.00<NAME>A\n\
<STMTTRN><TRNTYPE>CREDIT<DTPOSTED>20240116<TRNAMT>60.00<NAME>B\n\
</BANKTRANLIST></STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("end-tag-less SGML must parse");
        assert_eq!(r.directives.len(), 2);
    }

    /// OFX 2.x (XML) credit-card statement (`<CCSTMTRS>`, closed tags).
    #[test]
    fn test_native_2x_credit_card() {
        let ofx = "<?xml version=\"1.0\"?><?OFX OFXHEADER=\"200\" VERSION=\"200\"?>\n\
<OFX><CREDITCARDMSGSRSV1><CCSTMTTRNRS><CCSTMTRS><CURDEF>USD</CURDEF>\n\
<BANKTRANLIST><STMTTRN><TRNTYPE>DEBIT</TRNTYPE><DTPOSTED>20240110</DTPOSTED><TRNAMT>-25.50</TRNAMT><NAME>SHOP</NAME></STMTTRN></BANKTRANLIST>\n\
</CCSTMTRS></CCSTMTTRNRS></CREDITCARDMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Liabilities:Card", "USD"))
            .expect("2.x credit card must parse");
        assert_eq!(r.directives.len(), 1);
    }

    /// A transaction with neither NAME nor MEMO gets an empty narration.
    #[test]
    fn test_native_no_name_no_memo() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
<BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>-50.00</STMTTRN></BANKTRANLIST>\n\
</STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("must parse");
        assert_eq!(r.directives.len(), 1);
        let Directive::Transaction(t) = &r.directives[0] else {
            panic!("expected transaction");
        };
        assert_eq!(t.narration.as_str(), "");
    }

    /// A malformed/absent amount is skipped with a warning, not a hard failure
    /// or a silent drop.
    #[test]
    fn test_native_malformed_amount_warns() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
<BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>not-a-number<NAME>X</STMTTRN></BANKTRANLIST>\n\
</STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("parse succeeds; the bad txn is skipped");
        assert!(r.directives.is_empty());
        assert_eq!(r.warnings.len(), 1);
        assert!(r.warnings[0].contains("invalid amount"));
    }

    /// The civil date is the bank-stated date, not a UTC-shifted one: a late
    /// timestamp with an offset that would cross midnight in UTC stays put.
    #[test]
    fn test_native_date_is_local_not_utc() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
<BANKTRANLIST><STMTTRN><DTPOSTED>20240115230000[-5:EST]<TRNAMT>-50.00<NAME>LATE</STMTTRN></BANKTRANLIST>\n\
</STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let r = OfxImporter
            .extract_from_string(ofx, &ofx_cfg("Assets:Bank", "USD"))
            .expect("must parse");
        let Directive::Transaction(t) = &r.directives[0] else {
            panic!("expected transaction");
        };
        // 23:00 EST is 04:00 UTC next day; we keep the stated 2024-01-15.
        assert_eq!(t.date, rustledger_core::naive_date(2024, 1, 15).unwrap());
    }
}
