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

        // Statement-level sanity check before any transaction is built: the
        // file states which side of the balance sheet it describes, and a
        // mismatch against `config.account` silently inverts every sign.
        if let Some(kind) = detect_statement_kind(content)
            && let Some(warning) = account_kind_mismatch(&config.account, kind)
        {
            warnings.push(warning);
        }

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

        // The statement's own closing balance, as an assertion. This is what
        // turns an import from "hope it is complete" into "proven complete":
        // if a transaction were dropped, the assertion fails.
        // Ambiguous: several statements, one configured account. Taking the
        // first would emit an assertion describing only part of what was
        // imported, and a wrong assertion is worse than none — but declining
        // in silence would be its own bug, so say so.
        if ledgerbal_count(content) > 1 {
            warnings.push(format!(
                "{} statements carry a LEDGERBAL; no balance assertion was emitted \
                 because they cannot be attributed to one account. Split the file \
                 per account to get assertions.",
                ledgerbal_count(content)
            ));
        }

        // Only alongside transactions. The assertion's job is to prove the
        // transaction set is complete; with nothing extracted there is nothing
        // to prove, and a lone balance from an empty statement reads as an
        // import that did something when it did not.
        if ledgerbal_count(content) == 1
            && !directives.is_empty()
            && let Some(balance) = parse_statement_balance(content)
        {
            let currency = transactions
                .first()
                .and_then(|t| t.statement_currency.as_deref())
                .unwrap_or(default_currency);
            directives.push(Directive::Balance(rustledger_core::Balance::new(
                balance.assert_on,
                config.account.as_str(),
                Amount::new(balance.amount, currency),
            )));
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

        // The bank's own transaction id, as a link.
        //
        // A link rather than a tag because this is identity, not a category:
        // tags group many entries under one label, links connect specific
        // related ones. It also keeps thousands of unique ids out of the tag
        // namespace, where they would swamp autocomplete and tag queries.
        if let Some(link) = txn.fitid.as_deref().and_then(fitid_link) {
            txn_builder = txn_builder.with_link(link);
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
    /// The bank's own `FITID` for this transaction, if it gave one.
    ///
    /// Financial Institution Transaction ID: unique and stable per account,
    /// which is the property dedup wants. Everything else we match on (date,
    /// amount, payee text) is either shared by legitimate duplicates or
    /// changed by the user editing their ledger.
    fitid: Option<String>,
}

/// How many statements in this file state a closing balance.
///
/// More than one means more than one statement, and every transaction here is
/// posted to a single configured account, so there is no way to say which
/// balance that account should assert.
fn ledgerbal_count(content: &str) -> usize {
    content.matches("<LEDGERBAL").count()
}

/// The statement's closing balance, from `LEDGERBAL`.
///
/// `DTASOF` is the moment the bank states the balance held, so it is the
/// closing balance for that day.
struct StatementBalance {
    amount: rust_decimal::Decimal,
    /// The date the balance is asserted for, already adjusted (see below).
    assert_on: NaiveDate,
}

/// Parse `LEDGERBAL` into a balance assertion.
///
/// **The date is deliberately DTASOF + 1 day.** A beancount `balance`
/// directive asserts the balance at the *beginning* of its date, before that
/// day's own transactions; a bank's `DTASOF` balance is the closing figure
/// *after* them. Emitting it verbatim would assert yesterday's balance against
/// today's date and fail on any statement whose last day has activity.
/// Verified against the validator: an assertion dated the same day as a
/// transaction sees the pre-transaction balance.
///
/// Returns `None` when either field is missing or unparsable, since a balance
/// without a date cannot be placed and a date without an amount asserts
/// nothing. A partial `LEDGERBAL` is a statement we do not understand, and
/// guessing at one is how a wrong assertion gets into someone's ledger.
fn parse_statement_balance(content: &str) -> Option<StatementBalance> {
    let block_start = content.find("<LEDGERBAL")?;
    let rest = &content[block_start..];

    // Bound the element, the same way `STMTTRN` is bounded above. Reading to
    // end-of-input let the fields be filled from whatever came next, and what
    // comes next is nearly always `<AVAILBAL>` — a DIFFERENT balance. A
    // `LEDGERBAL` missing its `BALAMT` then asserted the *available* balance
    // as the ledger balance: a silently wrong number, which is the exact
    // outcome the "a partial LEDGERBAL yields nothing" rule below exists to
    // prevent. OFX 1.x may omit the close tag, so a sibling or a parent close
    // ends the element too.
    let end = [
        "</LEDGERBAL>",
        "<AVAILBAL",
        "</STMTRS>",
        "</CCSTMTRS>",
        "</OFX>",
    ]
    .iter()
    .filter_map(|marker| rest.find(marker))
    .min()
    .unwrap_or(rest.len());
    let block = &rest[..end];

    let amount: rust_decimal::Decimal = leaf(block, "BALAMT")?.trim().parse().ok()?;
    let as_of = ofx_date_to_naive(&leaf(block, "DTASOF")?).ok()?;

    Some(StatementBalance {
        amount,
        assert_on: as_of.tomorrow().ok()?,
    })
}

/// Prefix marking a link as a bank-assigned OFX transaction id.
///
/// Namespaced so it cannot collide with a link the user wrote, and so dedup
/// can tell "this is an id I can trust" from "this is someone's invoice tag".
const FITID_LINK_PREFIX: &str = "ofx-";

/// Render a `FITID` as a beancount link, or `None` if nothing usable survives.
///
/// Links lex as `\^[a-zA-Z0-9-_/.]+`, and a `FITID` is an opaque bank string
/// that need not respect that. Anything outside the set becomes `-`, so the
/// emitted ledger re-parses; without this an id containing a space or a colon
/// would produce a file rustledger itself could not read.
///
/// Distinctness is preserved for the ids this matters for: two different ids
/// only collide after sanitizing if they differ *only* in characters that all
/// map to `-`, which no real FITID scheme does. Dedup treats a link as strong
/// evidence, not proof, so a pathological collision degrades to the fuzzy
/// match rather than silently dropping a transaction.
fn fitid_link(fitid: &str) -> Option<String> {
    let cleaned: String = fitid
        .trim()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '/' | '.') {
                c
            } else {
                '-'
            }
        })
        .collect();

    // An id that sanitizes to nothing (or to only separators) carries no
    // information, and `^ofx-` alone would be a link every such transaction
    // shares — worse than no link at all.
    if cleaned.trim_matches('-').is_empty() {
        return None;
    }
    Some(format!("{FITID_LINK_PREFIX}{cleaned}"))
}

/// Which side of the balance sheet an OFX statement describes.
///
/// OFX states this twice over: the message set wrapping the statement
/// (`CREDITCARDMSGSRSV1` vs `BANKMSGSRSV1`) and, for bank statements, the
/// `ACCTTYPE` leaf. We read both because either can be absent in the wild.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatementKind {
    /// A bank statement: the account holds value.
    Asset,
    /// A credit card or line of credit: the account owes it.
    Liability,
}

impl StatementKind {
    /// A phrase naming this side of the balance sheet, for messages.
    #[must_use]
    pub const fn describe(self) -> &'static str {
        match self {
            Self::Asset => "an asset account",
            Self::Liability => "a liability account",
        }
    }
}

/// Infer the statement's account kind, or `None` when the file does not say
/// or contradicts itself.
///
/// Deliberately conservative. A file carrying BOTH message sets describes more
/// than one account, and this returns a single answer, so it declines rather
/// than pick one — the caller only uses this to warn, and a warning naming the
/// wrong statement is worse than no warning.
#[must_use]
pub fn detect_statement_kind(content: &str) -> Option<StatementKind> {
    // `<CCSTMTRS` does not contain `<STMTRS`, so the bank probe cannot match a
    // credit-card statement by accident.
    let credit_card = content.contains("<CREDITCARDMSGSRSV1") || content.contains("<CCSTMTRS");
    let bank = content.contains("<BANKMSGSRSV1") || content.contains("<STMTRS");

    match (credit_card, bank) {
        (true, true) | (false, false) => None,
        (true, false) => Some(StatementKind::Liability),
        (false, true) => match leaf(content, "ACCTTYPE").as_deref() {
            // A line of credit is a liability even though it arrives in the
            // bank message set.
            Some("CREDITLINE") => Some(StatementKind::Liability),
            _ => Some(StatementKind::Asset),
        },
    }
}

/// Warn when the configured account contradicts what the statement says it is.
///
/// This only ever warns. Inferring the account *name* is not possible from an
/// OFX file — `Liabilities:CreditCard` is a guess about someone's chart of
/// accounts, not a fact in the document — and this module already refuses to
/// guess a currency for the same reason. What IS a fact is the side of the
/// balance sheet, and getting that wrong inverts the sign of every imported
/// transaction, which is worth saying out loud (#2256).
///
/// Returns `None` when the account's root is not one of the DEFAULT English
/// Assets/Liabilities names. This deliberately does not consult the ledger's
/// `name_assets` / `name_liabilities` options: the importer has no access to
/// ledger options, and plumbing them here for a warning is not worth the
/// coupling. The consequence is that a ledger using localized roots
/// (`Actifs`, `Passif`) gets no opinion either way — which is the right
/// outcome, since such a ledger is not misconfigured and warning at it would
/// be noise.
fn account_kind_mismatch(account: &str, statement: StatementKind) -> Option<String> {
    let types = rustledger_core::AccountTypes::default();
    let root = account.split(':').next().unwrap_or("");

    let configured = if root == types.assets {
        StatementKind::Asset
    } else if root == types.liabilities {
        StatementKind::Liability
    } else {
        return None;
    };

    if configured == statement {
        return None;
    }

    Some(format!(
        "statement describes {} but --account is `{account}`; \
         every imported amount will carry the opposite sign of what you expect. \
         Check the account, or ignore this if the mapping is deliberate.",
        statement.describe()
    ))
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
            fitid: leaf(block, "FITID"),
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

    /// Count directives by kind.
    ///
    /// These used to assert a bare `directives.len()`. Now that a statement
    /// with `LEDGERBAL` also yields a balance assertion, a total count no
    /// longer says what the test means, so they say it directly.
    fn txn_count(r: &ImportResult) -> usize {
        r.directives
            .iter()
            .filter(|d| matches!(d, Directive::Transaction(_)))
            .count()
    }

    fn balance_count(r: &ImportResult) -> usize {
        r.directives
            .iter()
            .filter(|d| matches!(d, Directive::Balance(_)))
            .count()
    }

    // ---- LEDGERBAL -> balance assertion --------------------------------------

    fn statement_with_ledgerbal(balamt: &str, dtasof: &str) -> String {
        format!(
            "OFXHEADER:100\n<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
             <BANKTRANLIST><STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115<TRNAMT>-50.00\
             <FITID>t1<NAME>COFFEE</STMTTRN></BANKTRANLIST>\n\
             <LEDGERBAL><BALAMT>{balamt}</BALAMT><DTASOF>{dtasof}</DTASOF></LEDGERBAL>\n\
             </STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>"
        )
    }

    /// A beancount `balance` asserts the balance at the START of its date,
    /// before that day's transactions. A bank's DTASOF figure is the CLOSING
    /// balance, after them. So the assertion must be dated the following day,
    /// or every statement whose last day has activity would fail.
    #[test]
    fn ledgerbal_is_asserted_the_day_after_dtasof() {
        let src = statement_with_ledgerbal("1234.56", "20240131");
        let result = OfxImporter
            .extract_from_string(&src, &ofx_cfg("Assets:Bank", "USD"))
            .expect("import succeeds");

        let balances: Vec<_> = result
            .directives
            .iter()
            .filter_map(|d| match d {
                Directive::Balance(b) => Some(b),
                _ => None,
            })
            .collect();
        assert_eq!(balances.len(), 1, "expected exactly one assertion");
        assert_eq!(
            balances[0].date.to_string(),
            "2024-02-01",
            "DTASOF 2024-01-31 must assert on 2024-02-01"
        );
        assert_eq!(balances[0].account.as_str(), "Assets:Bank");
    }

    /// OFX 1.x omits closing tags, so the element bound cannot rely on
    /// `</LEDGERBAL>`; the next sibling has to end it. Without this the SGML
    /// dialect would still read AVAILBAL's amount.
    #[test]
    fn the_ledgerbal_bound_works_without_closing_tags() {
        let sgml = "OFXHEADER:100\n<OFX>\n<BANKMSGSRSV1><STMTTRNRS><STMTRS>\n\
             <CURDEF>USD\n<BANKTRANLIST>\n\
             <STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115<TRNAMT>-50.00<FITID>t1<NAME>C\n\
             </BANKTRANLIST>\n<LEDGERBAL>\n<BALAMT>1000.00\n<DTASOF>20240131\n\
             <AVAILBAL>\n<BALAMT>250.00\n<DTASOF>20240131\n\
             </STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";

        let result = OfxImporter
            .extract_from_string(sgml, &ofx_cfg("Assets:Bank", "USD"))
            .expect("import succeeds");
        let Some(Directive::Balance(b)) = result
            .directives
            .iter()
            .find(|d| matches!(d, Directive::Balance(_)))
        else {
            panic!("expected an assertion");
        };
        assert_eq!(
            b.amount.number.to_string(),
            "1000.00",
            "took AVAILBAL's amount in the SGML dialect"
        );
    }

    /// Second review pass on #2279. The `LEDGERBAL` block ran to end-of-input,
    /// so its fields could be filled from whatever followed — and what follows
    /// is nearly always `<AVAILBAL>`, a different balance. A `LEDGERBAL`
    /// missing its `BALAMT` asserted the AVAILABLE balance as the ledger
    /// balance: a silently wrong number in the user's ledger.
    #[test]
    fn ledgerbal_fields_are_not_taken_from_availbal() {
        let stmt = |ledgerbal: &str| {
            format!(
                "OFXHEADER:100\n<OFX><BANKMSGSRSV1><STMTRS><CURDEF>USD\n\
                 <BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>-50.00<FITID>t1\
                 <NAME>C</STMTTRN></BANKTRANLIST>\n{ledgerbal}\n\
                 <AVAILBAL><BALAMT>250.00</BALAMT><DTASOF>20240131</DTASOF></AVAILBAL>\n\
                 </STMTRS></BANKMSGSRSV1></OFX>"
            )
        };

        for (case, ledgerbal) in [
            (
                "no DTASOF",
                "<LEDGERBAL><BALAMT>1000.00</BALAMT></LEDGERBAL>",
            ),
            (
                "no BALAMT",
                "<LEDGERBAL><DTASOF>20240131</DTASOF></LEDGERBAL>",
            ),
            ("empty", "<LEDGERBAL></LEDGERBAL>"),
        ] {
            let result = OfxImporter
                .extract_from_string(&stmt(ledgerbal), &ofx_cfg("Assets:Bank", "USD"))
                .expect("import succeeds");
            assert_eq!(
                balance_count(&result),
                0,
                "{case}: a partial LEDGERBAL must not borrow from AVAILBAL"
            );
        }

        // The complement: a complete LEDGERBAL still works with AVAILBAL after it.
        let result = OfxImporter
            .extract_from_string(
                &stmt("<LEDGERBAL><BALAMT>1000.00</BALAMT><DTASOF>20240131</DTASOF></LEDGERBAL>"),
                &ofx_cfg("Assets:Bank", "USD"),
            )
            .expect("import succeeds");
        assert_eq!(balance_count(&result), 1);
        let Some(Directive::Balance(b)) = result
            .directives
            .iter()
            .find(|d| matches!(d, Directive::Balance(_)))
        else {
            panic!("expected an assertion");
        };
        assert_eq!(
            b.amount.number.to_string(),
            "1000.00",
            "the LEDGERBAL amount, not AVAILBAL's"
        );
    }

    /// Deep-review finding on #2279: a file with two statements carries two
    /// closing balances, and every transaction is posted to one configured
    /// account. Taking the first silently dropped the second and emitted an
    /// assertion describing only part of the import.
    #[test]
    fn several_statements_emit_no_assertion_but_do_warn() {
        let src = "OFXHEADER:100\n<OFX><BANKMSGSRSV1>\n\
             <STMTTRNRS><STMTRS><CURDEF>USD\n\
             <BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>-50.00<FITID>a1\
             <NAME>US</STMTTRN></BANKTRANLIST>\n\
             <LEDGERBAL><BALAMT>100.00</BALAMT><DTASOF>20240131</DTASOF></LEDGERBAL>\n\
             </STMTRS></STMTTRNRS>\n\
             <STMTTRNRS><STMTRS><CURDEF>EUR\n\
             <BANKTRANLIST><STMTTRN><DTPOSTED>20240116<TRNAMT>-20.00<FITID>b1\
             <NAME>EUR</STMTTRN></BANKTRANLIST>\n\
             <LEDGERBAL><BALAMT>777.00</BALAMT><DTASOF>20240228</DTASOF></LEDGERBAL>\n\
             </STMTRS></STMTTRNRS>\n</BANKMSGSRSV1></OFX>";

        let result = OfxImporter
            .extract_from_string(src, &ofx_cfg("Assets:Bank", "USD"))
            .expect("import succeeds");

        assert_eq!(
            txn_count(&result),
            2,
            "both statements' transactions import"
        );
        assert_eq!(
            balance_count(&result),
            0,
            "an unattributable balance must not be guessed at"
        );
        assert!(
            result.warnings.iter().any(|w| w.contains("LEDGERBAL")),
            "declining must not be silent; got {:?}",
            result.warnings
        );
    }

    /// `DTASOF + 1` has to survive the end of the representable range rather
    /// than panicking on it.
    #[test]
    fn a_dtasof_at_the_end_of_time_yields_no_assertion() {
        let src = statement_with_ledgerbal("1.00", "99991231");
        let result = OfxImporter
            .extract_from_string(&src, &ofx_cfg("Assets:Bank", "USD"))
            .expect("import succeeds rather than panicking");
        assert_eq!(balance_count(&result), 0);
    }

    /// A partial LEDGERBAL is a statement we do not understand. Guessing at
    /// one is how a wrong assertion reaches someone's ledger.
    #[test]
    fn an_incomplete_ledgerbal_produces_no_assertion() {
        let cases = [
            // no DTASOF
            "OFXHEADER:100\n<OFX><BANKMSGSRSV1><STMTRS><CURDEF>USD\n\
             <BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>-1.00<FITID>t1\
             </STMTTRN></BANKTRANLIST>\n<LEDGERBAL><BALAMT>5.00</BALAMT></LEDGERBAL>\n\
             </STMTRS></BANKMSGSRSV1></OFX>"
                .to_string(),
            // no BALAMT
            "OFXHEADER:100\n<OFX><BANKMSGSRSV1><STMTRS><CURDEF>USD\n\
             <BANKTRANLIST><STMTTRN><DTPOSTED>20240115<TRNAMT>-1.00<FITID>t1\
             </STMTTRN></BANKTRANLIST>\n<LEDGERBAL><DTASOF>20240131</DTASOF></LEDGERBAL>\n\
             </STMTRS></BANKMSGSRSV1></OFX>"
                .to_string(),
            // unparsable amount
            statement_with_ledgerbal("not-a-number", "20240131"),
            // no LEDGERBAL at all
            cc_statement(),
        ];
        for (i, src) in cases.iter().enumerate() {
            let result = OfxImporter
                .extract_from_string(src, &ofx_cfg("Assets:Bank", "USD"))
                .expect("import still succeeds");
            assert!(
                !result
                    .directives
                    .iter()
                    .any(|d| matches!(d, Directive::Balance(_))),
                "case {i} should produce no assertion"
            );
        }
    }

    // ---- FITID -> link ------------------------------------------------------

    #[test]
    fn fitid_becomes_a_namespaced_link() {
        assert_eq!(fitid_link("202401150001"), Some("ofx-202401150001".into()));
        assert_eq!(fitid_link("  t1  "), Some("ofx-t1".into()));
    }

    /// Links lex as `^[a-zA-Z0-9-_/.]+`. A FITID is an opaque bank string, so
    /// anything else has to be replaced or the emitted ledger would not parse.
    #[test]
    fn fitid_characters_outside_the_link_charset_are_replaced() {
        assert_eq!(fitid_link("a b:c"), Some("ofx-a-b-c".into()));
        assert_eq!(
            fitid_link("2024-01-15/001.x_y"),
            Some("ofx-2024-01-15/001.x_y".into())
        );
        assert_eq!(fitid_link("ünïcode"), Some("ofx--n-code".into()));

        // Whatever comes out must match the lexer's link rule.
        for raw in ["a b:c", "ünïcode", "x@y#z", "2024-01-15/001.x_y", "t1"] {
            let link = fitid_link(raw).expect("produces a link");
            assert!(
                link.chars()
                    .all(|c| c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '/' | '.')),
                "{link:?} would not lex as a link"
            );
        }
    }

    /// An id that sanitizes to nothing would give every such transaction the
    /// same link, which is worse than none.
    #[test]
    fn a_fitid_with_no_usable_characters_yields_no_link() {
        for empty in ["", "   ", "***", "--", " - - "] {
            assert_eq!(fitid_link(empty), None, "input {empty:?}");
        }
    }

    #[test]
    fn extracted_transactions_carry_the_fitid_link() {
        let result = OfxImporter
            .extract_from_string(&cc_statement(), &ofx_cfg("Liabilities:Card", "USD"))
            .expect("import succeeds");
        let Directive::Transaction(txn) = &result.directives[0] else {
            panic!("expected a transaction");
        };
        assert_eq!(
            txn.links
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            vec!["ofx-t1".to_string()]
        );
    }

    // ---- #2256: statement-kind vs configured account -----------------------

    /// Minimal statements carrying one transaction, in each message set.
    fn cc_statement() -> String {
        "OFXHEADER:100\n<OFX><CREDITCARDMSGSRSV1><CCSTMTTRNRS><CCSTMTRS><CURDEF>USD\n\
         <BANKTRANLIST><STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115<TRNAMT>-50.00\
         <FITID>t1<NAME>COFFEE SHOP</STMTTRN></BANKTRANLIST>\n\
         </CCSTMTRS></CCSTMTTRNRS></CREDITCARDMSGSRSV1></OFX>"
            .to_string()
    }

    fn bank_statement(acct_type: &str) -> String {
        format!(
            "OFXHEADER:100\n<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\n\
             <BANKACCTFROM><ACCTID>1<ACCTTYPE>{acct_type}</BANKACCTFROM>\n\
             <BANKTRANLIST><STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115<TRNAMT>-50.00\
             <FITID>t1<NAME>COFFEE SHOP</STMTTRN></BANKTRANLIST>\n\
             </STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>"
        )
    }

    fn warnings_for(content: &str, account: &str) -> Vec<String> {
        OfxImporter
            .extract_from_string(content, &ofx_cfg(account, "USD"))
            .expect("import succeeds")
            .warnings
    }

    #[test]
    fn credit_card_statement_into_an_asset_account_warns() {
        let w = warnings_for(&cc_statement(), "Assets:Bank:Checking");
        assert_eq!(w.len(), 1, "expected one warning, got {w:?}");
        assert!(w[0].contains("liability account"), "got: {}", w[0]);
        assert!(w[0].contains("opposite sign"), "got: {}", w[0]);
    }

    #[test]
    fn bank_statement_into_a_liability_account_warns() {
        let w = warnings_for(&bank_statement("CHECKING"), "Liabilities:CreditCard");
        assert_eq!(w.len(), 1, "expected one warning, got {w:?}");
        assert!(w[0].contains("asset account"), "got: {}", w[0]);
    }

    /// A line of credit arrives in the BANK message set but is still a liability.
    #[test]
    fn creditline_acct_type_is_a_liability() {
        let w = warnings_for(&bank_statement("CREDITLINE"), "Assets:Bank:Checking");
        assert_eq!(
            w.len(),
            1,
            "CREDITLINE should warn against an asset account"
        );
        assert!(w[0].contains("liability account"), "got: {}", w[0]);
    }

    // Direct unit tests of the two decisions. The end-to-end silence tests
    // below cannot distinguish "correctly quiet" from "feature deleted", so
    // these assert the logic positively instead.

    #[test]
    fn detect_statement_kind_reads_both_signals() {
        assert_eq!(
            detect_statement_kind(&cc_statement()),
            Some(StatementKind::Liability)
        );
        assert_eq!(
            detect_statement_kind(&bank_statement("CHECKING")),
            Some(StatementKind::Asset)
        );
        assert_eq!(
            detect_statement_kind(&bank_statement("CREDITLINE")),
            Some(StatementKind::Liability),
            "CREDITLINE is a liability inside the bank message set"
        );
        // Ambiguous and silent inputs both decline.
        let mixed = format!("{}\n{}", cc_statement(), bank_statement("CHECKING"));
        assert_eq!(detect_statement_kind(&mixed), None, "two message sets");
        assert_eq!(detect_statement_kind("<OFX></OFX>"), None, "neither");
    }

    #[test]
    fn account_kind_mismatch_only_fires_on_a_recognized_contradiction() {
        use StatementKind::{Asset, Liability};
        assert!(account_kind_mismatch("Assets:Bank", Liability).is_some());
        assert!(account_kind_mismatch("Liabilities:Card", Asset).is_some());
        assert!(account_kind_mismatch("Assets:Bank", Asset).is_none());
        assert!(account_kind_mismatch("Liabilities:Card", Liability).is_none());
        // Unrecognized roots yield no opinion, in either direction.
        assert!(account_kind_mismatch("Actifs:Banque", Liability).is_none());
        assert!(account_kind_mismatch("Passif:Carte", Asset).is_none());
        assert!(account_kind_mismatch("", Asset).is_none());
    }

    // ---- negative controls: the check must be able to stay silent ----------

    #[test]
    fn matching_accounts_do_not_warn() {
        assert!(warnings_for(&cc_statement(), "Liabilities:CreditCard").is_empty());
        assert!(warnings_for(&bank_statement("CHECKING"), "Assets:Bank:Checking").is_empty());
        assert!(warnings_for(&bank_statement("SAVINGS"), "Assets:Bank:Savings").is_empty());
    }

    /// Localized account roots are not misconfiguration. An unrecognized root
    /// means "no opinion", not "mismatch" — warning at a French ledger for
    /// using `Passif` would be noise.
    #[test]
    fn unrecognized_account_root_does_not_warn() {
        assert!(warnings_for(&cc_statement(), "Actifs:Banque").is_empty());
        assert!(warnings_for(&bank_statement("CHECKING"), "Passif:Carte").is_empty());
    }

    /// A file carrying both message sets describes more than one account, and
    /// the check returns a single answer, so it must decline.
    #[test]
    fn a_mixed_file_does_not_warn() {
        let mixed = format!("{}\n{}", cc_statement(), bank_statement("CHECKING"));
        assert!(
            warnings_for(&mixed, "Assets:Bank:Checking").is_empty(),
            "an ambiguous file must not produce a confident warning"
        );
    }

    #[test]
    fn a_statement_with_neither_message_set_does_not_warn() {
        let bare = "OFXHEADER:100\n<OFX><CURDEF>USD\n\
                    <BANKTRANLIST><STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240115\
                    <TRNAMT>-50.00<FITID>t1<NAME>COFFEE</STMTTRN></BANKTRANLIST></OFX>";
        assert!(warnings_for(bare, "Assets:Bank:Checking").is_empty());
    }

    /// The warning is advisory: a mismatch must not cost the user their import.
    #[test]
    fn the_warning_does_not_suppress_transactions() {
        let result = OfxImporter
            .extract_from_string(&cc_statement(), &ofx_cfg("Assets:Bank:Checking", "USD"))
            .expect("import succeeds despite the mismatch");
        assert_eq!(result.warnings.len(), 1);
        assert_eq!(
            result.directives.len(),
            1,
            "the transaction must still be imported"
        );
    }

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
        assert_eq!(txn_count(&import_result), 2);
        assert_eq!(
            balance_count(&import_result),
            1,
            "LEDGERBAL yields one assertion"
        );
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
        assert_eq!(txn_count(&import_result), 1);
        assert_eq!(
            balance_count(&import_result),
            1,
            "LEDGERBAL yields one assertion"
        );
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
        assert_eq!(txn_count(&import_result), 1);
        assert_eq!(
            balance_count(&import_result),
            1,
            "LEDGERBAL yields one assertion"
        );
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
        assert_eq!(txn_count(&import_result), 1);
        assert_eq!(
            balance_count(&import_result),
            1,
            "LEDGERBAL yields one assertion"
        );
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
        assert_eq!(txn_count(&import_result), 1);
        assert_eq!(
            balance_count(&import_result),
            1,
            "LEDGERBAL yields one assertion"
        );
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
