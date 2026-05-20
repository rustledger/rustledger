//! Example WASM importer for rustledger — a minimal CSV bank-statement
//! parser implemented against the importer ABI.
//!
//! This is a **reference implementation**, not a production importer.
//! It exists to show external authors what a real-world `extract` body
//! looks like end to end:
//!
//! - Reads `ImporterInput::content` as UTF-8 CSV.
//! - Expects three columns: `Date`, `Description`, `Amount` (header row
//!   required).
//! - Emits one Beancount `Transaction` per row with two postings:
//!   `config.account` and a default expense/income account (chosen by
//!   sign of the amount).
//! - Surfaces parse failures as per-row warnings (best-effort import:
//!   one bad row doesn't kill the whole statement).
//!
//! Production importers will typically want richer parsing — date
//! formats, locale-aware amount parsing, mapping rules, fingerprints
//! for dedup. The host crate's `CsvImporter` covers that territory; the
//! WASM ABI lets a third-party reimplement any of it.
//!
//! # Building
//!
//! ```sh
//! rustup target add wasm32-unknown-unknown
//! cargo build --release --target wasm32-unknown-unknown
//! # Output: target/wasm32-unknown-unknown/release/wasm_importer_csv_example.wasm
//! ```
//!
//! # Loading from the host
//!
//! ```ignore
//! use rustledger_importer::WasmImporter;
//! let importer = WasmImporter::load(
//!     "path/to/wasm_importer_csv_example.wasm",
//! )?;
//! // Now usable like any other Importer — register, identify, extract.
//! ```

use rustledger_plugin_types::{
    AmountData, DirectiveData, DirectiveWrapper, ImporterInput, ImporterOutput, PluginError,
    PostingData, TransactionData, wasm_importer_main,
};

/// Identify: handle any `.csv` path. Real importers often peek at the
/// header row too (via the path string alone — `identify` doesn't see
/// file content), but extension-only is a reasonable default for an
/// example.
fn identify(path: &str) -> bool {
    path.to_ascii_lowercase().ends_with(".csv")
}

/// Extract: parse `input.content` as `Date,Description,Amount` CSV and
/// emit one transaction per row.
///
/// Errors during row parsing are surfaced as per-row entries in
/// `output.errors` with severity `Warning` — the host's bridge formats
/// these as `"warning <file>:<line>: <msg>"` and merges them into the
/// result's warnings list. We deliberately don't abort on the first bad
/// row: bank exports often have a trailing balance row or non-data
/// metadata that the importer should skip rather than reject.
fn extract(input: ImporterInput) -> ImporterOutput {
    let mut directives = Vec::new();
    let mut errors = Vec::new();

    let content = match std::str::from_utf8(&input.content) {
        Ok(s) => s,
        Err(e) => {
            // No directives at all if the file isn't UTF-8 — but report
            // it as a structured error so the host can surface it
            // through the same path as per-row errors.
            return ImporterOutput {
                directives,
                warnings: vec![],
                errors: vec![PluginError::error(format!(
                    "file is not valid UTF-8: {e}"
                ))],
            };
        }
    };

    let default_currency = input.currency.as_deref().unwrap_or("USD");

    // Skip the header row. We don't validate header names — production
    // importers should, but the example stays minimal.
    for (i, line) in content.lines().enumerate().skip(1) {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let lineno = u32::try_from(i + 1).unwrap_or(u32::MAX);

        let Some((date, description, amount_str)) = parse_row(line) else {
            errors.push(
                PluginError::warning(format!(
                    "skipping malformed row (expected 3 comma-separated fields): {line}"
                ))
                .at(input.path.clone(), lineno),
            );
            continue;
        };

        // Amount validation: ensure it's parseable as a signed decimal
        // (digits, optional sign, optional decimal point). We don't
        // re-format — Beancount accepts whatever the importer emits as
        // long as it's a valid decimal literal.
        if !is_decimal_literal(amount_str) {
            errors.push(
                PluginError::warning(format!(
                    "skipping row with unparsable amount `{amount_str}`"
                ))
                .at(input.path.clone(), lineno),
            );
            continue;
        }

        let counter_account = if amount_str.starts_with('-') {
            // Money out — expense.
            "Expenses:Unknown"
        } else {
            // Money in — income. Beancount expects income postings to
            // be negative, so negate the amount on the counter side.
            "Income:Unknown"
        };
        let counter_amount = negate_amount(amount_str);

        directives.push(DirectiveWrapper {
            directive_type: String::new(),
            date: date.to_string(),
            filename: Some(input.path.clone()),
            lineno: Some(lineno),
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: description.to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: input.account.clone(),
                        units: Some(AmountData {
                            number: amount_str.to_string(),
                            currency: default_currency.to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                                            span: None,
                    },
                    PostingData {
                        account: counter_account.to_string(),
                        units: Some(AmountData {
                            number: counter_amount,
                            currency: default_currency.to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                                            span: None,
                    },
                ],
            }),
        });
    }

    ImporterOutput {
        directives,
        warnings: vec![],
        errors,
    }
}

/// Naive CSV row parser: splits on commas. Does NOT handle quoted
/// fields containing commas — production importers should use a real
/// CSV library, but pulling `csv` into a wasm32 cdylib (~150 KiB)
/// inflates the example beyond its illustrative purpose.
///
/// Returns `(date, description, amount)` for a 3-field row, or `None`.
fn parse_row(line: &str) -> Option<(&str, &str, &str)> {
    let mut parts = line.splitn(3, ',');
    let date = parts.next()?.trim();
    let description = parts.next()?.trim();
    let amount = parts.next()?.trim();
    if date.is_empty() || amount.is_empty() {
        return None;
    }
    Some((date, description, amount))
}

/// Cheap check that `s` looks like a decimal literal: optional `-`,
/// at least one digit, optional `.fraction`. Real importers should
/// parse to a Decimal type for arithmetic; we only need to detect
/// "this row's amount is junk" so we can skip it.
fn is_decimal_literal(s: &str) -> bool {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    let mut i = 0;
    if bytes[0] == b'-' || bytes[0] == b'+' {
        i += 1;
    }
    let mut saw_digit = false;
    let mut saw_dot = false;
    while i < bytes.len() {
        match bytes[i] {
            b'0'..=b'9' => saw_digit = true,
            b'.' if !saw_dot => saw_dot = true,
            _ => return false,
        }
        i += 1;
    }
    saw_digit
}

/// Negate a decimal literal string by toggling the leading sign.
/// Cheaper than parsing → Decimal → re-formatting, and the input has
/// already been validated by [`is_decimal_literal`].
fn negate_amount(s: &str) -> String {
    if let Some(rest) = s.strip_prefix('-') {
        rest.to_string()
    } else if let Some(rest) = s.strip_prefix('+') {
        format!("-{rest}")
    } else {
        format!("-{s}")
    }
}

wasm_importer_main! {
    name: "csv-example",
    description: "Minimal CSV bank-statement importer (Date, Description, Amount)",
    identify: identify,
    extract: extract,
}
