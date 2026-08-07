//! The `importers.toml` entry schema and its mapping onto [`ImporterConfig`].
//!
//! This is the canonical parser for one `[[importers]]` entry — the schema
//! documented in `docs/commands/extract.md`. It lives here (not in the CLI)
//! so every consumer of the declarative config speaks the same dialect: the
//! `rledger extract` command and the WASI component's `importer` interface
//! both build their [`ImporterConfig`] through [`build_config_from_entry`].
//! File *discovery* (search paths, `~` expansion, the `wasm_importer_dir`
//! setting) stays CLI-side — it is filesystem policy, not schema.
//!
//! Gated behind the `toml-config` feature so slim builds don't pull
//! `toml`/`serde`.

use crate::ImporterConfig;
use crate::config::CsvConfigBuilder;
use anyhow::{Result, anyhow};
use format_num_pattern::Locale;
use serde::Deserialize;
use std::collections::HashMap;
use std::str::FromStr;

/// A single importer entry in `importers.toml`.
#[derive(Debug, Deserialize)]
pub struct ImporterEntry {
    /// Name used to select this importer via --importer flag.
    pub name: String,
    /// Optional glob pattern to auto-identify this importer by filename.
    pub filename_pattern: Option<String>,
    /// Target account for imported transactions.
    pub account: Option<String>,
    /// Currency (default: USD).
    pub currency: Option<String>,
    /// Date column name or 0-based index.
    pub date_column: Option<toml::Value>,
    /// Date format (strftime-style).
    pub date_format: Option<String>,
    /// Narration/description column name or index.
    pub narration_column: Option<toml::Value>,
    /// Payee column name or index.
    pub payee_column: Option<toml::Value>,
    /// Amount column name or index.
    pub amount_column: Option<toml::Value>,
    /// Per-row currency column name or index.
    pub currency_column: Option<toml::Value>,
    /// Debit column name or index.
    pub debit_column: Option<toml::Value>,
    /// Credit column name or index.
    pub credit_column: Option<toml::Value>,
    /// A second date column (header name) to preserve as transaction metadata
    /// — e.g. a value date alongside the booking `date_column` (#1623).
    pub secondary_date_column: Option<String>,
    /// strftime-style format for `secondary_date_column` (default: `date_format`).
    pub secondary_date_format: Option<String>,
    /// Metadata key the secondary date is stored under (default: a slug of the
    /// column name, e.g. `value_date`).
    pub secondary_date_key: Option<String>,
    /// Amount locale for number parsing (e.g. `de_DE` so `21,12` reads as
    /// 21.12). Mirrors the `--amount-locale` CLI flag.
    pub amount_locale: Option<String>,
    /// Amount format pattern (`format_num_pattern` style). Mirrors the
    /// `--amount-format` CLI flag.
    pub amount_format: Option<String>,
    /// CSV delimiter character.
    pub delimiter: Option<String>,
    /// Number of rows to skip.
    pub skip_rows: Option<usize>,
    /// Whether the CSV has a header row.
    #[serde(default)]
    pub skip_header: Option<bool>,
    /// Whether to invert amount signs.
    #[serde(default)]
    pub invert_amounts: Option<bool>,
    /// Default expense account for unmatched negative-amount (money out) transactions.
    pub default_expense: Option<String>,
    /// Default income account for unmatched positive-amount (money in) transactions.
    pub default_income: Option<String>,
    /// Account mappings: pattern → account.
    #[serde(default)]
    pub mappings: HashMap<String, String>,
    /// Categorize via the built-in merchant dictionary (off by default).
    pub use_merchant_dict: Option<bool>,
    /// External preprocessing command (argv array). When set, the command
    /// runs BEFORE format detection and extraction: any `{input}` argument
    /// is replaced by the statement's path, stdout becomes the content the
    /// rest of the pipeline (inference, column mapping) consumes. This is
    /// how PDF and other unsupported formats import today, until a native
    /// parser exists.
    ///
    /// This is an ARGV ARRAY, not a shell command line: there is no shell, so
    /// `|`, `>` and `&&` are ordinary arguments rather than operators. A
    /// single program:
    ///
    /// ```toml
    /// preprocess = ["pdftotext", "-layout", "{input}", "-"]
    /// ```
    ///
    /// A pipeline needs a shell, asked for explicitly — and the path goes in
    /// as a POSITIONAL argument, never spliced into the command string:
    ///
    /// ```toml
    /// preprocess = ["sh", "-c", "pdftotext -layout \"$1\" - | to-csv", "_", "{input}"]
    /// ```
    ///
    /// `sh -c` parses its argument as source, so a `{input}` written inside it
    /// would let a filename become code: `a;rm -rf ~;b.pdf` is three commands.
    /// The filename is not the config author's — importing files you
    /// downloaded is the point — so the CLI REJECTS that shape. `{input}` as
    /// its own argv element is always safe; a shell never re-parses `$1`.
    ///
    /// **Trust model**: this executes a program named by the config, so the
    /// CLI honors it only when the config is yours — passed with `--config`,
    /// or in your user config directory. A `./importers.toml` picked up from
    /// the current directory is IGNORED for this field, with a warning,
    /// because that file belongs to whoever put it there rather than to you.
    /// Honored by the CLI only; the WASI component cannot exec and rejects
    /// entries that set it (the host runs the preprocessor and passes its
    /// output as content instead).
    #[serde(default)]
    pub preprocess: Option<Vec<String>>,
}

impl ImporterEntry {
    /// Parse a single entry from a bare TOML table, e.g.
    /// `name = "bank"\ndate_column = "Date"`. This is the config shape the
    /// component's `importer.extract` accepts — one entry, no
    /// `[[importers]]` wrapper.
    ///
    /// # Errors
    /// Returns an error when the TOML is malformed or missing `name`.
    pub fn from_toml_str(toml_str: &str) -> Result<Self> {
        toml::from_str(toml_str).map_err(|e| anyhow!("invalid importer config: {e}"))
    }
}

/// Apply a CSV column flag that may be a header name or a bare 0-based index.
///
/// CSV column flags are documented as "name or index". A value that parses as a
/// non-negative integer is treated as a positional index (so headerless CSVs
/// import correctly); anything else is a column name. Shared by the CLI-argument
/// and `importers.toml` config paths so both honor numeric columns.
pub fn apply_column(
    builder: CsvConfigBuilder,
    col: &str,
    by_index: impl FnOnce(CsvConfigBuilder, usize) -> CsvConfigBuilder,
    by_name: impl FnOnce(CsvConfigBuilder, &str) -> CsvConfigBuilder,
) -> CsvConfigBuilder {
    match col.parse::<usize>() {
        Ok(i) => by_index(builder, i),
        Err(_) => by_name(builder, col),
    }
}

/// Parse a TOML value as a column spec string (either a string name or integer index).
#[must_use]
pub fn parse_column_value(value: &toml::Value) -> Option<String> {
    match value {
        toml::Value::String(s) => Some(s.clone()),
        toml::Value::Integer(i) => Some(i.to_string()),
        _ => None,
    }
}

/// Like [`parse_column_value`], but a wrong TOML type is an ERROR naming the
/// field — a mistyped `amount_column = 2.0` must not silently fall back to
/// the builder's default column (review finding on the 3.5.0 component
/// surface; previously the CLI silently ignored such values too).
fn require_column_value(field: &str, value: &toml::Value) -> Result<String> {
    parse_column_value(value).ok_or_else(|| {
        anyhow!("`{field}` must be a column name (string) or 0-based index (integer), got: {value}")
    })
}

/// Parse an amount-locale name (e.g. `de_DE`, `en_US`) into a [`Locale`].
///
/// Emits a consistent error for an unrecognized name. Shared by the CLI's
/// `--amount-locale` flag and the `amount_locale` config field.
///
/// # Errors
/// Returns an error when `name` is not a recognized locale.
pub fn parse_amount_locale(name: &str) -> Result<Locale> {
    Locale::from_str(name).map_err(|_| anyhow!("{name} is not a valid locale"))
}

/// Build an [`ImporterConfig`] from a named importer entry.
///
/// # Errors
/// Returns an error when a field fails to validate (e.g. an unknown
/// `amount_locale`) or the assembled config is incomplete.
pub fn build_config_from_entry(entry: &ImporterEntry) -> Result<ImporterConfig> {
    let mut builder = ImporterConfig::csv();

    if let Some(ref account) = entry.account {
        builder = builder.account(account);
    }
    if let Some(ref currency) = entry.currency {
        builder = builder.currency(currency);
    }
    if let Some(ref val) = entry.date_column {
        let col = require_column_value("date_column", val)?;
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::date_column_index,
            |b, n| b.date_column(n),
        );
    }
    if let Some(ref fmt) = entry.date_format {
        builder = builder.date_format(fmt);
    }
    if let Some(ref col) = entry.secondary_date_column {
        // Format defaults to the primary date format; key defaults to a slug of
        // the column name (e.g. "Value Date" -> "value_date").
        let fmt = entry
            .secondary_date_format
            .clone()
            .or_else(|| entry.date_format.clone())
            .unwrap_or_else(|| "%Y-%m-%d".to_string());
        let key = entry.secondary_date_key.clone().unwrap_or_else(|| {
            col.trim()
                .to_lowercase()
                .replace(|c: char| !c.is_ascii_alphanumeric(), "_")
        });
        builder = builder.secondary_date(col, fmt, key);
    }
    if let Some(ref val) = entry.narration_column {
        let col = require_column_value("narration_column", val)?;
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::narration_column_index,
            |b, n| b.narration_column(n),
        );
    }
    if let Some(ref val) = entry.payee_column {
        let col = require_column_value("payee_column", val)?;
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::payee_column_index,
            |b, n| b.payee_column(n),
        );
    }
    if let Some(ref val) = entry.amount_column {
        let col = require_column_value("amount_column", val)?;
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::amount_column_index,
            |b, n| b.amount_column(n),
        );
    }
    if let Some(ref val) = entry.currency_column {
        let col = require_column_value("currency_column", val)?;
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::currency_column_index,
            |b, n| b.currency_column(n),
        );
    }
    if let Some(ref val) = entry.debit_column {
        let col = require_column_value("debit_column", val)?;
        builder = builder.debit_column(&col);
    }
    if let Some(ref val) = entry.credit_column {
        let col = require_column_value("credit_column", val)?;
        builder = builder.credit_column(&col);
    }
    if let Some(ref locale) = entry.amount_locale {
        builder = builder.amount_locale(parse_amount_locale(locale)?);
    }
    if let Some(ref format) = entry.amount_format {
        builder = builder.amount_format(format);
    }
    if let Some(ref delim) = entry.delimiter
        && let Some(c) = delim.chars().next()
    {
        builder = builder.delimiter(c);
    }
    if let Some(skip) = entry.skip_rows {
        builder = builder.skip_rows(skip);
    }
    if let Some(skip_header) = entry.skip_header {
        builder = builder.has_header(!skip_header);
    }
    if let Some(invert) = entry.invert_amounts {
        builder = builder.invert_sign(invert);
    }
    if let Some(ref account) = entry.default_expense {
        builder = builder.default_expense(account);
    }
    if let Some(ref account) = entry.default_income {
        builder = builder.default_income(account);
    }
    if !entry.mappings.is_empty() {
        let mut mappings: Vec<(String, String)> = entry
            .mappings
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        mappings.sort_by_key(|a| std::cmp::Reverse(a.0.len()));
        builder = builder.mappings(mappings);
    }

    if let Some(enable) = entry.use_merchant_dict {
        builder = builder.use_merchant_dict(enable);
    }

    builder.build()
}

/// Render an inferred CSV mapping as an `importers.toml` entry (bare table).
///
/// The output round-trips through [`ImporterEntry::from_toml_str`] +
/// [`build_config_from_entry`], so a host can show it to the user, let them
/// edit it, and pass it straight back to an extract call. Only inferred
/// fields are emitted; account/currency are the caller's to add.
///
/// # Errors
/// Serialization of a flat table of scalars should not fail; the error is
/// still propagated rather than swallowed so a future non-scalar field
/// can't silently produce an empty config.
pub fn entry_toml_from_inferred(
    name: &str,
    inferred: &crate::csv_inference::InferredCsvConfig,
) -> Result<String> {
    use crate::config::ColumnSpec;
    use toml::Value;

    fn col(spec: &ColumnSpec) -> Value {
        match spec {
            ColumnSpec::Name(n) => Value::String(n.clone()),
            #[allow(clippy::cast_possible_wrap)]
            ColumnSpec::Index(i) => Value::Integer(*i as i64),
        }
    }

    let mut t = toml::value::Table::new();
    t.insert("name".into(), Value::String(name.to_string()));
    t.insert(
        "delimiter".into(),
        Value::String(inferred.delimiter.to_string()),
    );
    if !inferred.has_header {
        t.insert("skip_header".into(), Value::Boolean(true));
    }
    t.insert("date_column".into(), col(&inferred.date_column));
    t.insert(
        "date_format".into(),
        Value::String(inferred.date_format.clone()),
    );
    if let Some(ref c) = inferred.amount_column {
        t.insert("amount_column".into(), col(c));
    }
    if let Some(ref c) = inferred.debit_column {
        t.insert("debit_column".into(), col(c));
    }
    if let Some(ref c) = inferred.credit_column {
        t.insert("credit_column".into(), col(c));
    }
    if let Some(ref c) = inferred.narration_column {
        t.insert("narration_column".into(), col(c));
    }
    if let Some(ref c) = inferred.payee_column {
        t.insert("payee_column".into(), col(c));
    }
    if let Some(ref c) = inferred.currency_column {
        t.insert("currency_column".into(), col(c));
    }
    // Inference only ever produces a Name column here (secondary-date
    // detection is header-gated — see `csv_inference`'s SecondaryDate
    // construction), so the Name-only match is lossless. Pinned by
    // `inferred_secondary_date_is_always_named`.
    if let Some(ref sd) = inferred.secondary_date
        && let ColumnSpec::Name(ref n) = sd.column
    {
        t.insert("secondary_date_column".into(), Value::String(n.clone()));
        t.insert(
            "secondary_date_format".into(),
            Value::String(sd.format.clone()),
        );
        t.insert(
            "secondary_date_key".into(),
            Value::String(sd.meta_key.clone()),
        );
    }
    if let Some(locale) = inferred.amount_locale {
        // `Locale`'s variant names ARE the locale codes (`de_DE`, `en_US`),
        // so the Debug form round-trips through `Locale::from_str` /
        // `parse_amount_locale`. Pinned by `inferred_locale_round_trips`.
        t.insert("amount_locale".into(), Value::String(format!("{locale:?}")));
    }
    toml::to_string(&Value::Table(t)).map_err(|e| anyhow!("serializing inferred config: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::ImporterType;

    #[derive(Debug, Deserialize)]
    struct EntriesWrapper {
        importers: Vec<ImporterEntry>,
    }

    /// Regression for #1133: `amount_locale` / `amount_format` set in
    /// `importers.toml` were silently ignored — only the matching CLI flags
    /// (`--amount-locale` / `--amount-format`) applied them.
    #[test]
    fn build_config_from_entry_applies_amount_locale_and_format() {
        let src = r##"
[[importers]]
name = "de-locale"
account = "Assets:Bank"
amount_locale = "de_DE"

[[importers]]
name = "de-format"
account = "Assets:Bank"
amount_locale = "de_DE"
amount_format = "#.##0,00"
"##;
        let file: EntriesWrapper = toml::from_str(src).expect("toml parses");

        // amount_locale: in de_DE the comma is the decimal separator, so
        // "21,12" reads as 21.12 (the #1133 bug read it as 2112).
        let cfg = build_config_from_entry(&file.importers[0]).expect("config builds");
        let ImporterType::Csv(csv) = &cfg.importer_type;
        let fmt = csv.compile_amount_format().expect("format compiles");
        assert_eq!(
            fmt.parse("21,12").expect("amount parses").to_string(),
            "21.12"
        );

        // amount_format also flows through from the toml entry.
        let cfg = build_config_from_entry(&file.importers[1]).expect("config builds");
        let ImporterType::Csv(csv) = &cfg.importer_type;
        assert_eq!(csv.amount_format.as_deref(), Some("#.##0,00"));
    }

    /// The component's config shape: one bare TOML table, no `[[importers]]`.
    #[test]
    fn entry_parses_from_bare_table() {
        let entry = ImporterEntry::from_toml_str(
            r#"
name = "bank"
account = "Assets:Bank"
date_column = "Date"
amount_column = 2
"#,
        )
        .expect("bare table parses");
        assert_eq!(entry.name, "bank");
        // Numeric columns survive as indices.
        assert_eq!(
            parse_column_value(entry.amount_column.as_ref().expect("set")),
            Some("2".to_string())
        );
        build_config_from_entry(&entry).expect("config builds");
    }

    #[test]
    fn preprocess_parses_as_argv() {
        let entry = ImporterEntry::from_toml_str(
            "name = \"pdf\"\npreprocess = [\"pdftotext\", \"-layout\", \"{input}\", \"-\"]",
        )
        .expect("parses");
        assert_eq!(
            entry.preprocess.as_deref(),
            Some(
                &[
                    "pdftotext".to_string(),
                    "-layout".into(),
                    "{input}".into(),
                    "-".into()
                ][..]
            )
        );
    }

    #[test]
    fn entry_without_name_is_rejected() {
        assert!(ImporterEntry::from_toml_str("account = \"Assets:Bank\"").is_err());
    }

    /// Inference output round-trips: serialize → parse → build a config.
    #[test]
    fn inferred_entry_toml_round_trips() {
        let content =
            "Date,Description,Amount\n2026-07-01,Coffee,-4.50\n2026-07-02,Salary,2500.00\n";
        let inferred = crate::csv_inference::infer_csv_config(content).expect("inferable");
        let toml_str = entry_toml_from_inferred("inferred", &inferred).expect("serializes");
        let entry = ImporterEntry::from_toml_str(&toml_str).expect("round-trips");
        assert_eq!(entry.name, "inferred");
        build_config_from_entry(&entry).expect("config builds");
    }

    /// A mistyped column value is an error, not a silent fallback to the
    /// default column.
    #[test]
    fn wrong_column_type_is_rejected() {
        let entry = ImporterEntry::from_toml_str(
            "name = \"bad\"\naccount = \"Assets:Bank\"\namount_column = 2.0",
        )
        .expect("parses as TOML");
        let err = build_config_from_entry(&entry).expect_err("must reject");
        assert!(err.to_string().contains("amount_column"), "{err}");
    }

    /// Drift guard: the TOML round-trip path (`entry_toml_from_inferred` →
    /// `build_config_from_entry`) must agree with the canonical direct
    /// mapping (`InferredCsvConfig::to_csv_config`) on the same inference.
    #[test]
    fn inferred_toml_path_matches_to_csv_config() {
        let content = "Booking Date,Value Date,Description,Amount\n\
                       2026-07-01,2026-07-02,Coffee,-4.50\n\
                       2026-07-03,2026-07-04,Salary,2500.00\n";
        let inferred = crate::csv_inference::infer_csv_config(content).expect("inferable");
        let direct = inferred.to_csv_config();

        let toml_str = entry_toml_from_inferred("x", &inferred).expect("serializes");
        let entry = ImporterEntry::from_toml_str(&toml_str).expect("round-trips");
        let via_toml = build_config_from_entry(&entry).expect("config builds");
        let ImporterType::Csv(via_toml) = &via_toml.importer_type;

        assert_eq!(
            format!("{:?}", via_toml.date_column),
            format!("{:?}", direct.date_column)
        );
        assert_eq!(via_toml.date_format, direct.date_format);
        assert_eq!(
            format!("{:?}", via_toml.amount_column),
            format!("{:?}", direct.amount_column)
        );
        assert_eq!(
            format!("{:?}", via_toml.narration_column),
            format!("{:?}", direct.narration_column)
        );
        assert_eq!(via_toml.delimiter, direct.delimiter);
        assert_eq!(via_toml.has_header, direct.has_header);
        assert_eq!(
            format!("{:?}", via_toml.secondary_date),
            format!("{:?}", direct.secondary_date),
            "secondary date must survive the TOML round trip"
        );
    }

    /// The invariant `entry_toml_from_inferred`'s Name-only secondary-date
    /// match relies on: inference never emits an Index secondary column.
    #[test]
    fn inferred_secondary_date_is_always_named() {
        let content = "Booking Date,Value Date,Description,Amount\n\
                       2026-07-01,2026-07-02,Coffee,-4.50\n";
        let inferred = crate::csv_inference::infer_csv_config(content).expect("inferable");
        if let Some(sd) = inferred.secondary_date {
            assert!(matches!(sd.column, crate::config::ColumnSpec::Name(_)));
        }
    }

    /// The Debug form of `Locale` is the locale code and parses back —
    /// the contract `entry_toml_from_inferred` relies on.
    #[test]
    fn inferred_locale_round_trips() {
        let locale = parse_amount_locale("de_DE").expect("valid locale");
        assert_eq!(
            parse_amount_locale(&format!("{locale:?}")).expect("round-trips"),
            locale
        );
    }
}
