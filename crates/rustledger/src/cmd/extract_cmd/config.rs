//! Importers TOML configuration for extract command.

use anyhow::{Context, Result, anyhow};
use rustledger_importer::ImporterConfig;
use rustledger_importer::config::CsvConfigBuilder;
use serde::Deserialize;
use std::collections::HashMap;
use std::path::Path;
#[cfg(feature = "python-plugin-wasm")]
use std::path::PathBuf;

/// Top-level importers configuration file.
#[derive(Debug, Deserialize)]
pub(super) struct ImportersFile {
    /// Director(ies) to scan for WASM importer modules at startup.
    /// Accepts either a single string for the common case
    /// (`wasm_importer_dir = "~/imp"`) or a list
    /// (`wasm_importer_dir = ["a", "b"]`). The CLI
    /// `--wasm-importer-dir` flag(s) override this setting entirely
    /// when present.
    #[cfg(feature = "python-plugin-wasm")]
    #[serde(default)]
    pub(super) wasm_importer_dir: WasmDirSetting,
    #[serde(default)]
    pub(super) importers: Vec<ImporterEntry>,
}

#[cfg(feature = "python-plugin-wasm")]
/// TOML-side representation of `wasm_importer_dir` — accepts a
/// bare string or a list of strings so the common single-dir case
/// stays ergonomic while multi-dir is also expressible.
#[derive(Debug, Default, Deserialize)]
#[serde(untagged)]
pub(super) enum WasmDirSetting {
    #[default]
    None,
    Single(PathBuf),
    Many(Vec<PathBuf>),
}

#[cfg(feature = "python-plugin-wasm")]
impl WasmDirSetting {
    /// Normalize into a flat `Vec<PathBuf>` for the registry-build
    /// pipeline. Empty for [`Self::None`].
    pub(super) fn into_vec(self) -> Vec<PathBuf> {
        match self {
            Self::None => Vec::new(),
            Self::Single(p) => vec![p],
            Self::Many(v) => v,
        }
    }
}

#[cfg(feature = "python-plugin-wasm")]
/// Expand a leading `~` in a path to the user's home directory.
/// Without this, `wasm_importer_dir = "~/imp"` in `importers.toml`
/// would be read as a literal `~/imp` path that doesn't exist — a
/// real footgun for a config setting where shell expansion isn't
/// available.
///
/// Only handles `~` and `~/...` (no `~user/...`); falls through to
/// the original path if the home directory can't be determined.
pub(super) fn expand_tilde(path: &Path) -> PathBuf {
    let s = path.to_string_lossy();
    if s == "~" {
        return dirs::home_dir().unwrap_or_else(|| path.to_path_buf());
    }
    if let Some(rest) = s.strip_prefix("~/")
        && let Some(home) = dirs::home_dir()
    {
        return home.join(rest);
    }
    path.to_path_buf()
}

/// A single importer entry in importers.toml.
#[derive(Debug, Deserialize)]
pub(super) struct ImporterEntry {
    /// Name used to select this importer via --importer flag.
    pub(super) name: String,
    /// Optional glob pattern to auto-identify this importer by filename.
    pub(super) filename_pattern: Option<String>,
    /// Target account for imported transactions.
    pub(super) account: Option<String>,
    /// Currency (default: USD).
    pub(super) currency: Option<String>,
    /// Date column name or 0-based index.
    pub(super) date_column: Option<toml::Value>,
    /// Date format (strftime-style).
    pub(super) date_format: Option<String>,
    /// Narration/description column name or index.
    pub(super) narration_column: Option<toml::Value>,
    /// Payee column name or index.
    pub(super) payee_column: Option<toml::Value>,
    /// Amount column name or index.
    pub(super) amount_column: Option<toml::Value>,
    /// Debit column name or index.
    pub(super) debit_column: Option<toml::Value>,
    /// Credit column name or index.
    pub(super) credit_column: Option<toml::Value>,
    /// Amount locale for number parsing (e.g. `de_DE` so `21,12` reads as
    /// 21.12). Mirrors the `--amount-locale` CLI flag.
    pub(super) amount_locale: Option<String>,
    /// Amount format pattern (`format_num_pattern` style). Mirrors the
    /// `--amount-format` CLI flag.
    pub(super) amount_format: Option<String>,
    /// CSV delimiter character.
    pub(super) delimiter: Option<String>,
    /// Number of rows to skip.
    pub(super) skip_rows: Option<usize>,
    /// Whether the CSV has a header row.
    #[serde(default)]
    pub(super) skip_header: Option<bool>,
    /// Whether to invert amount signs.
    #[serde(default)]
    pub(super) invert_amounts: Option<bool>,
    /// Default expense account for unmatched negative-amount (money out) transactions.
    pub(super) default_expense: Option<String>,
    /// Default income account for unmatched positive-amount (money in) transactions.
    pub(super) default_income: Option<String>,
    /// Account mappings: pattern → account.
    #[serde(default)]
    pub(super) mappings: HashMap<String, String>,
}

/// Apply a CSV column flag that may be a header name or a bare 0-based index.
///
/// CSV column flags are documented as "name or index". A value that parses as a
/// non-negative integer is treated as a positional index (so headerless CSVs
/// import correctly); anything else is a column name. Shared by the CLI-argument
/// and `importers.toml` config paths so both honor numeric columns.
pub(super) fn apply_column(
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
pub(super) fn parse_column_value(value: &toml::Value) -> Option<String> {
    match value {
        toml::Value::String(s) => Some(s.clone()),
        toml::Value::Integer(i) => Some(i.to_string()),
        _ => None,
    }
}

/// Find the importers.toml file, searching in standard locations.
pub(super) fn find_importers_config(
    explicit_path: Option<&Path>,
) -> Result<Option<std::path::PathBuf>> {
    if let Some(path) = explicit_path {
        if path.exists() {
            return Ok(Some(path.to_path_buf()));
        }
        return Err(anyhow!("Importers config not found: {}", path.display()));
    }

    if let Ok(cwd) = std::env::current_dir() {
        let local = cwd.join("importers.toml");
        if local.exists() {
            return Ok(Some(local));
        }
    }

    if let Some(config_dir) = dirs::config_dir() {
        let user_path = config_dir.join("rledger").join("importers.toml");
        if user_path.exists() {
            return Ok(Some(user_path));
        }
    }

    Ok(None)
}

/// Load and parse an importers.toml file.
pub(super) fn load_importers_config(path: &Path) -> Result<ImportersFile> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read importers config: {}", path.display()))?;
    let config: ImportersFile = toml::from_str(&content)
        .with_context(|| format!("Failed to parse importers config: {}", path.display()))?;
    Ok(config)
}

/// Build an `ImporterConfig` from a named importer entry.
pub(super) fn build_config_from_entry(entry: &ImporterEntry) -> Result<ImporterConfig> {
    let mut builder = ImporterConfig::csv();

    if let Some(ref account) = entry.account {
        builder = builder.account(account);
    }
    if let Some(ref currency) = entry.currency {
        builder = builder.currency(currency);
    }
    if let Some(ref val) = entry.date_column
        && let Some(col) = parse_column_value(val)
    {
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
    if let Some(ref val) = entry.narration_column
        && let Some(col) = parse_column_value(val)
    {
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::narration_column_index,
            |b, n| b.narration_column(n),
        );
    }
    if let Some(ref val) = entry.payee_column
        && let Some(col) = parse_column_value(val)
    {
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::payee_column_index,
            |b, n| b.payee_column(n),
        );
    }
    if let Some(ref val) = entry.amount_column
        && let Some(col) = parse_column_value(val)
    {
        builder = apply_column(
            builder,
            &col,
            CsvConfigBuilder::amount_column_index,
            |b, n| b.amount_column(n),
        );
    }
    if let Some(ref val) = entry.debit_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.debit_column(&col);
    }
    if let Some(ref val) = entry.credit_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.credit_column(&col);
    }
    if let Some(ref locale) = entry.amount_locale {
        builder = builder.amount_locale(super::parse_amount_locale(locale)?);
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

    builder.build()
}

/// Check if an importer matches the given filename using its glob pattern.
pub(super) fn importer_matches_filename(entry: &ImporterEntry, filename: &str) -> bool {
    if let Some(pattern) = &entry.filename_pattern {
        glob::Pattern::new(pattern).is_ok_and(|p| p.matches(filename))
    } else {
        false
    }
}

/// Find importers that match the given filename.
pub(super) fn find_matching_importers<'a>(
    config: &'a ImportersFile,
    filename: &str,
) -> Vec<&'a ImporterEntry> {
    config
        .importers
        .iter()
        .filter(|imp| importer_matches_filename(imp, filename))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_importer::config::ImporterType;

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
        let file: ImportersFile = toml::from_str(src).expect("toml parses");

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
}
