use crate::format::FormatConfig;
use anyhow::{Context, Result};
use rustledger_loader::{LoadError, Loader};
use rustledger_parser::{format_source, parse};
use std::io::Write;
use std::path::{Path, PathBuf};

/// Diagnose whether `rledger format` on a ledger is byte-stable —
/// `format(parse(source)) == source` — across the entry file and every
/// file it transitively `include`s. Uses the loader to resolve the
/// include graph with path-traversal protection, then runs the canonical
/// `format_source` path on each file's source independently.
pub(super) fn cmd_roundtrip<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    writeln!(writer, "Round-trip test for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Step 1: resolve includes. `with_path_security(true)` keeps the
    // include graph confined to the entry file's directory tree —
    // diagnosing an unfamiliar ledger should never reach outside its
    // own tree, even if it contains a malicious `include "/etc/passwd"`.
    writeln!(writer, "Step 1: Resolving include graph...")?;
    let mut loader = Loader::new().with_path_security(true);
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Surface ONLY parse errors as a round-trip blocker. Infrastructure
    // errors (include cycles, unmatched globs, path traversal, IO,
    // decryption) are not format-stability questions; the doctor reports
    // them as advisory and still attempts the per-file round-trip on
    // files that did parse.
    let parse_errors: Vec<&LoadError> = load_result
        .errors
        .iter()
        .filter(|e| matches!(e, LoadError::ParseErrors { .. }))
        .collect();
    let infra_errors: Vec<&LoadError> = load_result
        .errors
        .iter()
        .filter(|e| !matches!(e, LoadError::ParseErrors { .. }))
        .collect();

    if !parse_errors.is_empty() {
        writeln!(
            writer,
            "  Found {} parse error(s) — fix them before diagnosing round-trip:",
            parse_errors.len()
        )?;
        for err in parse_errors.iter().take(10) {
            writeln!(writer, "    {err}")?;
        }
        if parse_errors.len() > 10 {
            writeln!(writer, "    ... and {} more", parse_errors.len() - 10)?;
        }
        anyhow::bail!("round-trip aborted: source has parse errors");
    }

    if !infra_errors.is_empty() {
        writeln!(
            writer,
            "  Note: {} non-parse infrastructure error(s) — proceeding with files that loaded successfully:",
            infra_errors.len()
        )?;
        for err in infra_errors.iter().take(5) {
            writeln!(writer, "    {err}")?;
        }
        if infra_errors.len() > 5 {
            writeln!(writer, "    ... and {} more", infra_errors.len() - 5)?;
        }
    }

    let files = load_result.source_map.files();
    writeln!(
        writer,
        "  Resolved {} file(s) in include graph",
        files.len()
    )?;

    let config = FormatConfig::default();
    let mut all_stable = true;
    let mut total_directives = 0usize;

    // Step 2: per-file canonical round-trip.
    writeln!(writer)?;
    writeln!(writer, "Step 2: Checking byte-stability per file...")?;
    for sf in files {
        // No bespoke BOM strip here — the parser's lexer now skips a
        // leading UTF-8 BOM transparently, so the doctor sees what the
        // CLI sees byte-for-byte.
        let source: &str = &sf.source;
        let parse_result = parse(source);
        if !parse_result.errors.is_empty() {
            writeln!(
                writer,
                "  [{}] {} parse error(s) — skipping",
                relative_path(&sf.path, file),
                parse_result.errors.len()
            )?;
            all_stable = false;
            continue;
        }

        let formatted = format_source(source, &parse_result, &config);
        let stable = formatted == source;

        let reparsed = parse(&formatted);
        let reparsed_count = reparsed.directives.len();
        total_directives += parse_result.directives.len();

        if stable {
            writeln!(
                writer,
                "  [stable]   {} ({} directives)",
                relative_path(&sf.path, file),
                parse_result.directives.len()
            )?;
        } else if reparsed.errors.is_empty() && reparsed_count == parse_result.directives.len() {
            writeln!(
                writer,
                "  [reflow]   {} ({} directives) — bytes change but structure preserved",
                relative_path(&sf.path, file),
                parse_result.directives.len()
            )?;
            all_stable = false;
        } else {
            writeln!(
                writer,
                "  [MISMATCH] {} — original {} directives, re-parse {} directives, {} errors",
                relative_path(&sf.path, file),
                parse_result.directives.len(),
                reparsed_count,
                reparsed.errors.len()
            )?;
            all_stable = false;
        }
    }

    writeln!(writer)?;
    writeln!(writer, "Step 3: Summary")?;
    writeln!(
        writer,
        "  {} file(s), {} directives total",
        files.len(),
        total_directives
    )?;
    if all_stable {
        writeln!(
            writer,
            "  SUCCESS: every file is byte-stable under `rledger format`"
        )?;
    } else {
        writeln!(
            writer,
            "  Some files would be modified by `rledger format` — run `rledger format --diff` on the [reflow] / [MISMATCH] files to inspect"
        )?;
    }

    Ok(())
}

/// Display each include-graph file relative to the entry file's
/// canonical parent when possible. Falls back to the absolute path if
/// the strip fails (e.g., entry parent is outside the loader's
/// canonical-path tree, which can happen on odd symlink layouts).
fn relative_path(file: &Path, entry: &Path) -> String {
    let entry_parent = entry
        .canonicalize()
        .ok()
        .and_then(|c| c.parent().map(Path::to_path_buf));
    if let Some(base) = entry_parent
        && let Ok(rel) = file.strip_prefix(&base)
    {
        return rel.display().to_string();
    }
    file.display().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn write_file(dir: &Path, name: &str, contents: &str) -> PathBuf {
        let p = dir.join(name);
        fs::write(&p, contents).unwrap();
        p
    }

    #[test]
    fn stable_single_file_reports_success() {
        let dir = TempDir::new().unwrap();
        let p = write_file(
            dir.path(),
            "ledger.beancount",
            "2024-01-01 open Assets:Cash\n",
        );
        let mut out = Vec::new();
        cmd_roundtrip(&p, &mut out).unwrap();
        let report = String::from_utf8(out).unwrap();
        assert!(report.contains("[stable]"), "{report}");
        assert!(report.contains("SUCCESS"), "{report}");
    }

    /// BOM at the start of the file must NOT block the round-trip
    /// diagnosis — the parser's lexer skips it transparently.
    #[test]
    fn bom_prefixed_file_does_not_abort() {
        let dir = TempDir::new().unwrap();
        let with_bom = "\u{FEFF}2024-01-01 open Assets:Cash\n";
        let p = write_file(dir.path(), "ledger.beancount", with_bom);
        let mut out = Vec::new();
        cmd_roundtrip(&p, &mut out).expect("BOM should be parsed transparently");
        let report = String::from_utf8(out).unwrap();
        assert!(
            !report.to_lowercase().contains("parse error"),
            "BOM should not produce a parse error: {report}"
        );
    }

    /// A multi-file ledger via `include` is walked and each file
    /// reported individually.
    #[test]
    fn multi_file_include_graph_walked() {
        let dir = TempDir::new().unwrap();
        write_file(
            dir.path(),
            "accounts.beancount",
            "2024-01-01 open Assets:Cash\n",
        );
        let main = write_file(
            dir.path(),
            "main.beancount",
            "include \"accounts.beancount\"\n",
        );
        let mut out = Vec::new();
        cmd_roundtrip(&main, &mut out).unwrap();
        let report = String::from_utf8(out).unwrap();
        assert!(
            report.contains("Resolved 2 file(s)"),
            "expected 2 files in graph: {report}"
        );
        assert!(report.contains("accounts.beancount"), "{report}");
        assert!(report.contains("main.beancount"), "{report}");
    }

    /// A glob that matches nothing is an infrastructure error, not a
    /// parse error, so the doctor continues with the entry file's
    /// per-file round-trip rather than bailing.
    #[test]
    fn glob_no_match_continues_with_advisory() {
        let dir = TempDir::new().unwrap();
        let main = write_file(
            dir.path(),
            "main.beancount",
            "include \"nope/*.beancount\"\n2024-01-01 open Assets:Cash\n",
        );
        let mut out = Vec::new();
        cmd_roundtrip(&main, &mut out).expect("infra errors should not abort");
        let report = String::from_utf8(out).unwrap();
        assert!(
            report.contains("infrastructure error"),
            "should mention infra errors: {report}"
        );
        assert!(report.contains("[stable]"), "{report}");
    }

    /// Parse errors abort the diagnosis.
    #[test]
    fn parse_errors_abort() {
        let dir = TempDir::new().unwrap();
        let p = write_file(
            dir.path(),
            "ledger.beancount",
            "2024-01-01 open\nthis is not a directive\n",
        );
        let mut out = Vec::new();
        let result = cmd_roundtrip(&p, &mut out);
        assert!(result.is_err(), "expected bail on parse errors");
        let report = String::from_utf8(out).unwrap();
        assert!(report.to_lowercase().contains("parse error"), "{report}");
    }
}
