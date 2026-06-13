use anyhow::{Context, Result};
use rustledger_loader::{LoadError, Loader};
use rustledger_parser::format::format_source_with_parsed;
use rustledger_parser::parse;
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

    // Abort on EVERY load error except GlobNoMatch. The doctor's
    // contract is "predict what `rledger format` would do on every file
    // in the ledger"; that's only meaningful if we actually read every
    // file. Unread files (Io, PathTraversal, Decryption, IncludeCycle,
    // GlobError) silently hide format-instability bugs from the
    // diagnosis. Only GlobNoMatch is genuinely advisory — an
    // intentionally-empty glob (e.g., `include "2025/*.bean"` when 2025
    // hasn't started yet) is a common ledger pattern.
    let blocking: Vec<&LoadError> = load_result
        .errors
        .iter()
        .filter(|e| !matches!(e, LoadError::GlobNoMatch { .. }))
        .collect();
    let advisory: Vec<&LoadError> = load_result
        .errors
        .iter()
        .filter(|e| matches!(e, LoadError::GlobNoMatch { .. }))
        .collect();

    if !blocking.is_empty() {
        writeln!(
            writer,
            "  Found {} error(s) preventing complete diagnosis — fix them first:",
            blocking.len()
        )?;
        for err in blocking.iter().take(10) {
            writeln!(writer, "    {err}")?;
        }
        if blocking.len() > 10 {
            writeln!(writer, "    ... and {} more", blocking.len() - 10)?;
        }
        // Behavior-change hint: include cycles previously surfaced as
        // advisory; they now block diagnosis because a cycle means the
        // loader stopped partway through resolving the graph and the
        // doctor cannot give a complete verdict.
        if blocking
            .iter()
            .any(|e| matches!(e, LoadError::IncludeCycle { .. }))
        {
            writeln!(
                writer,
                "  Note: include cycles now block the doctor (previously advisory). Break the cycle to enable diagnosis."
            )?;
        }
        anyhow::bail!(
            "round-trip aborted: {} blocking load error(s); diagnosis on a partially-read ledger would be unreliable",
            blocking.len()
        );
    }

    if !advisory.is_empty() {
        writeln!(
            writer,
            "  Note: {} empty-glob include(s) — these are valid ledger patterns and the diagnosis proceeds:",
            advisory.len()
        )?;
        for err in advisory.iter().take(5) {
            writeln!(writer, "    {err}")?;
        }
        if advisory.len() > 5 {
            writeln!(writer, "    ... and {} more", advisory.len() - 5)?;
        }
    }

    let files = load_result.source_map.files();
    writeln!(
        writer,
        "  Resolved {} file(s) in include graph",
        files.len()
    )?;

    // Precompute the canonical parent of the entry file once; the per-
    // file loop calls `relative_path` N times and recomputing
    // canonicalize() on every call is O(N) syscalls.
    let entry_parent: Option<PathBuf> = file
        .canonicalize()
        .ok()
        .and_then(|c| c.parent().map(Path::to_path_buf));
    let entry_parent = entry_parent.as_deref();

    let mut all_stable = true;
    let mut total_directives = 0usize;

    // Step 2: per-file canonical round-trip.
    writeln!(writer)?;
    writeln!(writer, "Step 2: Checking byte-stability per file...")?;
    for sf in files {
        // No bespoke BOM strip here — `rustledger_parser::parse`
        // strips a strict-byte-0 BOM via `crate::bom::strip_leading`
        // at its public entry and records the outcome in
        // `ParseResult::has_leading_bom`; `format_source` re-prepends
        // it on output. The doctor sees what the CLI sees byte-for-
        // byte and the BOM-preservation contract lives in one place.
        let source: &str = &sf.source;
        let parse_result = parse(source);
        if !parse_result.errors.is_empty() {
            writeln!(
                writer,
                "  [{}] {} parse error(s) — skipping",
                relative_path(&sf.path, entry_parent),
                parse_result.errors.len()
            )?;
            all_stable = false;
            continue;
        }

        // Reuse `parse_result` from the error gate above. Saves a
        // full re-parse + `compute_alignment` walk per file — on
        // a project of 200 included files the doctor pass roughly
        // halves its parsing cost. Byte-identical output pinned
        // by `format_source_with_parsed_matches_format_source`.
        let formatted = format_source_with_parsed(&parse_result, source);
        let stable = formatted == source;

        let reparsed = parse(&formatted);
        let reparsed_count = reparsed.directives.len();
        total_directives += parse_result.directives.len();

        if stable {
            writeln!(
                writer,
                "  [stable]   {} ({} directives)",
                relative_path(&sf.path, entry_parent),
                parse_result.directives.len()
            )?;
        } else if reparsed.errors.is_empty() && reparsed_count == parse_result.directives.len() {
            writeln!(
                writer,
                "  [reflow]   {} ({} directives) — bytes change but structure preserved",
                relative_path(&sf.path, entry_parent),
                parse_result.directives.len()
            )?;
            all_stable = false;
        } else {
            writeln!(
                writer,
                "  [MISMATCH] {} — original {} directives, re-parse {} directives, {} errors",
                relative_path(&sf.path, entry_parent),
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

/// Display each include-graph file relative to a precomputed canonical
/// parent. Falls back to the absolute path when no parent is supplied or
/// when the strip fails (e.g., the file is outside the canonical tree —
/// possible with odd symlink layouts).
fn relative_path(file: &Path, entry_parent: Option<&Path>) -> String {
    if let Some(base) = entry_parent
        && let Ok(rel) = file.strip_prefix(base)
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

    /// BOM at the start of the file parses transparently but does NOT
    /// round-trip byte-stable: the canonical form drops the leading
    /// BOM (see PR-4 decision comment on #1262 and
    /// `rustledger_parser::format`'s rustdoc). The doctor reports
    /// `[reflow]` — same directive structure, different bytes — and
    /// the user can run `rledger format -i` to strip the BOM.
    #[test]
    fn bom_prefixed_file_reflows_on_format() {
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
        assert!(
            report.contains("[reflow]"),
            "BOM-prefixed file should reflow (canonical form drops the BOM); got: {report}"
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

    /// A glob that matches nothing is intentional in many real ledgers
    /// (e.g., `include "2025/*.bean"` ahead of the new year). The doctor
    /// reports an advisory note and continues the per-file round-trip.
    /// All OTHER load errors abort.
    #[test]
    fn glob_no_match_continues_with_advisory() {
        let dir = TempDir::new().unwrap();
        // Two-directive file with a blank line between the include and
        // the open. Since #1325 the formatter preserves the author's
        // blank lines verbatim (grouped or separated both round-trip
        // stably); this fixture keeps the blank purely for readability.
        let main = write_file(
            dir.path(),
            "main.beancount",
            "include \"nope/*.beancount\"\n\n2024-01-01 open Assets:Cash\n",
        );
        let mut out = Vec::new();
        cmd_roundtrip(&main, &mut out).expect("GlobNoMatch should not abort");
        let report = String::from_utf8(out).unwrap();
        assert!(
            report.contains("empty-glob include"),
            "should describe empty-glob advisory: {report}"
        );
        assert!(report.contains("[stable]"), "{report}");
    }

    /// Unread-include errors (IO permission, path traversal,
    /// decryption) abort: the doctor cannot give a reliable verdict on
    /// a partially-read ledger.
    #[test]
    fn path_traversal_blocks_diagnosis() {
        let dir = TempDir::new().unwrap();
        // `include` outside the entry's directory triggers the
        // path-traversal check (which path-security catches).
        let main = write_file(
            dir.path(),
            "main.beancount",
            "include \"/etc/this-cannot-be-read-by-doctor.bean\"\n2024-01-01 open Assets:Cash\n",
        );
        let mut out = Vec::new();
        let result = cmd_roundtrip(&main, &mut out);
        assert!(result.is_err(), "path traversal should abort: {result:?}");
        let report = String::from_utf8(out).unwrap();
        assert!(report.contains("preventing complete diagnosis"), "{report}");
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
