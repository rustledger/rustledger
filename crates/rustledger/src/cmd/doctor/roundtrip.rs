use crate::format::FormatConfig;
use anyhow::{Context, Result};
use rustledger_loader::Loader;
use rustledger_parser::{format_source, parse};
use std::io::Write;
use std::path::{Path, PathBuf};

/// Diagnose whether `rledger format` on a ledger is byte-stable —
/// `format(parse(source)) == source` — across the entry file and every
/// file it transitively `include`s. Uses the loader to resolve the
/// include graph, then runs the canonical `format_source` path on each
/// file's source independently (the same path the CLI takes).
pub(super) fn cmd_roundtrip<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    writeln!(writer, "Round-trip test for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Resolve the include graph via the loader. The loader's parse errors
    // are surfaced up front; we do NOT format a file whose parse failed,
    // because format_source would silently drop the unparsable content
    // and a count-equality check would then report SUCCESS for what is
    // actually a lossy round-trip.
    writeln!(writer, "Step 1: Resolving include graph...")?;
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    if !load_result.errors.is_empty() {
        writeln!(
            writer,
            "  Found {} parse error(s) — fix them before diagnosing round-trip:",
            load_result.errors.len()
        )?;
        for err in load_result.errors.iter().take(10) {
            writeln!(writer, "    {err}")?;
        }
        if load_result.errors.len() > 10 {
            writeln!(writer, "    ... and {} more", load_result.errors.len() - 10)?;
        }
        anyhow::bail!("round-trip aborted: source has parse errors");
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
        let source = strip_utf8_bom(&sf.source);
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

        // Re-parse to verify structure round-trips even when bytes differ.
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

/// Strip a leading UTF-8 BOM (`\u{FEFF}` = `EF BB BF`) if present.
fn strip_utf8_bom(s: &str) -> &str {
    s.strip_prefix('\u{FEFF}').unwrap_or(s)
}

/// Display the absolute file path relative to the entry file's parent
/// when possible, so output stays readable for multi-file ledgers.
fn relative_path(file: &Path, entry: &Path) -> String {
    if let Some(base) = entry.parent()
        && let Ok(rel) = file.strip_prefix(base)
    {
        return rel.display().to_string();
    }
    file.display().to_string()
}
