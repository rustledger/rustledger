use crate::format::FormatConfig;
use anyhow::{Context, Result};
use rustledger_parser::{format_source, parse};
use std::fs;
use std::io::Write;
use std::path::PathBuf;

/// Diagnose whether `rledger format` on this file is byte-stable, i.e.
/// `format(parse(source)) == source` after one normalization. Tests the
/// exact path the CLI takes (`format_source`), not the directive-list
/// aggregator — so the result mirrors what the user would see running
/// `rledger format --check` and `rledger format` themselves.
pub(super) fn cmd_roundtrip<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    writeln!(writer, "Round-trip test for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Step 1: read and parse the source directly (no Loader — Loader applies
    // booking + plugins and produces booked Directives without source spans,
    // which the canonical format_source needs).
    writeln!(writer, "Step 1: Loading original file...")?;
    let source =
        fs::read_to_string(file).with_context(|| format!("failed to read {}", file.display()))?;
    let parse_result = parse(&source);
    let original_count = parse_result.directives.len();
    writeln!(writer, "  Parsed {original_count} directives")?;

    // Bail before formatting on parse errors. format_source ignores
    // anything the parser couldn't recognize; running it on a partial parse
    // would silently drop the unparsable directives, and the comparison
    // below would then report SUCCESS for what is actually a lossy
    // round-trip. Surface the error condition to the user instead.
    if !parse_result.errors.is_empty() {
        writeln!(
            writer,
            "  Found {} parse error(s) in original — cannot diagnose round-trip until they are fixed:",
            parse_result.errors.len()
        )?;
        for err in parse_result.errors.iter().take(10) {
            writeln!(writer, "    {err}")?;
        }
        if parse_result.errors.len() > 10 {
            writeln!(
                writer,
                "    ... and {} more",
                parse_result.errors.len() - 10
            )?;
        }
        anyhow::bail!("round-trip aborted: source has parse errors");
    }

    // Step 2: format via the same path the CLI uses.
    writeln!(writer)?;
    writeln!(writer, "Step 2: Formatting source via format_source...")?;
    let config = FormatConfig::default();
    let formatted = format_source(&source, &parse_result, &config);

    let byte_stable = formatted == source;
    writeln!(
        writer,
        "  Byte-stable: {}",
        if byte_stable { "YES" } else { "NO" }
    )?;

    // Step 3: re-parse the formatter's output to catch any output the
    // parser can't read back.
    writeln!(writer)?;
    writeln!(writer, "Step 3: Re-parsing formatted output...")?;
    let result2 = parse(&formatted);

    if !result2.errors.is_empty() {
        writeln!(
            writer,
            "  Found {} parse errors in round-trip",
            result2.errors.len()
        )?;
        for err in &result2.errors {
            writeln!(writer, "    {}", err.message())?;
        }
    }
    let roundtrip_count = result2.directives.len();
    writeln!(writer, "  Parsed {roundtrip_count} directives")?;

    // Step 4: compare.
    writeln!(writer)?;
    writeln!(writer, "Step 4: Comparing results...")?;
    if byte_stable {
        writeln!(
            writer,
            "  SUCCESS: Source is byte-stable under `rledger format`"
        )?;
    } else if original_count == roundtrip_count && result2.errors.is_empty() {
        writeln!(
            writer,
            "  PARTIAL: format produced {original_count} directive(s) → re-parse yielded {roundtrip_count} directive(s); structure preserved but bytes changed (run `rledger format --diff` to inspect)"
        )?;
    } else {
        writeln!(
            writer,
            "  MISMATCH: Original had {original_count} directives, round-trip has {roundtrip_count}"
        )?;
    }

    Ok(())
}
