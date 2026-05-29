use crate::format::{FormatConfig, format_directive};
use anyhow::{Context, Result};
use rustledger_loader::Loader;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_roundtrip<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    writeln!(writer, "Round-trip test for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // First pass: load and parse
    writeln!(writer, "Step 1: Loading original file...")?;
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    if !load_result.errors.is_empty() {
        writeln!(
            writer,
            "  Found {} parse errors in original",
            load_result.errors.len()
        )?;
    }

    let original_count = load_result.directives.len();
    writeln!(writer, "  Parsed {original_count} directives")?;

    // Format back to string
    writeln!(writer)?;
    writeln!(writer, "Step 2: Formatting directives...")?;
    let config = FormatConfig::default();
    let mut formatted = String::new();
    for spanned in &load_result.directives {
        formatted.push_str(&format_directive(&spanned.value, &config));
    }

    // Second pass: parse the formatted output
    writeln!(writer)?;
    writeln!(writer, "Step 3: Re-parsing formatted output...")?;
    let result2 = rustledger_parser::parse(&formatted);

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

    // Compare counts
    writeln!(writer)?;
    writeln!(writer, "Step 4: Comparing results...")?;
    if original_count == roundtrip_count && result2.errors.is_empty() {
        writeln!(
            writer,
            "  SUCCESS: Round-trip produced same number of directives"
        )?;
    } else {
        writeln!(
            writer,
            "  MISMATCH: Original had {original_count} directives, round-trip has {roundtrip_count}"
        )?;
    }

    Ok(())
}
