use anyhow::{Context, Result};
use rustledger_core::Precision;
use rustledger_loader::Loader;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_display_context<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let dctx = &load_result.display_context;

    writeln!(writer, "Display Context for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;
    writeln!(
        writer,
        "Inference policy: {:?} (default; matches Python bean-query)",
        dctx.precision()
    )?;
    if dctx.render_commas() {
        writeln!(writer, "Render commas: enabled")?;
    }
    writeln!(writer)?;

    let currencies: Vec<&str> = dctx.currencies().collect();
    if currencies.is_empty() {
        writeln!(writer, "No currencies observed.")?;
        return Ok(());
    }

    for currency in currencies {
        let mode = dctx.precision_under(currency, Precision::MostCommon);
        let max = dctx.precision_under(currency, Precision::Maximum);
        let fixed = dctx.has_fixed_precision(currency);

        writeln!(writer, "{currency}:")?;

        // Effective dp under the active policy. Surfacing this first lines
        // up with what BQL output will actually use.
        let effective = dctx.get_precision(currency);
        let effective_str = effective.map_or_else(|| "<none>".to_string(), |dp| dp.to_string());
        let suffix = if fixed {
            " (FIXED via option \"display_precision\")"
        } else {
            ""
        };
        writeln!(writer, "  effective: {effective_str} dp{suffix}")?;

        // Distribution view — useful for understanding why mode != max.
        let hist = dctx.histogram(currency);
        if !hist.is_empty() {
            let parts: Vec<String> = hist
                .iter()
                .map(|(dp, count)| format!("dp={dp}: {count}"))
                .collect();
            writeln!(writer, "  distribution: {}", parts.join(", "))?;
        }

        // Both policies, for comparison. Helps users understand the
        // MostCommon-vs-Maximum trade-off when diagnosing a divergence.
        if let (Some(m), Some(x)) = (mode, max)
            && m != x
        {
            writeln!(writer, "  mode (MostCommon): {m}")?;
            writeln!(writer, "  max (Maximum):     {x}")?;
        }

        writeln!(writer)?;
    }

    Ok(())
}
