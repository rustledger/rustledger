use anyhow::{Context, Result};
use rustledger_core::{DisplayContext, Precision};
use rustledger_loader::Loader;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_display_context<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let label = format!("Display Context for {}", file.display());
    render_display_context(&load_result.display_context, &label, writer)
}

/// Render the diagnostic view of a `DisplayContext` to `writer`.
///
/// Split from `cmd_display_context` so the rendering can be unit-tested
/// against a manually-constructed context without going through file
/// I/O.
fn render_display_context<W: Write>(
    dctx: &DisplayContext,
    label: &str,
    writer: &mut W,
) -> Result<()> {
    writeln!(writer, "{label}")?;
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
        // The override could come from `option "display_precision"` OR from
        // a programmatic `set_fixed_precision` call. The "fixed" label is
        // source-agnostic on purpose.
        let suffix = if fixed { " (fixed override)" } else { "" };
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

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    fn render(dctx: &DisplayContext) -> String {
        let mut buf: Vec<u8> = Vec::new();
        render_display_context(dctx, "Display Context (test)", &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn empty_context_reports_no_currencies() {
        let out = render(&DisplayContext::new());
        assert!(out.contains("No currencies observed."));
        // Header still rendered before the early return.
        assert!(out.contains("Display Context (test)"));
        assert!(out.contains("Inference policy: MostCommon"));
    }

    #[test]
    fn single_currency_shows_effective_and_distribution() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD");
        }
        let out = render(&ctx);
        assert!(out.contains("USD:"));
        // Mode == 2dp, all samples agree.
        assert!(out.contains("effective: 2 dp"));
        assert!(out.contains("distribution: dp=2: 5"));
        // Mode and max are equal here, so the side-by-side block must NOT fire.
        assert!(!out.contains("mode (MostCommon)"));
        assert!(!out.contains("max (Maximum)"));
    }

    #[test]
    fn mode_and_max_shown_when_they_differ() {
        // 5×2dp + 1×4dp → mode=2, max=4 → side-by-side block fires.
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD");
        }
        ctx.update(dec!(1.2345), "USD");
        let out = render(&ctx);
        assert!(out.contains("mode (MostCommon): 2"));
        assert!(out.contains("max (Maximum):     4"));
    }

    #[test]
    fn fixed_override_is_labeled() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        let out = render(&ctx);
        // The override could come from option "display_precision" OR from
        // set_fixed_precision; the label is source-agnostic.
        assert!(out.contains("effective: 2 dp (fixed override)"));
        // Distribution still shown so users can see what the inference
        // would have produced.
        assert!(out.contains("distribution: dp=3: 1"));
    }

    #[test]
    fn render_commas_flag_surfaced() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.set_render_commas(true);
        let out = render(&ctx);
        assert!(out.contains("Render commas: enabled"));
    }

    #[test]
    fn render_commas_off_does_not_emit_line() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        let out = render(&ctx);
        assert!(!out.contains("Render commas:"));
    }

    #[test]
    fn fixed_only_currency_appears_with_no_distribution() {
        // A currency declared via `option "display_precision"` but never
        // observed in any posting still shows in the listing — the
        // currencies() iterator includes fixed-only entries.
        let mut ctx = DisplayContext::new();
        ctx.set_fixed_precision("BTC", 8);
        let out = render(&ctx);
        assert!(out.contains("BTC:"));
        assert!(out.contains("effective: 8 dp (fixed override)"));
        // No distribution: line because no observations exist.
        let btc_section = out.split("BTC:").nth(1).unwrap_or("");
        assert!(!btc_section.contains("distribution:"));
    }

    #[test]
    fn currencies_listed_in_sorted_order() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.update(dec!(1.5), "EUR");
        ctx.update(dec!(0.001), "BTC");
        let out = render(&ctx);
        let usd_pos = out.find("USD:").expect("USD shown");
        let eur_pos = out.find("EUR:").expect("EUR shown");
        let btc_pos = out.find("BTC:").expect("BTC shown");
        assert!(btc_pos < eur_pos && eur_pos < usd_pos);
    }
}
