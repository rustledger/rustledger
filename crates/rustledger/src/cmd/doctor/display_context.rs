use anyhow::{Context, Result};
use rustledger_core::{Directive, DisplayContext, Precision};
use rustledger_loader::{LoadResult, Loader};
use std::collections::HashSet;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_display_context<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let label = format!("Display Context for {}", file.display());
    let sources = collect_fixed_sources(&load_result);
    render_display_context(&load_result.display_context, &label, Some(&sources), writer)
}

/// Origin of a fixed-precision override for a currency (issue #1031).
///
/// Used by the doctor renderer to label `(fixed via …)` so users can
/// tell whether a precision override came from the file-level
/// `option "display_precision"`, from per-commodity `precision:` metadata
/// (PR #1032 / issue #991), or both.
#[derive(Debug, Default)]
struct FixedSources {
    /// Currencies that have an entry in `options.display_precision`.
    option: HashSet<String>,
    /// Currencies that have a valid `precision:` metadata declaration on
    /// at least one `commodity` directive. Multi-declaration is last-wins
    /// in the loader; for the doctor label, a currency is "metadata-sourced"
    /// if any valid declaration exists.
    metadata: HashSet<String>,
}

/// Walk a `LoadResult` to compute the source map.
///
/// Note on the `option "display_precision"` source: rledger only parses
/// the colon-encoded form (`"USD:0.01"`). If the option value fails to
/// parse, `options.display_precision` doesn't get the entry — the parser
/// emits an `E7002` warning separately. So checking `display_precision`
/// keys is sufficient; we don't need to look at the raw option strings.
fn collect_fixed_sources(load_result: &LoadResult) -> FixedSources {
    let option: HashSet<String> = load_result
        .options
        .display_precision
        .keys()
        .cloned()
        .collect();

    let metadata: HashSet<String> = load_result
        .directives
        .iter()
        .filter_map(|spanned| {
            let Directive::Commodity(comm) = &spanned.value else {
                return None;
            };
            let value = comm.meta.get("precision")?;
            // Same gate the loader uses: invalid values fall back to
            // inference, so they're not "metadata-sourced" for label
            // purposes.
            rustledger_core::parse_precision_meta(value).ok()?;
            Some(comm.currency.as_str().to_string())
        })
        .collect();

    FixedSources { option, metadata }
}

/// Suffix string for a currency's fixed-precision label, given the
/// source map. Returns the empty string if the currency has no fixed
/// override.
///
/// Pinned strings (issue #1031 AC):
/// - option only: `(fixed via option "display_precision")`
/// - metadata only: `(fixed via commodity metadata)`
/// - both: `(fixed via commodity metadata, overrides option "display_precision")`
/// - programmatic: `(fixed via programmatic source)` — only reachable from
///   test paths that hand-build a `DisplayContext` without a `LoadResult`.
fn fixed_label_suffix(
    currency: &str,
    has_fixed: bool,
    sources: Option<&FixedSources>,
) -> &'static str {
    if !has_fixed {
        return "";
    }
    let Some(srcs) = sources else {
        return " (fixed via programmatic source)";
    };
    let in_meta = srcs.metadata.contains(currency);
    let in_opt = srcs.option.contains(currency);
    match (in_meta, in_opt) {
        (true, true) => " (fixed via commodity metadata, overrides option \"display_precision\")",
        (true, false) => " (fixed via commodity metadata)",
        (false, true) => " (fixed via option \"display_precision\")",
        // The currency has a fixed override but no LoadResult-derived
        // source. That's the programmatic-call path, same as the
        // sources=None case above.
        (false, false) => " (fixed via programmatic source)",
    }
}

/// Render the diagnostic view of a `DisplayContext` to `writer`.
///
/// Split from `cmd_display_context` so the rendering can be unit-tested
/// against a manually-constructed context without going through file I/O.
///
/// `sources` carries the per-currency fixed-precision origin map. Pass
/// `Some(&sources)` from the cmd path (computed via
/// [`collect_fixed_sources`]); pass `None` from tests that hand-build a
/// `DisplayContext` and don't care about source labels — the renderer
/// will fall back to `(fixed via programmatic source)`.
fn render_display_context<W: Write>(
    dctx: &DisplayContext,
    label: &str,
    sources: Option<&FixedSources>,
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
        let suffix = fixed_label_suffix(currency, fixed, sources);
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

    /// Render with no source map — exercises the programmatic-source
    /// fallback. Used by tests that hand-build a `DisplayContext`.
    fn render(dctx: &DisplayContext) -> String {
        let mut buf: Vec<u8> = Vec::new();
        render_display_context(dctx, "Display Context (test)", None, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    /// Render with an explicit source map — exercises the labeled paths.
    fn render_with(dctx: &DisplayContext, sources: &FixedSources) -> String {
        let mut buf: Vec<u8> = Vec::new();
        render_display_context(dctx, "Display Context (test)", Some(sources), &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    fn sources(option: &[&str], metadata: &[&str]) -> FixedSources {
        FixedSources {
            option: option.iter().map(|s| (*s).to_string()).collect(),
            metadata: metadata.iter().map(|s| (*s).to_string()).collect(),
        }
    }

    #[test]
    fn empty_context_reports_no_currencies() {
        let out = render(&DisplayContext::new());
        assert!(out.contains("No currencies observed."));
        // Header still rendered before the early return.
        assert!(out.contains("Display Context (test)"));
        assert!(out.contains("Inference policy: MostCommon"));
        // Stability: no `fixed via …` label when no currencies are
        // observed (issue #1031 AC).
        assert!(!out.contains("fixed via"));
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
        // No fixed override → no `fixed via` label (stability AC #1031).
        assert!(!out.contains("fixed via"));
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
    fn programmatic_fixed_override_falls_back_to_programmatic_label() {
        // Hand-built context with no source map: render() passes None,
        // exercising the programmatic-source fallback.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        let out = render(&ctx);
        assert!(out.contains("effective: 2 dp (fixed via programmatic source)"));
        // Distribution still shown so users can see what the inference
        // would have produced.
        assert!(out.contains("distribution: dp=3: 1"));
    }

    #[test]
    fn fixed_via_option_only() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        let srcs = sources(&["USD"], &[]);
        let out = render_with(&ctx, &srcs);
        assert!(out.contains("effective: 2 dp (fixed via option \"display_precision\")"));
    }

    #[test]
    fn fixed_via_commodity_metadata_only() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        let srcs = sources(&[], &["USD"]);
        let out = render_with(&ctx, &srcs);
        assert!(out.contains("effective: 2 dp (fixed via commodity metadata)"));
    }

    #[test]
    fn fixed_via_both_metadata_overrides_option() {
        // Both option AND commodity metadata set for USD. Per #991/#1032,
        // metadata wins; the doctor label says so explicitly so users
        // can debug precedence at a glance.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 4);
        let srcs = sources(&["USD"], &["USD"]);
        let out = render_with(&ctx, &srcs);
        assert!(out.contains(
            "effective: 4 dp (fixed via commodity metadata, overrides option \"display_precision\")"
        ));
    }

    #[test]
    fn fixed_with_sources_but_currency_not_in_either_falls_back_to_programmatic() {
        // Defensive degradation: if the source map doesn't list a currency
        // that has a fixed override, the most likely explanation is a
        // programmatic `set_fixed_precision` call (i.e. someone built the
        // context outside the loader path). A bug in `collect_fixed_sources`
        // could ALSO produce this state — the renderer's behavior here is
        // to fall back gracefully rather than misattribute. Same label as
        // the None-sources case.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        // Empty source map.
        let srcs = sources(&[], &[]);
        let out = render_with(&ctx, &srcs);
        assert!(out.contains("effective: 2 dp (fixed via programmatic source)"));
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
        let srcs = sources(&["BTC"], &[]);
        let out = render_with(&ctx, &srcs);
        assert!(out.contains("BTC:"));
        assert!(out.contains("effective: 8 dp (fixed via option \"display_precision\")"));
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

    #[test]
    fn fixed_label_suffix_returns_empty_for_unfixed() {
        // Unit-test the helper directly. No fixed override → no suffix
        // regardless of source map state.
        assert_eq!(fixed_label_suffix("USD", false, None), "");
        let srcs = sources(&["USD"], &["USD"]);
        assert_eq!(fixed_label_suffix("USD", false, Some(&srcs)), "");
    }

    /// End-to-end: drive `cmd_display_context` against a real fixture
    /// that uses both `option "display_precision"` AND commodity-metadata
    /// `precision:` declarations. Pins the integration between the
    /// loader's source data and the renderer's labels.
    #[test]
    fn e2e_cmd_display_context_labels_each_source_correctly() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("e2e.beancount");
        std::fs::write(
            &path,
            // GBP via option only.
            // BTC via commodity metadata only.
            // USD via BOTH (metadata wins per #991/#1032).
            r#"option "display_precision" "GBP:0.01"
option "display_precision" "USD:0.001"

2024-01-01 commodity USD
  precision: 4

2024-01-01 commodity BTC
  precision: 8

2024-01-01 open Assets:USD
2024-01-01 open Assets:GBP
2024-01-01 open Assets:BTC
2024-01-01 open Equity:Opening

2024-01-15 * "USD"
  Assets:USD       100.00 USD
  Equity:Opening

2024-01-15 * "GBP"
  Assets:GBP       50.00 GBP
  Equity:Opening

2024-01-15 * "BTC"
  Assets:BTC       0.50000000 BTC
  Equity:Opening
"#,
        )
        .unwrap();

        let mut buf: Vec<u8> = Vec::new();
        cmd_display_context(&path, &mut buf).expect("cmd should succeed");
        let out = String::from_utf8(buf).unwrap();

        // Scope each label assertion to the per-currency block so a bug
        // that produced the right *count* of labels in the wrong sections
        // would still fire (Copilot review on PR #1036).
        assert_eq!(
            currency_section(&out, "GBP").trim_end(),
            "  effective: 2 dp (fixed via option \"display_precision\")\n  \
             distribution: dp=2: 1",
            "GBP block; full output:\n{out}"
        );
        assert_eq!(
            currency_section(&out, "BTC").trim_end(),
            "  effective: 8 dp (fixed via commodity metadata)\n  \
             distribution: dp=8: 1",
            "BTC block; full output:\n{out}"
        );
        // USD has the override case AND a non-trivial mode/max difference
        // (option=3dp, metadata=4dp; observed 2dp). Scope to the section
        // and check the label substring; the mode/max specifics aren't
        // the contract this test is pinning.
        let usd_section = currency_section(&out, "USD");
        assert!(
            usd_section
                .contains("(fixed via commodity metadata, overrides option \"display_precision\")"),
            "USD section should carry the override label; section was:\n{usd_section}"
        );
        assert!(
            !usd_section.contains("(fixed via option \"display_precision\")\n"),
            "USD section must NOT carry the option-only label; section was:\n{usd_section}"
        );

        // None of the labels should be the legacy `(fixed override)` form
        // anywhere in the output.
        assert!(
            !out.contains("(fixed override)"),
            "legacy source-agnostic label should be gone; got:\n{out}"
        );
    }

    /// E2E: invalid `precision:` metadata coexisting with a valid
    /// `option "display_precision"`. The loader applies the option,
    /// skips the invalid metadata (validator emits E5003), and the
    /// effective precision comes from the option. The doctor label
    /// must say "fixed via option", NOT "fixed via commodity metadata"
    /// — pinning that `collect_fixed_sources`'s `parse_precision_meta`
    /// gate matches the loader's gate. Without this test, a future
    /// "simplification" of `collect_fixed_sources` (e.g. dropping the
    /// validity check and treating any `precision` key as
    /// metadata-sourced) would silently mislabel the override.
    #[test]
    fn e2e_invalid_metadata_with_option_labels_as_option() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("e2e_invalid.beancount");
        std::fs::write(
            &path,
            r#"option "display_precision" "USD:0.01"

2024-01-01 commodity USD
  precision: -1

2024-01-01 open Assets:USD
2024-01-01 open Equity:Opening

2024-01-15 * "USD"
  Assets:USD       100.00 USD
  Equity:Opening
"#,
        )
        .unwrap();

        let mut buf: Vec<u8> = Vec::new();
        cmd_display_context(&path, &mut buf).expect("cmd should succeed");
        let out = String::from_utf8(buf).unwrap();

        let usd = currency_section(&out, "USD");
        assert!(
            usd.contains("(fixed via option \"display_precision\")"),
            "USD should be option-sourced (invalid metadata is skipped); section:\n{usd}"
        );
        assert!(
            !usd.contains("commodity metadata"),
            "invalid metadata must NOT be labeled metadata-sourced; section:\n{usd}"
        );
    }

    /// Extract the per-currency block from a doctor output. Returns
    /// everything from the line after `<CCY>:` up to the next blank
    /// line (or end-of-output). Used by `e2e_*` tests to scope label
    /// assertions to the right currency.
    ///
    /// Panics if the currency isn't in the output — silent fallthrough
    /// would let a typo'd test name silently assert against the doctor
    /// header section.
    ///
    /// The header search is anchored to a preceding newline (`\n<CCY>:\n`)
    /// so a mid-line mention of `<CCY>:` (e.g. an inline summary that a
    /// future format change might add) doesn't match.
    fn currency_section<'a>(out: &'a str, currency: &str) -> &'a str {
        let header = format!("\n{currency}:\n");
        let start = out
            .find(&header)
            .unwrap_or_else(|| panic!("currency {currency:?} not found in output:\n{out}"))
            + header.len();
        let rest = &out[start..];
        let end = rest.find("\n\n").unwrap_or(rest.len());
        &rest[..end]
    }
}
