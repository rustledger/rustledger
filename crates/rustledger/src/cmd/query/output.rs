//! Query result output formatting (text, CSV, JSON, beancount).

use super::ShellSettings;
use anyhow::{Context, Result};
use rustledger_core::{Directive, DisplayContext};
use rustledger_query::{Executor, Value, parse as parse_query};
use std::io::Write;

pub(super) fn execute_query<W: Write>(
    query_str: &str,
    directives: &[Directive],
    settings: &ShellSettings,
    writer: &mut W,
) -> Result<()> {
    // Parse the query
    let query = parse_query(query_str).with_context(|| "failed to parse query")?;

    // Execute
    let mut executor = Executor::new(directives);
    let result = executor
        .execute(&query)
        .with_context(|| "failed to execute query")?;

    // Output results using display context for consistent number formatting
    let ctx = &settings.display_context;
    match settings.format {
        super::OutputFormat::Text => write_text(&result, writer, settings.numberify, ctx)?,
        super::OutputFormat::Csv => write_csv(&result, writer, settings.numberify, ctx)?,
        super::OutputFormat::Json => write_json(&result, writer)?,
        super::OutputFormat::Beancount => write_beancount(&result, writer, ctx)?,
    }

    Ok(())
}

fn write_text<W: Write>(
    result: &rustledger_query::QueryResult,
    writer: &mut W,
    numberify: bool,
    ctx: &DisplayContext,
) -> Result<()> {
    if result.columns.is_empty() {
        return Ok(());
    }

    // Build per-column display contexts by scanning all values. Naked-Decimal
    // columns also inherit the ledger context as a fallback for the issue #954
    // path (a column of `Value::Number(0)` from an aggregate that collapsed
    // to literal zero needs *some* precision source). Inherit ONCE per column
    // — `update_from` now merges histograms by summing counts (PR #986), so
    // calling it per row would inflate the ledger's sample frequencies by N
    // and could shift the column's effective mode. Caught by Copilot review.
    let mut col_contexts: Vec<DisplayContext> = vec![DisplayContext::new(); result.columns.len()];
    let mut col_inherited: Vec<bool> = vec![false; result.columns.len()];
    for row in &result.rows {
        for (i, value) in row.iter().enumerate() {
            if i >= col_contexts.len() {
                continue;
            }
            // First Number value in the column triggers a single inheritance
            // pass, so the column ctx has a precision fallback for the
            // issue #954 zero-pad path.
            if matches!(value, Value::Number(_)) && !col_inherited[i] {
                col_contexts[i].update_from(ctx);
                col_inherited[i] = true;
            }
            update_column_context(&mut col_contexts[i], value, ctx);
        }
    }

    // Calculate column widths using per-column contexts
    let mut widths: Vec<usize> = result
        .columns
        .iter()
        .map(std::string::String::len)
        .collect();

    for (row_idx, row) in result.rows.iter().enumerate() {
        let currency_hint = result
            .row_group_keys
            .get(row_idx)
            .and_then(|k| k.as_ref())
            .and_then(|key_values| {
                key_values.iter().find_map(|v| match v {
                    Value::String(s) if looks_like_currency(s) => Some(s.as_str()),
                    _ => None,
                })
            });
        for (i, value) in row.iter().enumerate() {
            let col_ctx = col_contexts.get(i).unwrap_or(ctx);
            let len = format_value_with_hint(value, numberify, col_ctx, currency_hint).len();
            if i < widths.len() && len > widths[i] {
                widths[i] = len;
            }
        }
    }

    // Determine which columns are numeric (for right-alignment)
    let is_numeric_col: Vec<bool> = (0..result.columns.len())
        .map(|i| {
            result.rows.first().is_some_and(|row| {
                row.get(i)
                    .is_some_and(|v| matches!(v, Value::Integer(_) | Value::Number(_)))
            })
        })
        .collect();

    // Print header (right-align numeric column headers to match Python)
    for (i, col) in result.columns.iter().enumerate() {
        if i > 0 {
            write!(writer, "  ")?;
        }
        if i < is_numeric_col.len() && is_numeric_col[i] {
            write!(writer, "{:>width$}", col, width = widths[i])?;
        } else {
            write!(writer, "{:width$}", col, width = widths[i])?;
        }
    }
    writeln!(writer)?;

    // Print separator
    for (i, width) in widths.iter().enumerate() {
        if i > 0 {
            write!(writer, "  ")?;
        }
        write!(writer, "{}", "-".repeat(*width))?;
    }
    writeln!(writer)?;

    // Print rows using per-column display contexts
    for (row_idx, row) in result.rows.iter().enumerate() {
        // Per-row currency hint recovered from the GROUP BY key (issue #988):
        // when a row was produced by an aggregate over `GROUP BY currency`,
        // the renderer needs the currency to quantize Value::Number cells
        // (e.g. `SUM(number)`) at the right per-currency precision. Without
        // this, a SUM of two `0.00 USD` values keeps `rust_decimal`'s natural
        // wider scale and renders `0.000` instead of `0.00`.
        let currency_hint = result
            .row_group_keys
            .get(row_idx)
            .and_then(|k| k.as_ref())
            .and_then(|key_values| {
                key_values.iter().find_map(|v| match v {
                    Value::String(s) if looks_like_currency(s) => Some(s.as_str()),
                    _ => None,
                })
            });

        for (i, value) in row.iter().enumerate() {
            if i > 0 {
                write!(writer, "  ")?;
            }
            let col_ctx = col_contexts.get(i).unwrap_or(ctx);
            let formatted = format_value_with_hint(value, numberify, col_ctx, currency_hint);
            if i < widths.len() {
                // Right-align numeric columns to match Python beancount
                if i < is_numeric_col.len() && is_numeric_col[i] {
                    write!(writer, "{:>width$}", formatted, width = widths[i])?;
                } else {
                    write!(writer, "{:width$}", formatted, width = widths[i])?;
                }
            } else {
                write!(writer, "{formatted}")?;
            }
        }
        writeln!(writer)?;
    }

    // Print row count
    writeln!(writer)?;
    writeln!(writer, "{} row(s)", result.rows.len())?;
    Ok(())
}

fn write_csv<W: Write>(
    result: &rustledger_query::QueryResult,
    writer: &mut W,
    numberify: bool,
    ctx: &DisplayContext,
) -> Result<()> {
    // Print header
    writeln!(writer, "{}", result.columns.join(","))?;

    // Print rows
    for row in &result.rows {
        let values: Vec<String> = row
            .iter()
            .map(|v| escape_csv(&format_value(v, numberify, ctx)))
            .collect();
        writeln!(writer, "{}", values.join(","))?;
    }
    Ok(())
}

fn write_json<W: Write>(result: &rustledger_query::QueryResult, writer: &mut W) -> Result<()> {
    let rows: Vec<serde_json::Value> = result
        .rows
        .iter()
        .map(|row| {
            let obj: serde_json::Map<String, serde_json::Value> = result
                .columns
                .iter()
                .zip(row.iter())
                .map(|(col, val)| (col.clone(), value_to_json(val)))
                .collect();
            serde_json::Value::Object(obj)
        })
        .collect();

    let output = serde_json::json!({
        "columns": result.columns,
        "rows": rows,
        "row_count": result.rows.len(),
    });

    writeln!(writer, "{}", serde_json::to_string_pretty(&output)?)?;
    Ok(())
}

fn write_beancount<W: Write>(
    result: &rustledger_query::QueryResult,
    writer: &mut W,
    ctx: &DisplayContext,
) -> Result<()> {
    for row in &result.rows {
        for value in row {
            writeln!(writer, "{}", format_value(value, false, ctx))?;
        }
    }
    Ok(())
}

/// Update a per-column display context with the amounts in a value.
fn update_column_context(col_ctx: &mut DisplayContext, value: &Value, ledger_ctx: &DisplayContext) {
    match value {
        Value::Amount(a) => {
            let quantized = ledger_ctx.quantize(a.number, a.currency.as_str());
            col_ctx.update(quantized, a.currency.as_str());
        }
        Value::Position(p) => {
            let quantized = ledger_ctx.quantize(p.units.number, p.units.currency.as_str());
            col_ctx.update(quantized, p.units.currency.as_str());
            if let Some(ref cost) = p.cost {
                let quantized = ledger_ctx.quantize(cost.number, cost.currency.as_str());
                col_ctx.update(quantized, cost.currency.as_str());
            }
        }
        Value::Inventory(inv) => {
            for pos in inv.positions() {
                let quantized = ledger_ctx.quantize(pos.units.number, pos.units.currency.as_str());
                col_ctx.update(quantized, pos.units.currency.as_str());
                if let Some(ref cost) = pos.cost {
                    let quantized = ledger_ctx.quantize(cost.number, cost.currency.as_str());
                    col_ctx.update(quantized, cost.currency.as_str());
                }
            }
        }
        // For naked Decimal columns (e.g. SUM(number), cost_number),
        // observe the column's actual values into the `__default__`
        // bucket. Matches Python `bean-query`'s `DecimalRenderer`, which
        // tracks per-column dp independently of the per-currency dctx.
        // Pre-fix this only inherited from the ledger ctx, which made
        // the column inherit precision from unrelated currencies (e.g.
        // a column of USD `cost_number` values rendered at VBMPX's 3dp
        // precision).
        //
        // The ledger-ctx inheritance happens ONCE per column at the
        // call site (write_text) — see the `col_inherited` guard. Doing
        // it here per-cell would inflate the ledger's histogram by N
        // (number of rows) under the new add-merge semantics of
        // `update_from`.
        Value::Number(n) => {
            col_ctx.update(*n, rustledger_core::DEFAULT_CURRENCY);
        }
        _ => {}
    }
}

/// Heuristic: does a string look like a beancount currency? Used to detect
/// the currency-column entry in a row's GROUP BY key so the renderer can
/// apply per-currency precision to a sibling SUM/AVG cell (issue #988).
///
/// Beancount currencies are 1-24 chars, start with an uppercase letter, and
/// only contain `[A-Z0-9'._-]`. The check is conservative — false negatives
/// just leave the cell at default precision (the pre-fix behavior); false
/// positives would let an unrelated string drive precision lookup, but the
/// `DisplayContext::format` call falls back to default if the "currency"
/// has no recorded precision, so the worst case is a no-op.
fn looks_like_currency(s: &str) -> bool {
    if s.is_empty() || s.len() > 24 {
        return false;
    }
    let mut chars = s.chars();
    let first = chars.next().unwrap();
    if !first.is_ascii_uppercase() {
        return false;
    }
    chars.all(|c| {
        c.is_ascii_uppercase() || c.is_ascii_digit() || matches!(c, '\'' | '.' | '_' | '-')
    })
}

/// Format a value with optional GROUP BY currency hint (issue #988).
///
/// When `currency_hint` is set and the value is a `Value::Number` (typically
/// produced by an aggregate like `SUM(number)` over a `GROUP BY currency`),
/// route through `DisplayContext::format` for per-currency quantization so
/// the rendered scale matches bean-query (e.g. `0.00` not `0.000`). Without
/// the hint, behavior is identical to `format_value`.
///
/// The hint is *only* consulted by the text renderer — JSON / CSV /
/// beancount output paths still use `format_value`, keeping their values
/// lossless (issue #988 acceptance criterion #4).
pub(super) fn format_value_with_hint(
    value: &Value,
    numberify: bool,
    ctx: &DisplayContext,
    currency_hint: Option<&str>,
) -> String {
    if let (Value::Number(n), Some(currency)) = (value, currency_hint) {
        return ctx.format(*n, currency);
    }
    format_value(value, numberify, ctx)
}

pub(super) fn format_value(value: &Value, numberify: bool, ctx: &DisplayContext) -> String {
    match value {
        Value::String(s) => s.clone(),
        // Naked Decimals have no associated currency, so we route through
        // `DisplayContext::format_default` to match bean-query's rendering of
        // unspecified-currency aggregate columns. Previously this called
        // `n.normalize().to_string()`, which stripped trailing zeros and
        // diverged from bean-query for cases like `SUM(0.00)` returning "0"
        // instead of "0.00". See issue #954.
        Value::Number(n) => ctx.format_default(*n),
        Value::Integer(i) => i.to_string(),
        Value::Date(d) => d.to_string(),
        Value::Boolean(b) => b.to_string(),
        Value::Amount(a) => {
            if numberify {
                ctx.format(a.number, a.currency.as_str())
            } else {
                ctx.format_amount(a.number, a.currency.as_str())
            }
        }
        Value::Position(p) => {
            if numberify {
                ctx.format(p.units.number, p.units.currency.as_str())
            } else {
                let mut s = ctx.format_amount(p.units.number, p.units.currency.as_str());
                if let Some(ref cost) = p.cost {
                    s.push_str(&format!(
                        " {{{}}}",
                        ctx.format_amount(cost.number, cost.currency.as_str())
                    ));
                }
                s
            }
        }
        Value::Inventory(inv) => {
            use rustledger_core::Position;
            use std::collections::HashMap;

            let mut aggregated: HashMap<(String, Option<String>), Position> = HashMap::new();
            for pos in inv.positions().iter().filter(|p| !p.is_empty()) {
                let cost_key = pos.cost.as_ref().map(|c| {
                    format!(
                        "{}|{}|{:?}|{:?}",
                        c.number.normalize(),
                        c.currency,
                        c.date,
                        c.label
                    )
                });
                let key = (pos.units.currency.to_string(), cost_key);

                aggregated
                    .entry(key)
                    .and_modify(|existing| {
                        existing.units.number += pos.units.number;
                    })
                    .or_insert_with(|| pos.clone());
            }

            let mut sorted_positions: Vec<_> = aggregated.values().collect();
            sorted_positions.sort_by(|a, b| {
                if a.units.currency != b.units.currency {
                    return a.units.currency.cmp(&b.units.currency);
                }
                let qty_cmp = b.units.number.cmp(&a.units.number);
                if qty_cmp != std::cmp::Ordering::Equal {
                    return qty_cmp;
                }
                match (&a.cost, &b.cost) {
                    (Some(ca), Some(cb)) => {
                        if ca.currency != cb.currency {
                            return ca.currency.cmp(&cb.currency);
                        }
                        if ca.number != cb.number {
                            return cb.number.cmp(&ca.number);
                        }
                        ca.date.cmp(&cb.date)
                    }
                    (Some(_), None) => std::cmp::Ordering::Greater,
                    (None, Some(_)) => std::cmp::Ordering::Less,
                    (None, None) => std::cmp::Ordering::Equal,
                }
            });

            let positions: Vec<String> = sorted_positions
                .iter()
                .filter(|p| !p.is_empty())
                .map(|p| {
                    if numberify {
                        ctx.format(p.units.number, p.units.currency.as_str())
                    } else {
                        let mut s = ctx.format_amount(p.units.number, p.units.currency.as_str());
                        if let Some(ref cost) = p.cost {
                            s.push_str(&format!(
                                " {{{}}}",
                                ctx.format_amount(cost.number, cost.currency.as_str())
                            ));
                        }
                        s
                    }
                })
                .collect();
            positions.join("   ")
        }
        Value::StringSet(set) => set.join(", "),
        Value::Set(values) => {
            let strs: Vec<String> = values
                .iter()
                .map(|v| format_value(v, numberify, ctx))
                .collect();
            format!("({})", strs.join(", "))
        }
        Value::Metadata(meta) => meta
            .iter()
            .map(|(k, v)| format!("{k}: {v:?}"))
            .collect::<Vec<_>>()
            .join(", "),
        Value::Interval(interval) => {
            let unit_str = match interval.unit {
                rustledger_query::IntervalUnit::Day => "day",
                rustledger_query::IntervalUnit::Week => "week",
                rustledger_query::IntervalUnit::Month => "month",
                rustledger_query::IntervalUnit::Quarter => "quarter",
                rustledger_query::IntervalUnit::Year => "year",
            };
            let plural = if interval.count.abs() == 1 { "" } else { "s" };
            format!("{} {}{}", interval.count, unit_str, plural)
        }
        Value::Object(obj) => {
            let pairs: Vec<String> = obj
                .iter()
                .map(|(k, v)| format!("{k}: {}", format_value(v, numberify, ctx)))
                .collect();
            format!("{{{}}}", pairs.join(", "))
        }
        Value::Null => String::new(),
    }
}

fn value_to_json(value: &Value) -> serde_json::Value {
    match value {
        Value::String(s) => serde_json::Value::String(s.clone()),
        Value::Number(n) => serde_json::json!(n.to_string()),
        Value::Integer(i) => serde_json::json!(i),
        Value::Date(d) => serde_json::Value::String(d.to_string()),
        Value::Boolean(b) => serde_json::Value::Bool(*b),
        Value::Amount(a) => serde_json::json!({
            "number": a.number.to_string(),
            "currency": a.currency,
        }),
        Value::Position(p) => serde_json::json!({
            "units": {
                "number": p.units.number.to_string(),
                "currency": p.units.currency,
            },
            "cost": p.cost.as_ref().map(|c| serde_json::json!({
                "number": c.number.to_string(),
                "currency": c.currency,
            })),
        }),
        Value::Inventory(inv) => serde_json::json!({
            "positions": inv.positions().iter().map(|p| serde_json::json!({
                "number": p.units.number.to_string(),
                "currency": p.units.currency,
            })).collect::<Vec<_>>(),
        }),
        Value::StringSet(set) => serde_json::json!(set),
        Value::Set(values) => {
            let arr: Vec<serde_json::Value> = values.iter().map(value_to_json).collect();
            serde_json::Value::Array(arr)
        }
        Value::Metadata(meta) => {
            let obj: serde_json::Map<String, serde_json::Value> = meta
                .iter()
                .map(|(k, v)| (k.clone(), serde_json::json!(format!("{v:?}"))))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::Interval(interval) => serde_json::json!({
            "count": interval.count,
            "unit": match interval.unit {
                rustledger_query::IntervalUnit::Day => "day",
                rustledger_query::IntervalUnit::Week => "week",
                rustledger_query::IntervalUnit::Month => "month",
                rustledger_query::IntervalUnit::Quarter => "quarter",
                rustledger_query::IntervalUnit::Year => "year",
            },
        }),
        Value::Object(obj) => {
            let mut map = serde_json::Map::new();
            for (k, v) in obj.as_ref() {
                map.insert(k.clone(), value_to_json(v));
            }
            serde_json::Value::Object(map)
        }
        Value::Null => serde_json::Value::Null,
    }
}

fn escape_csv(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Cost, Inventory, Position};

    /// Issue #987: cost-spec braces in BQL output had a leading space
    /// inside the open brace (`{ 128.99 USD}` instead of `{128.99 USD}`),
    /// diverging from `bean-query`. Pin both the `Position` and
    /// `Inventory` paths so a future change to the format string can't
    /// silently regress.
    #[test]
    fn test_position_with_cost_renders_without_leading_space_inside_braces() {
        let pos = Position::with_cost(
            Amount::new(dec!(8.373), "RGAGX"),
            Cost::new(dec!(128.99), "USD"),
        );
        let value = Value::Position(Box::new(pos));
        let ctx = DisplayContext::new();
        let rendered = format_value(&value, false, &ctx);

        assert!(
            !rendered.contains("{ "),
            "expected no leading space after `{{`, got {rendered:?}"
        );
        assert!(
            rendered.contains("{128.99 USD}"),
            "expected `{{128.99 USD}}` in output, got {rendered:?}"
        );
    }

    #[test]
    fn test_inventory_with_cost_renders_without_leading_space_inside_braces() {
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(8.373), "RGAGX"),
            Cost::new(dec!(128.99), "USD"),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(8.199), "RGAGX"),
            Cost::new(dec!(131.73), "USD"),
        ));
        let value = Value::Inventory(Box::new(inv));
        let ctx = DisplayContext::new();
        let rendered = format_value(&value, false, &ctx);

        assert!(
            !rendered.contains("{ "),
            "expected no leading space after `{{`, got {rendered:?}"
        );
        assert!(
            rendered.contains("{128.99 USD}") && rendered.contains("{131.73 USD}"),
            "expected both costs rendered without leading space, got {rendered:?}"
        );
    }

    // ─── Issue #988 ──────────────────────────────────────────────────────
    // SUM-aggregate text output should match bean-query's per-currency
    // precision. With `SELECT currency, SUM(number) GROUP BY currency`, the
    // SUM cell receives the GROUP BY currency from the row sidecar and
    // quantizes via DisplayContext, so `0.00 USD` inputs sum to `0.00`
    // rather than rust_decimal's natural `0.000`. JSON / CSV / beancount
    // paths still go through `format_value` (no hint), preserving the
    // unquantized value (AC #4: lossless non-text output).

    /// Heuristic detection of currency-shaped strings (used by the text
    /// renderer to find the GROUP BY currency in a row's sidecar).
    #[test]
    fn test_looks_like_currency_accepts_typical_currencies() {
        assert!(looks_like_currency("USD"));
        assert!(looks_like_currency("EUR"));
        assert!(looks_like_currency("BTC"));
        assert!(looks_like_currency("V0AAA"));
        assert!(looks_like_currency("X.Y"));
        assert!(looks_like_currency("ABC-123"));
    }

    #[test]
    fn test_looks_like_currency_rejects_non_currencies() {
        assert!(!looks_like_currency(""));
        assert!(!looks_like_currency("usd")); // lowercase first
        assert!(!looks_like_currency("123")); // starts with digit
        assert!(!looks_like_currency("hello world")); // space
        assert!(!looks_like_currency(&"A".repeat(25))); // too long
    }

    /// Pinning the format dispatch: a `Value::Number` cell rendered with
    /// a currency hint goes through `DisplayContext::format(n, currency)`,
    /// not `format_default(n)`. Without the hint, behavior is unchanged
    /// from `format_value`.
    #[test]
    fn test_format_value_with_hint_routes_number_through_per_currency_ctx() {
        let mut ctx = DisplayContext::new();
        // Seed USD precision at 2dp by observing typical USD amounts.
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");
        ctx.update(dec!(3.00), "USD");

        // A SUM-of-USD-zeros that came out at scale 3 from rust_decimal:
        let sum_value = Value::Number(dec!(0.000));

        let with_hint = format_value_with_hint(&sum_value, false, &ctx, Some("USD"));
        let without_hint = format_value_with_hint(&sum_value, false, &ctx, None);

        // With the hint, USD's per-currency precision (2dp) wins.
        assert_eq!(
            with_hint, "0.00",
            "expected 2dp via USD ctx, got {with_hint:?}"
        );
        // Without the hint, we fall back to format_value's default (preserves
        // the natural 3dp scale from rust_decimal).
        assert_eq!(
            without_hint, "0.000",
            "expected default-format to keep rust_decimal natural scale, got {without_hint:?}"
        );
    }

    /// Negative path: a non-currency hint string is filtered out by the
    /// `looks_like_currency` check at the call site, so `format_value_with_hint`
    /// never sees it. Pin that the helper itself still does the right thing
    /// when handed a non-currency-shaped string (falls through to ctx,
    /// which has no entry, so returns default precision).
    #[test]
    fn test_format_value_with_hint_unknown_currency_falls_back_safely() {
        let ctx = DisplayContext::new();
        let v = Value::Number(dec!(1.5));
        // "MADEUP" passes looks_like_currency but ctx has no entry — safe.
        let rendered = format_value_with_hint(&v, false, &ctx, Some("MADEUP"));
        // Just assert it's a string representation of 1.5 (default scale).
        assert!(
            rendered.contains("1.5"),
            "expected 1.5 in output, got {rendered:?}"
        );
    }
}
