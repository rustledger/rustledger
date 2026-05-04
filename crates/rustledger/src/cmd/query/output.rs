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

    for row in &result.rows {
        for (i, value) in row.iter().enumerate() {
            let col_ctx = col_contexts.get(i).unwrap_or(ctx);
            let len = format_value(value, numberify, col_ctx).len();
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
    for row in &result.rows {
        for (i, value) in row.iter().enumerate() {
            if i > 0 {
                write!(writer, "  ")?;
            }
            let col_ctx = col_contexts.get(i).unwrap_or(ctx);
            let formatted = format_value(value, numberify, col_ctx);
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
                        " {{ {}}}",
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
                                " {{ {}}}",
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
