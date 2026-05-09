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

    // Resolve per-row currency hints once. The hint feeds both the
    // width-calculation pass and the print pass; computing per-pass
    // would duplicate the lookup.
    //
    // Lifetime: the `&str` entries borrow from `result.row_group_keys`.
    // Safe because `result` is `&`-borrowed for the rest of this
    // function — any future refactor that mutates `result` mid-stream
    // would break this and the borrow checker would point at the cache.
    //
    // Short-circuit: when no row has a GROUP BY key (the common case for
    // non-aggregate queries), every hint would be `None` — skip the
    // allocation entirely. Access via `currency_hints.get(i).copied().flatten()`
    // tolerates the empty Vec.
    let currency_hints: Vec<Option<&str>> = if result.has_aggregate_rows() {
        (0..result.rows.len())
            .map(|i| currency_hint_for_row(result, i, ctx))
            .collect()
    } else {
        Vec::new()
    };

    // Resolve per-column currency hints from column names (issue #1023).
    //
    // PIVOT BY currency reshapes rows: the GROUP BY currency moves into
    // column position, and each pivoted column's *name* is a currency
    // code (e.g. "USD", "JPY"). The pivot path uses `add_row` (not
    // `add_aggregate_row`), so the per-row sidecar is `None` for those
    // rows — we'd lose the precision context if we relied on
    // `currency_hints` alone.
    //
    // Same false-positive guard as `currency_hint_for_row`: the column
    // name must both look like a currency AND have tracked precision.
    // The precision check is what stops a literal column named "USD"
    // (when no USD has been observed) from routing through
    // `DisplayContext::format`'s normalize path and stripping zeros.
    let column_currency_hints: Vec<Option<&str>> = result
        .columns
        .iter()
        .map(|col| {
            if looks_like_currency(col) && ctx.get_precision(col).is_some() {
                Some(col.as_str())
            } else {
                None
            }
        })
        .collect();

    // Calculate column widths using per-column contexts
    let mut widths: Vec<usize> = result
        .columns
        .iter()
        .map(std::string::String::len)
        .collect();

    for (row_idx, row) in result.rows.iter().enumerate() {
        for (i, value) in row.iter().enumerate() {
            let col_ctx = col_contexts.get(i).unwrap_or(ctx);
            let cell_hint = resolve_cell_hint(&currency_hints, &column_currency_hints, row_idx, i);
            let len = format_value_with_hint(value, numberify, col_ctx, cell_hint).len();
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
        for (i, value) in row.iter().enumerate() {
            if i > 0 {
                write!(writer, "  ")?;
            }
            let col_ctx = col_contexts.get(i).unwrap_or(ctx);
            let cell_hint = resolve_cell_hint(&currency_hints, &column_currency_hints, row_idx, i);
            let formatted = format_value_with_hint(value, numberify, col_ctx, cell_hint);
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

/// Heuristic: does a string look like a beancount currency? Used as a
/// pre-filter when scanning a row's GROUP BY key for a candidate currency
/// to drive per-cell precision lookup (issue #988). Beancount currencies
/// are 2-24 chars (the spec allows shorter, but every real-world ticker
/// is at least 2 — the lower bound is a defensive narrowing of the
/// heuristic since single uppercase letters mostly aren't currencies),
/// start with an uppercase letter, and only contain `[A-Z0-9'._-]`.
///
/// This is only step one of two. The caller (`currency_hint_for_row`) ALSO
/// checks that the candidate has tracked precision in the `DisplayContext`
/// before returning it — without that gate, a false-positive (unrelated
/// uppercase string in the key) would route a `Value::Number` through
/// `DisplayContext::format`, whose unknown-currency fallback calls
/// `normalize()` and *strips* trailing zeros (`0.000` → `0`), making
/// output worse than the pre-fix state.
fn looks_like_currency(s: &str) -> bool {
    if s.len() < 2 || s.len() > 24 {
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

/// Find the per-row currency hint for issue #988 quantization.
///
/// Scans the row's GROUP BY key (from `QueryResult::group_key`) for the
/// first string that both *looks* like a currency AND has tracked precision
/// in the active `DisplayContext`. The precision check is essential — see
/// `looks_like_currency`'s docstring for why a heuristic-only filter would
/// regress output.
///
/// Multi-currency-column GROUP BY (rare but possible) takes the *first*
/// match in iteration order — see `QueryResult::add_aggregate_row`'s
/// docstring for the contract.
fn currency_hint_for_row<'a>(
    result: &'a rustledger_query::QueryResult,
    row_idx: usize,
    ctx: &DisplayContext,
) -> Option<&'a str> {
    result.group_key(row_idx).and_then(|key_values| {
        key_values.iter().find_map(|v| match v {
            Value::String(s)
                if looks_like_currency(s) && ctx.get_precision(s.as_str()).is_some() =>
            {
                Some(s.as_str())
            }
            _ => None,
        })
    })
}

/// Combine row sidecar and column-name hints into a single per-cell hint.
///
/// Precedence: **row hint wins** over column-name fallback. The row sidecar
/// came from the actual GROUP BY key (`add_aggregate_row`), so it's a more
/// authoritative signal than the column name (a heuristic from
/// `looks_like_currency`).
///
/// Pinning the precedence in one helper guarantees the width-calculation
/// pass and the print pass agree — they MUST, otherwise rendered widths
/// don't match the rendered values they were sized for.
fn resolve_cell_hint<'a>(
    row_hints: &[Option<&'a str>],
    col_hints: &[Option<&'a str>],
    row_idx: usize,
    col_idx: usize,
) -> Option<&'a str> {
    row_hints
        .get(row_idx)
        .copied()
        .flatten()
        .or_else(|| col_hints.get(col_idx).copied().flatten())
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
///
/// The caller is responsible for ensuring the hint resolves to a currency
/// with tracked precision (`ctx.get_precision(currency).is_some()`) — pass
/// `None` otherwise. See `currency_hint_for_row` for the canonical
/// extraction path.
pub(super) fn format_value_with_hint(
    value: &Value,
    numberify: bool,
    ctx: &DisplayContext,
    currency_hint: Option<&str>,
) -> String {
    if let (Value::Number(n), Some(currency)) = (value, currency_hint) {
        // Debug-only tripwire for the contract documented above: fire if a
        // future caller passes a hint without filtering through the
        // precision gate first. Only meaningful inside this branch — for
        // non-Number values the hint is ignored, so a "bad" hint there is
        // harmless. Release builds skip the check; the worst observable
        // effect is the strip-trailing-zeros regression that the gate
        // was designed to prevent.
        debug_assert!(
            ctx.get_precision(currency).is_some(),
            "format_value_with_hint called with currency {currency:?} lacking \
             tracked precision in the DisplayContext — would silently strip \
             trailing zeros via the normalize() fallback. Filter via \
             currency_hint_for_row first."
        );
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
                    // `{ N CCY}` — leading space inside `{` matches
                    // Beancount Position.__str__. Pre-fix this emitted
                    // `{N CCY}` and accounted for ~137 of 510 BQL
                    // compat (file × query) mismatches.
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
                            // See `Value::Position` arm above for why
                            // there's a leading space after `{`.
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

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Cost, Inventory, Position};

    /// Cost-spec braces in BQL output match Beancount's
    /// `Position.__str__`: `{ 128.99 USD}` — single space after `{`,
    /// no space before `}`.
    ///
    /// Earlier (#987) tests pinned the no-leading-space form after
    /// comparing against an older bean-query release that emitted
    /// `{128.99 USD}`. With beanquery 0.2.0 + beancount 3.2.3 (what
    /// CI installs and the dev shell ships via the compat container,
    /// PR #1047), bean-query renders with the leading space — so
    /// matching it closes ~137 of 510 BQL compat (file × query)
    /// mismatches. Pin both `Position` and `Inventory` paths so a
    /// future format change can't silently regress.
    #[test]
    fn test_position_with_cost_matches_beancount_position_str() {
        let pos = Position::with_cost(
            Amount::new(dec!(8.373), "RGAGX"),
            Cost::new(dec!(128.99), "USD"),
        );
        let value = Value::Position(Box::new(pos));
        let ctx = DisplayContext::new();
        let rendered = format_value(&value, false, &ctx);

        assert!(
            rendered.contains("{ 128.99 USD}"),
            "expected `{{ 128.99 USD}}` (matching bean-query), got {rendered:?}"
        );
        assert!(
            !rendered.contains(" }"),
            "no space immediately before `}}`, got {rendered:?}"
        );
    }

    #[test]
    fn test_inventory_with_cost_matches_beancount_position_str() {
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
            rendered.contains("{ 128.99 USD}") && rendered.contains("{ 131.73 USD}"),
            "expected both costs rendered with leading space, got {rendered:?}"
        );
    }

    // ─── Issue #988 ──────────────────────────────────────────────────────
    // SUM-aggregate text output should match bean-query's per-currency
    // precision. With `SELECT currency, SUM(number) GROUP BY currency`, the
    // SUM cell receives the GROUP BY currency from the row sidecar and
    // quantizes via DisplayContext. Concretely, the bug shows up when
    // inputs have varying scales (e.g. one `0.000` mixed with several
    // `0.00`s): `rust_decimal::Decimal::add` returns max-scale, so the sum
    // keeps the wider `0.000` form even though USD's tracked precision is
    // 2dp. After the fix, the per-currency hint pulls the SUM through
    // `DisplayContext::format(_, "USD")`, rounding back to 2dp.
    //
    // JSON / CSV / beancount paths still go through `format_value` (no
    // hint), preserving the unquantized value (AC #4: lossless non-text
    // output).

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
        assert!(!looks_like_currency("U")); // single char (real currencies are 2+)
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

    /// Critical regression: `DisplayContext::format(n, currency)` falls
    /// back to `n.normalize()` when the currency has no tracked precision,
    /// which STRIPS trailing zeros. So a false-positive hint isn't a no-op
    /// — it would render `0.000` as `0`, making output WORSE than the
    /// pre-fix state. The gate lives in `currency_hint_for_row` (only
    /// returns hints for currencies that pass `ctx.get_precision().is_some()`);
    /// this test pins that contract end-to-end.
    #[test]
    fn test_currency_hint_for_row_filters_untracked_currencies() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut result = QueryResult::new(vec!["currency".into(), "sum".into()]);
        // Row 0: GROUP BY key contains tracked USD → hint returned.
        result.add_aggregate_row(
            vec![Value::String("USD".into()), Value::Number(dec!(0.000))],
            vec![Value::String("USD".into())],
        );
        // Row 1: GROUP BY key contains MADEUP — passes shape check but
        // has no tracked precision → hint MUST be filtered out.
        result.add_aggregate_row(
            vec![Value::String("MADEUP".into()), Value::Number(dec!(0.000))],
            vec![Value::String("MADEUP".into())],
        );

        let usd_hint = currency_hint_for_row(&result, 0, &ctx);
        let madeup_hint = currency_hint_for_row(&result, 1, &ctx);

        assert_eq!(usd_hint, Some("USD"));
        assert_eq!(
            madeup_hint, None,
            "untracked currency must NOT be returned as a hint — would cause \
             DisplayContext::format to strip trailing zeros via normalize()"
        );
    }

    // ─── AC #4: lossless CSV / JSON / beancount output ───────────────────
    //
    // The fix MUST NOT bleed into non-text renderers. Aggregate values
    // there should still be the unquantized rust_decimal — JSON consumers
    // parsing exact scales depend on this. These tests pin the contract
    // by rendering an aggregate `Value::Number(0.000)` with a USD
    // GROUP BY key context that *would* be quantized in text mode.

    /// CSV of an aggregate row preserves the unquantized decimal even
    /// when a GROUP BY currency would otherwise drive 2dp quantization.
    #[test]
    fn test_csv_aggregate_output_preserves_unquantized_decimal() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut result = QueryResult::new(vec!["currency".into(), "sum".into()]);
        result.add_aggregate_row(
            vec![Value::String("USD".into()), Value::Number(dec!(0.000))],
            vec![Value::String("USD".into())],
        );

        let mut buf: Vec<u8> = Vec::new();
        write_csv(&result, &mut buf, false, &ctx).expect("csv ok");
        let csv = String::from_utf8(buf).expect("utf8");

        // Parse the data row by splitting on lines and commas — robust
        // to either `\n` or `\r\n` line endings that platform-specific
        // String/I/O might emit.
        let data_row = csv
            .lines()
            .nth(1)
            .expect("CSV should have a header line + 1 data row");
        let cells: Vec<&str> = data_row.split(',').collect();
        assert_eq!(cells.len(), 2, "expected 2 columns, got: {cells:?}");
        assert_eq!(cells[0], "USD");
        assert_eq!(
            cells[1], "0.000",
            "CSV sum cell must be the unquantized 0.000 (lossless AC #4)"
        );
    }

    /// JSON of an aggregate row likewise preserves the unquantized
    /// decimal — JSON consumers (e.g. downstream pipelines reading
    /// `bean-query --format json`) get the raw `rust_decimal` scale.
    #[test]
    fn test_json_aggregate_output_preserves_unquantized_decimal() {
        use rustledger_query::QueryResult;

        // `write_json` takes no DisplayContext — it serializes raw Decimal
        // values via `to_string()`, so per-currency precision can't bleed
        // into the JSON path even by accident.

        let mut result = QueryResult::new(vec!["currency".into(), "sum".into()]);
        result.add_aggregate_row(
            vec![Value::String("USD".into()), Value::Number(dec!(0.000))],
            vec![Value::String("USD".into())],
        );

        let mut buf: Vec<u8> = Vec::new();
        write_json(&result, &mut buf).expect("json ok");
        let json = String::from_utf8(buf).expect("utf8");

        // Lossless: the literal string "0.000" appears as the Number's
        // serialized form. Quoted (since the JSON emitter stringifies
        // decimals to preserve precision).
        assert!(
            json.contains(r#""0.000""#),
            "expected unquantized \"0.000\" in JSON, got {json}"
        );
        // And the quantized form must NOT appear. `r#""0.00""#` is a
        // unique substring (the closing quote distinguishes it from
        // `"0.000"` — `0.000` contains `0.00` but not `0.00"`).
        assert!(
            !json.contains(r#""0.00""#),
            "JSON must NOT contain quantized \"0.00\", got {json}"
        );
    }

    /// `bean-query`-style beancount output similarly stays at the
    /// natural decimal scale.
    #[test]
    fn test_beancount_aggregate_output_preserves_unquantized_decimal() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut result = QueryResult::new(vec!["currency".into(), "sum".into()]);
        result.add_aggregate_row(
            vec![Value::String("USD".into()), Value::Number(dec!(0.000))],
            vec![Value::String("USD".into())],
        );

        let mut buf: Vec<u8> = Vec::new();
        write_beancount(&result, &mut buf, &ctx).expect("beancount ok");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("0.000"),
            "expected unquantized 0.000 in beancount output, got {out:?}"
        );
    }

    /// Mirror of the AC #4 tests for the *text* renderer: same input
    /// MUST be quantized. This is the bug we're fixing — without the
    /// hint, text output would also keep 0.000. Together with the
    /// three lossless tests above, this pins the divergence: text
    /// quantizes, everything else doesn't.
    #[test]
    fn test_text_aggregate_output_quantizes_via_currency_hint() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");
        ctx.update(dec!(3.00), "USD");

        let mut result = QueryResult::new(vec!["currency".into(), "sum".into()]);
        result.add_aggregate_row(
            vec![Value::String("USD".into()), Value::Number(dec!(0.000))],
            vec![Value::String("USD".into())],
        );

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("text ok");
        let text = String::from_utf8(buf).expect("utf8");

        assert!(
            text.contains("0.00") && !text.contains("0.000"),
            "text output should be quantized to 2dp via USD hint, got {text:?}"
        );
    }

    /// End-to-end integration test (the canary the issue's compat
    /// harness would fire). Drives a real BQL query
    /// `SELECT currency, SUM(number) GROUP BY currency` through the
    /// Executor and the text renderer, then asserts the rendered
    /// output is quantized to USD's tracked precision (2dp) instead of
    /// `rust_decimal`'s natural 3dp.
    ///
    /// This is the only test in the file that exercises the FULL
    /// pipeline — Executor populates `row_group_keys`, `write_text`
    /// reads via `currency_hint_for_row`, format dispatches through
    /// `DisplayContext::format`. A regression that breaks the wiring
    /// (e.g. someone reverting `add_aggregate_row` to `add_row` in
    /// the executor) would fire here even if the helper-level tests
    /// stay green.
    #[test]
    fn test_e2e_sum_group_by_currency_text_output_matches_per_currency_precision() {
        use rustledger_core::{Amount, Directive, Posting, Transaction};
        use rustledger_query::{Executor, parse};

        let date = |y, m, d| rustledger_core::naive_date(y, m, d).unwrap();

        // Build a tiny ledger where SUM(number) GROUP BY currency on USD
        // mixes scales: 5.00 + (-5.00) + 0.000 = 0.000 (rust_decimal
        // natural). Without the fix this renders as `0.000`. With the
        // fix and a USD-tracked DisplayContext at 2dp, it should render
        // as `0.00`.
        let directives = vec![
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Coffee")
                    .with_flag('*')
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-5.00), "USD"))),
            ),
            // A scale-3 input that bumps SUM's natural scale to 3.
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "Refund")
                    .with_flag('*')
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(0.000), "USD"),
                    ))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(0.0), "USD"))),
            ),
        ];

        // Build a DisplayContext that would naturally come from the
        // loader observing typical USD amounts at 2dp.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(5.00), "USD");
        ctx.update(dec!(-5.00), "USD");

        let mut executor = Executor::new(&directives);
        let query =
            parse("SELECT currency, SUM(number) GROUP BY currency").expect("parse should succeed");
        let result = executor.execute(&query).expect("execute should succeed");

        // The executor MUST have recorded the GROUP BY currency.
        // Otherwise the renderer can't know to quantize.
        assert!(
            result.group_key(0).is_some(),
            "aggregate executor must populate row_group_keys; got None for row 0"
        );

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("write_text ok");
        let text = String::from_utf8(buf).expect("utf8");

        // Anchor the assertion on the data-row's last whitespace-
        // separated token (the SUM cell, right-aligned). Avoids a
        // brittle global substring scan: e.g. an unrelated "0.0001"
        // elsewhere in the table would defeat a `!text.contains("0.000")`
        // check, but the column-anchored slice is the actual contract.
        let data_row = text
            .lines()
            .find(|l| l.contains("USD"))
            .unwrap_or_else(|| panic!("expected a USD data row; raw output:\n{text}"));
        let sum_cell = data_row
            .split_whitespace()
            .last()
            .unwrap_or_else(|| panic!("expected non-empty data row; got: {data_row:?}"));
        assert_eq!(
            sum_cell, "0.00",
            "SUM cell should be quantized to USD's 2dp; row was {data_row:?}, raw output:\n{text}"
        );
    }

    /// Implicit GROUP BY: when the SELECT clause mixes aggregate and
    /// non-aggregate exprs without an explicit `GROUP BY`, the executor
    /// implicitly groups by the non-aggregate columns
    /// (`extract_implicit_group_by_exprs` in
    /// `rustledger-query/src/executor/aggregation.rs`). This test
    /// verifies the implicit path also populates `row_group_keys` with
    /// the currency, so the renderer's quantization works for queries
    /// that omit `GROUP BY` — bean-query's most common shape.
    #[test]
    fn test_e2e_implicit_group_by_currency_text_output_quantized() {
        use rustledger_core::{Amount, Directive, Posting, Transaction};
        use rustledger_query::{Executor, parse};

        let date = |y, m, d| rustledger_core::naive_date(y, m, d).unwrap();

        let directives = vec![
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "T1")
                    .with_flag('*')
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-5.00), "USD"))),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "T2")
                    .with_flag('*')
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(0.000), "USD"),
                    ))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(0.0), "USD"))),
            ),
        ];

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(5.00), "USD");
        ctx.update(dec!(-5.00), "USD");

        let mut executor = Executor::new(&directives);
        // Note: NO `GROUP BY currency` — implicit grouping kicks in.
        let query = parse("SELECT currency, SUM(number)").expect("parse should succeed");
        let result = executor.execute(&query).expect("execute should succeed");

        assert!(
            result.group_key(0).is_some(),
            "implicit-group-by aggregate must populate row_group_keys"
        );

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("write_text ok");
        let text = String::from_utf8(buf).expect("utf8");

        let data_row = text
            .lines()
            .find(|l| l.contains("USD"))
            .unwrap_or_else(|| panic!("expected USD data row; raw output:\n{text}"));
        let sum_cell = data_row.split_whitespace().last().expect("non-empty row");
        assert_eq!(
            sum_cell, "0.00",
            "implicit GROUP BY should quantize same as explicit; got {sum_cell:?} \
             in row {data_row:?}\n full output:\n{text}"
        );
    }

    /// Multi-column GROUP BY: when the key has both a non-currency
    /// column (account) and a currency column, the renderer should
    /// pick the currency-shaped string regardless of position. Pins
    /// the contract documented on `add_aggregate_row`.
    #[test]
    fn test_currency_hint_for_row_finds_currency_in_multi_column_group_by_key() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut result = QueryResult::new(vec!["account".into(), "currency".into(), "sum".into()]);
        // Key order: [account="Assets:Bank", currency="USD"]. account
        // doesn't pass `looks_like_currency` (lowercase chars + colon),
        // so the iterator skips to the second key element and picks USD.
        result.add_aggregate_row(
            vec![
                Value::String("Assets:Bank".into()),
                Value::String("USD".into()),
                Value::Number(dec!(0.000)),
            ],
            vec![
                Value::String("Assets:Bank".into()),
                Value::String("USD".into()),
            ],
        );

        let hint = currency_hint_for_row(&result, 0, &ctx);
        assert_eq!(
            hint,
            Some("USD"),
            "expected USD hint extracted from second key element"
        );
    }

    /// Pins the documented "first match wins" contract on
    /// `add_aggregate_row`: when TWO currency-shaped strings appear in
    /// the GROUP BY key (rare but possible — e.g.
    /// `GROUP BY currency, quote_currency`), iteration picks the first
    /// one. A future change to `find_map` → `last`, scoring, or
    /// alphabetical-min would break this test (which is the point —
    /// the contract is load-bearing for downstream behavior).
    #[test]
    fn test_currency_hint_for_row_first_currency_wins_when_multiple() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        // Both EUR and USD have tracked precision so the gate doesn't
        // disambiguate — only the iteration order does.
        ctx.update(dec!(1.00), "EUR");
        ctx.update(dec!(2.00), "EUR");
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut result = QueryResult::new(vec![
            "currency".into(),
            "quote_currency".into(),
            "sum".into(),
        ]);
        // Row 0 key: [EUR, USD]. First-wins → EUR.
        result.add_aggregate_row(
            vec![
                Value::String("EUR".into()),
                Value::String("USD".into()),
                Value::Number(dec!(0.000)),
            ],
            vec![Value::String("EUR".into()), Value::String("USD".into())],
        );
        // Row 1 key: [USD, EUR] — reversed. Confirms the result tracks
        // key order, not some side property of EUR/USD specifically.
        result.add_aggregate_row(
            vec![
                Value::String("USD".into()),
                Value::String("EUR".into()),
                Value::Number(dec!(0.000)),
            ],
            vec![Value::String("USD".into()), Value::String("EUR".into())],
        );

        assert_eq!(
            currency_hint_for_row(&result, 0, &ctx),
            Some("EUR"),
            "first-wins: [EUR, USD] should pick EUR"
        );
        assert_eq!(
            currency_hint_for_row(&result, 1, &ctx),
            Some("USD"),
            "first-wins: [USD, EUR] should pick USD"
        );
    }

    // ─── Issue #1023: PIVOT BY currency precision ────────────────────────
    //
    // After PIVOT, the GROUP BY currency moves into column position and
    // each pivoted column's *name* is a currency code. The pivot path
    // uses `add_row` (not `add_aggregate_row`), so the per-row sidecar is
    // `None` for those rows. The renderer needs a column-name fallback
    // to recover the precision context.

    /// Pivoted rows have `None` `group_key` but the column name is a
    /// currency code. The width-calc and print passes both consult the
    /// column-name fallback, so a `Value::Number(0.000)` in a USD-named
    /// column should render as `0.00` (matching USD's tracked 2dp).
    #[test]
    fn test_text_pivoted_column_uses_column_name_as_currency_hint() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        // Simulate post-PIVOT shape: the value cell is a Number whose
        // precision context lives in the column name "USD". No row
        // sidecar (mirrors what `apply_pivot` produces).
        let mut result = QueryResult::new(vec!["account".into(), "USD".into()]);
        result.add_row(vec![
            Value::String("Assets:Cash".into()),
            Value::Number(dec!(0.000)),
        ]);

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("text ok");
        let text = String::from_utf8(buf).expect("utf8");

        let data_row = text
            .lines()
            .find(|l| l.contains("Assets:Cash"))
            .unwrap_or_else(|| panic!("expected an Assets:Cash row; raw output:\n{text}"));
        let last_cell = data_row
            .split_whitespace()
            .last()
            .unwrap_or_else(|| panic!("expected non-empty data row; got: {data_row:?}"));
        assert_eq!(
            last_cell, "0.00",
            "pivoted column named USD should drive 2dp quantization; row was {data_row:?}, raw output:\n{text}"
        );
    }

    /// False-positive guard: a column literally named "USD" but with no
    /// tracked precision in the active context must NOT route through
    /// `DisplayContext::format` — the unknown-currency fallback there
    /// calls `normalize()` which strips trailing zeros. Without this
    /// gate, `0.000` would render as `0` (worse than the unfixed state).
    #[test]
    fn test_text_pivoted_column_with_untracked_currency_falls_back_safely() {
        // No DisplayContext seeding for USD — `get_precision("USD")`
        // returns None.
        let ctx = DisplayContext::new();

        let mut result = rustledger_query::QueryResult::new(vec!["account".into(), "USD".into()]);
        result.add_row(vec![
            Value::String("Assets:Cash".into()),
            Value::Number(dec!(0.000)),
        ]);

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("text ok");
        let text = String::from_utf8(buf).expect("utf8");

        // Without a tracked USD precision, the column-name fallback must
        // be filtered out and `format_value`'s default path retains the
        // natural 3dp scale.
        assert!(
            text.contains("0.000"),
            "untracked USD must NOT route through format → would strip zeros; got {text:?}"
        );
        assert!(
            !text.lines().any(|l| {
                l.contains("Assets:Cash")
                    && l.split_whitespace()
                        .last()
                        .is_some_and(|c| c == "0" || c == "0.00")
            }),
            "must not emit `0` (normalize-stripped) or `0.00` (false-positive quantize); got {text:?}"
        );
    }

    /// Precedence: row sidecar wins over column-name fallback. When both
    /// supply a hint (rare but possible: `GROUP BY currency PIVOT BY
    /// some_other_col`), the row's sidecar is the more authoritative
    /// signal — it came from the actual GROUP BY key, not a heuristic
    /// over the column header.
    #[test]
    fn test_row_sidecar_wins_over_column_name_fallback() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        // Both currencies tracked, but at different scales: USD=2dp, JPY=0dp.
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(100), "JPY");

        // Column name says JPY (0dp); row sidecar says USD (2dp).
        // The row sidecar must win → 2dp quantization.
        let mut result = QueryResult::new(vec!["account".into(), "JPY".into()]);
        result.add_aggregate_row(
            vec![
                Value::String("Assets:Cash".into()),
                Value::Number(dec!(0.000)),
            ],
            vec![Value::String("USD".into())],
        );

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("text ok");
        let text = String::from_utf8(buf).expect("utf8");

        let data_row = text
            .lines()
            .find(|l| l.contains("Assets:Cash"))
            .unwrap_or_else(|| panic!("expected Assets:Cash row; raw output:\n{text}"));
        let last_cell = data_row.split_whitespace().last().expect("non-empty row");
        assert_eq!(
            last_cell, "0.00",
            "row sidecar (USD, 2dp) must beat column name (JPY, 0dp); row was {data_row:?}"
        );
    }

    /// End-to-end integration test for issue #1023.
    /// Drives `SELECT currency, account, SUM(number) GROUP BY currency,
    /// account PIVOT BY currency` through the full pipeline. Mirrors
    /// `test_e2e_sum_group_by_currency_text_output_matches_per_currency_precision`
    /// but adds the PIVOT clause that was regressing #988's fix.
    ///
    /// Pins:
    /// - The pivoted USD column quantizes to 2dp via column-name fallback.
    /// - The non-pivoted columns (here just `account`) are unaffected.
    /// - JSON output for the same query stays lossless (AC #2).
    #[test]
    fn test_e2e_pivot_by_currency_text_output_matches_per_currency_precision() {
        use rustledger_core::{Amount, Directive, Posting, Transaction};
        use rustledger_query::{Executor, parse};

        let date = |y, m, d| rustledger_core::naive_date(y, m, d).unwrap();

        // Two USD postings whose SUM lands at scale 3 (mixing 0.000 and
        // 5.00 in rust_decimal yields a 3dp natural form). The PIVOT
        // BY currency would lose the precision hint without #1023's
        // column-name fallback.
        let directives = vec![
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Coffee")
                    .with_flag('*')
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-5.00), "USD"))),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "Refund")
                    .with_flag('*')
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(0.000), "USD"),
                    ))
                    .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(0.0), "USD"))),
            ),
        ];

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(5.00), "USD");
        ctx.update(dec!(-5.00), "USD");

        let mut executor = Executor::new(&directives);
        // Two-column PIVOT BY (post-#1034): first arg is the pivot value
        // column, second is the GROUP BY column to keep as the row key.
        let query = parse(
            "SELECT account, currency, SUM(number) \
             GROUP BY account, currency \
             PIVOT BY currency, account",
        )
        .expect("parse should succeed");
        let result = executor.execute(&query).expect("execute should succeed");

        // After PIVOT, the per-row sidecar is None (apply_pivot's
        // contract — it uses add_row, not add_aggregate_row). This
        // contract is exactly why #1023 needed the column-name fallback.
        assert!(
            !result.has_aggregate_rows()
                || (0..result.rows.len()).all(|i| result.group_key(i).is_none()),
            "post-PIVOT rows should have no per-row group_key; the column-name fallback is what carries the hint"
        );

        // The USD column must exist as a pivoted output column.
        assert!(
            result.columns.iter().any(|c| c == "USD"),
            "expected pivoted USD column, got columns={:?}",
            result.columns
        );

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("write_text ok");
        let text = String::from_utf8(buf).expect("utf8");

        // The bug surface is "the rendered text contains 0.000". Without
        // #1023's column-name fallback, the post-PIVOT SUM cell would
        // render at rust_decimal's natural 3dp scale. With the fix, USD's
        // tracked 2dp drives the column, so 0.000 should NOT appear in
        // the pivoted USD cell.
        //
        // We check this two ways:
        //   1. The full output (excluding the row-count footer line)
        //      must not contain "0.000" — this is the cleanest contract.
        //   2. At least one data row must contain "0.00" (anchored as a
        //      whole token) — confirms quantization actually happened
        //      and we're not just missing data.
        let data_section = text
            .lines()
            .filter(|l| !l.contains("row(s)"))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            !data_section.contains("0.000"),
            "USD pivoted column must be quantized to 2dp; found 0.000 in output:\n{text}"
        );

        let saw_quantized = text.lines().any(|l| {
            !l.contains("row(s)")
                && l.split_whitespace()
                    .any(|t| t == "0.00" || t.ends_with(".00"))
        });
        assert!(
            saw_quantized,
            "expected at least one 2dp-quantized cell in the data section; raw output:\n{text}"
        );

        // AC #2 (lossless non-text output) is independently pinned by
        // `test_json_aggregate_output_preserves_unquantized_decimal`,
        // `test_csv_aggregate_output_preserves_unquantized_decimal`, and
        // `test_beancount_aggregate_output_preserves_unquantized_decimal`
        // above — those use hand-built `QueryResult`s with a known
        // unquantized scale, which is more reliable than building one
        // through the executor (rust_decimal's add behavior can normalize
        // scales in ways that depend on input shape, making a contrived
        // fixture brittle). The text-renderer behavior IS the contract
        // this PR changes; the JSON path goes through `write_json`
        // unchanged.
    }

    /// Multi-currency PIVOT: USD column at 2dp, JPY column at 0dp on the
    /// same row. Each pivoted column must use its OWN precision via the
    /// per-column hint — the column-name fallback isn't a single global
    /// setting, it's resolved per cell.
    #[test]
    fn test_text_pivoted_multi_currency_uses_per_column_precision() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        // USD seeded at 2dp, JPY at 0dp.
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");
        ctx.update(dec!(100), "JPY");
        ctx.update(dec!(200), "JPY");

        // Simulate post-PIVOT shape: same row has BOTH a USD value at
        // scale 3 and a JPY value at scale 2. After the per-column
        // fallback, USD should render at 2dp and JPY at 0dp.
        let mut result = QueryResult::new(vec!["account".into(), "USD".into(), "JPY".into()]);
        result.add_row(vec![
            Value::String("Assets:Cash".into()),
            Value::Number(dec!(0.000)),
            Value::Number(dec!(50.00)),
        ]);

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("text ok");
        let text = String::from_utf8(buf).expect("utf8");

        let data_row = text
            .lines()
            .find(|l| l.contains("Assets:Cash"))
            .unwrap_or_else(|| panic!("expected Assets:Cash row; raw output:\n{text}"));

        // Pull both numeric cells. Whitespace-split is safe here — both
        // numeric cells have no internal whitespace and the account name
        // has no spaces.
        let tokens: Vec<&str> = data_row.split_whitespace().collect();
        let [_account, usd_cell, jpy_cell] = tokens.as_slice() else {
            panic!("expected 3 whitespace-separated tokens, got: {tokens:?}");
        };
        assert_eq!(
            *usd_cell, "0.00",
            "USD column should render at 2dp; row was {data_row:?}"
        );
        assert_eq!(
            *jpy_cell, "50",
            "JPY column should render at 0dp (integer); row was {data_row:?}"
        );
    }

    /// Defensive regression test: a non-pivoted query with a column
    /// aliased as a currency code (e.g. `SELECT … AS USD`) must NOT have
    /// its values silently quantized when the active context tracks USD
    /// for unrelated reasons.
    ///
    /// The column-name fallback's `ctx.get_precision().is_some()` guard
    /// would let the hint kick in if USD is tracked. The expected behavior
    /// here is debatable — but pinning it as a test means a future change
    /// will be a deliberate choice, not a silent drift.
    ///
    /// Today's contract: WITH tracked USD precision, the fallback DOES
    /// quantize cells in the USD-aliased column. This is the same
    /// behavior PIVOT relies on; we're just acknowledging that
    /// non-pivoted queries inherit it too. If it turns out to be a real
    /// problem in practice, the fix is to gate the fallback on something
    /// PIVOT-specific (e.g. a boolean on `QueryResult` set by
    /// `apply_pivot`).
    #[test]
    fn test_non_pivoted_currency_named_column_inherits_fallback_quantization() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        // Non-pivoted result: column literally named USD, value at scale 3.
        // No row sidecar (so `currency_hints` is empty for this row).
        let mut result = QueryResult::new(vec!["label".into(), "USD".into()]);
        result.add_row(vec![
            Value::String("test".into()),
            Value::Number(dec!(0.000)),
        ]);

        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("text ok");
        let text = String::from_utf8(buf).expect("utf8");

        // With USD tracked at 2dp, the column-name fallback applies even
        // outside the PIVOT path. Pin this behavior so a future tightening
        // (e.g. PIVOT-only fallback) is a deliberate change.
        let data_row = text
            .lines()
            .find(|l| l.contains("test"))
            .unwrap_or_else(|| panic!("expected `test` row; raw output:\n{text}"));
        let last_cell = data_row.split_whitespace().last().expect("non-empty row");
        assert_eq!(
            last_cell, "0.00",
            "currency-named column drives quantization regardless of PIVOT path; row was {data_row:?}"
        );
    }
}
