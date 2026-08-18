//! Query result output formatting (text, CSV, JSON, beancount).

use super::ShellSettings;
use anyhow::{Context, Result};
use rustledger_core::format::escape_csv;
use rustledger_core::{Directive, DisplayContext, Spanned};
use rustledger_loader::SourceMap;
use rustledger_query::{Executor, Value, parse as parse_query};
use std::io::Write;

/// Cap on the dynamic width passed to `write!("{:width$}", .., width = w)`.
/// `std::fmt::rt::Argument::from_usize` panics with "Formatting argument
/// out of range" when the runtime width exceeds `u16::MAX`. Cells wider
/// than this cap are still written verbatim because `write!` does not
/// truncate when content length exceeds the requested width — capping
/// only suppresses padding, which is the correct fallback at this scale
/// (no terminal can usefully align 65k-character columns). Surfaces on
/// JOURNAL queries with thousands of lots in the `balance` column (#1086).
const MAX_COLUMN_WIDTH: usize = u16::MAX as usize;

pub(super) fn execute_query<W: Write>(
    query_str: &str,
    directives: &[Spanned<Directive>],
    source_map: &SourceMap,
    settings: &ShellSettings,
    writer: &mut W,
) -> Result<()> {
    // Parse the query
    let query = parse_query(query_str).with_context(|| "failed to parse query")?;

    // Execute. Use the source-map-aware constructor so the `filename`/`lineno`
    // columns (and `meta`-derived location lookups) resolve to real source
    // positions instead of NULL.
    let mut executor = Executor::new_with_sources(directives, source_map);
    executor.set_account_types(settings.account_types.clone());
    let result = executor
        .execute(&query)
        .with_context(|| "failed to execute query")?;

    // Output results using display context for consistent number formatting.
    // `render_commas` is resolved ONCE here, against the surface being written,
    // so each writer receives a context it can use verbatim (#1892).
    let ctx = &settings.display_context.for_surface(settings.format.into());
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
    // `render_commas` is presentation policy for the whole table, not a
    // per-column precision fact, so every column carries it regardless of what
    // it holds. It used to arrive only as a side effect of the Number-column
    // `update_from` below, which meant `SUM(number)` printed `1,234,567.89`
    // while `SUM(position)` in the same query printed `1234567.89 USD`
    // (issue #1892). Adopt the policy WHOLE — the ledger-wide flag plus every
    // per-commodity override — rather than copying the global bit, which left
    // a commodity's own `render_commas:` declaration unreadable here (#1896).
    for col in &mut col_contexts {
        col.adopt_grouping_from(ctx);
    }
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

    // No per-cell currency hint. bean-query's `DecimalRenderer` renders a
    // naked Decimal at its INTRINSIC scale and never quantizes — it pads only
    // for decimal-point alignment — so any per-currency rounding here is a
    // divergence, in either direction.
    //
    // #988 and #1023 both added one, to compensate for SUM losing scale
    // during accumulation. #2046 fixed that at the source (`add_python_scale`
    // — `rust_decimal` dropped a zero operand's scale), which left the hints
    // padding output that was already correct. Measured against bean-query
    // 3.2.3:
    //
    //     SELECT currency, SUM(number) ...   py `-900`   rs `-900.00`
    //     PIVOT BY ... (a scale-0 cell)      py `3`      rs `3.00`
    //
    // The second is the #1023 shape specifically: bean-query renders `-5.00`
    // and `5.000` in the SAME pivoted column, per cell, which is the clearest
    // statement that the column has no shared precision to impose.

    // Calculate column widths using per-column contexts. Each column is
    // clamped to `MAX_COLUMN_WIDTH` to keep the dynamic width passed to
    // `write!` below within the stdlib's `u16::MAX` cap — see the constant.
    let mut widths: Vec<usize> = result
        .columns
        .iter()
        .map(|c| c.len().min(MAX_COLUMN_WIDTH))
        .collect();

    for row in &result.rows {
        for (i, value) in row.iter().enumerate() {
            let col_ctx = col_contexts.get(i).unwrap_or(ctx);
            let len = format_value(value, numberify, col_ctx).len();
            if i < widths.len() && len > widths[i] {
                widths[i] = len.min(MAX_COLUMN_WIDTH);
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
    // `ctx` already has `render_commas` resolved for this surface by the
    // dispatcher, so it is used verbatim here.

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
        // Observe the NETTED positions, i.e. exactly what `format_value`
        // will print — see `rendered_inventory_positions`. Walking the raw
        // lots here made the histogram describe numbers that never appear
        // in the output.
        Value::Inventory(inv) => {
            for pos in rendered_inventory_positions(inv) {
                let quantized = ledger_ctx.quantize(pos.units.number, pos.units.currency.as_str());
                col_ctx.update(quantized, pos.units.currency.as_str());
                if let Some(ref cost) = pos.cost {
                    let quantized = ledger_ctx.quantize(cost.number, cost.currency.as_str());
                    col_ctx.update(quantized, cost.currency.as_str());
                }
            }
        }
        // A naked Decimal contributes NOTHING to the per-column histogram.
        // It used to feed the `__default__` bucket so the column could carry
        // its own dp, but nothing reads that: `format_value` renders a
        // `Value::Number` through `DisplayContext::format_default`, which
        // consults only the commas flag and never a precision. The bucket was
        // written on every cell and read by no one once the #988/#1023 hints
        // were removed.
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
/// Whether a `Position` should be omitted from `Value::Inventory` rendering.
///
/// **Exactly zero only.** This stands in for a difference in the INVENTORY,
/// not a display rule. `Inventory::add` coalesces same-key lots, so a lot that
/// is bought and then fully sold nets to a `0 ORNG {1 USD}` entry that stays in
/// the map; beancount drops the key at that point, so the position is simply
/// absent there and the cell renders blank.
///
/// Note `Inventory::positions()` is an unfiltered iterator over that map (the
/// `!p.is_empty()` filter lives on the `Display` impl, a different path), so
/// the coalesced zero does reach this filter and has to be dropped here.
/// Delete this the day `Inventory` drops zero-net keys itself.
///
/// # It used to also blank sub-precision residuals, and that was wrong
///
/// #1104 added a second test — round to the currency's display precision and
/// drop the position if that is zero — on the belief that bean-query
/// blank-cells a residual like `-0.0003183 USD`. It does not. Checked against
/// bean-query 3.2.3:
///
/// ```text
/// ; Assets:B holds 0.0003183 USD
/// bean-query "SELECT account, SUM(position) ..."
///   Assets:A            <- blank: inventory is EMPTY
///   Assets:B  0.00 USD  <- shown: the position exists, rounded for display
/// ```
///
/// beancount blanks an empty inventory, not a small number. Rounding to
/// `0.00` is display precision doing its job, and suppressing the row instead
/// hid real positions — the zero-sum fixtures reported nothing where
/// bean-query reported `0.00 USD` (#2015 tail).
const fn position_renders_as_zero(pos: &rustledger_core::Position) -> bool {
    // An exactly-zero position is one beancount's Inventory would have
    // REMOVED on reduction (a cost lot closed out, `0 ORNG {1 USD}`); ours
    // retains it, so this filter stands in for that difference and must stay
    // until the inventory itself drops them.
    pos.units.number.is_zero()
}
/// Collapse an inventory's raw lots into the positions that are actually
/// RENDERED: one per `(units currency, cost key)`, summed, in display order.
///
/// Shared deliberately by the formatter and by the display-precision
/// histogram in [`update_column_context`]. They used to derive this
/// separately — the formatter aggregated, the histogram walked
/// `inv.positions()` raw — so the column's inferred precision described a
/// different set of numbers than the ones printed.
///
/// That is not academic. A running `balance` column re-observes every
/// surviving lot on every row, so an early integer-valued lot is counted once
/// per row it persists in and can outvote the fractional lots that net against
/// it. On the `beancount-lazy-plugins` `COOL_FUND` ledger the raw walk yielded
/// 5 samples at 0dp against 4 at 7dp — mode 0 — and
/// `545.4545455 COOL_FUND_USD` printed as `545`, while bean-query (which
/// histograms the netted value it prints) chose 7dp. Aggregating first gives
/// 2 samples at 0dp against 4 at 7dp, and the two agree.
fn rendered_inventory_positions(
    inv: &rustledger_core::Inventory,
) -> Vec<rustledger_core::Position> {
    use rustc_hash::FxHashMap;
    use rustledger_core::{Cost, Currency, Position};

    // Key on the typed values rather than a formatted string. `Currency` and
    // `Cost` are both `Eq + Hash`, and `rust_decimal`'s `Hash` agrees with its
    // `Eq` — `1.00` and `1` compare equal AND hash equal — so lots written at
    // `{1.00 USD}` and `{1 USD}` still net together, which is what the old
    // key's `number.normalize()` was there to ensure. Avoids two allocations
    // per lot on a path walked once per row.
    // `FxHashMap`, sized up front. This runs once per OUTPUT ROW and inserts
    // once per lot, so on a long-held account it was the query's single largest
    // cost: SipHash plus the rehash of a map grown from empty accounted for
    // roughly a fifth of the run (#2086). The hasher is free to change here
    // because the sort below is total — the comment on its label arm records
    // why — so iteration order cannot reach the output.
    let mut aggregated: FxHashMap<(Currency, Option<Cost>), Position> =
        FxHashMap::with_capacity_and_hasher(inv.len(), rustc_hash::FxBuildHasher);
    for pos in inv.positions().filter(|p| !p.is_empty()) {
        let key = (pos.units.currency.clone(), pos.cost.clone());

        aggregated
            .entry(key)
            .and_modify(|existing| {
                existing.units.number += pos.units.number;
            })
            .or_insert_with(|| pos.clone());
    }

    // Drop positions that net to exactly zero. The formatter already skips
    // them (`position_renders_as_zero`), so leaving them in would reintroduce
    // in miniature the very mismatch this function exists to remove: a sample
    // in the histogram with no corresponding number in the output.
    let mut sorted_positions: Vec<Position> = aggregated
        .into_values()
        .filter(|p| !position_renders_as_zero(p))
        .collect();
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
                if ca.date != cb.date {
                    return ca.date.cmp(&cb.date);
                }
                // Label is the last discriminator. It is part of `Cost`'s
                // `Eq`/`Hash`, so two lots differing only by label survive
                // aggregation as separate entries — and without this arm they
                // compared Equal and their order fell out of `HashMap`
                // iteration, which is seeded per process. The same query on
                // the same file could print its rows in either order run to
                // run. With it the comparator is total: anything that still
                // ties shares a key and was already netted.
                ca.label.cmp(&cb.label)
            }
            (Some(_), None) => std::cmp::Ordering::Greater,
            (None, Some(_)) => std::cmp::Ordering::Less,
            (None, None) => std::cmp::Ordering::Equal,
        }
    });
    sorted_positions
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
                ctx.format_amount_number(a.number, a.currency.as_str())
            } else {
                ctx.format_amount(a.number, a.currency.as_str())
            }
        }
        Value::Position(p) => {
            if numberify {
                ctx.format_amount_number(p.units.number, p.units.currency.as_str())
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
            let sorted_positions = rendered_inventory_positions(inv);

            // No zero-filter here: `rendered_inventory_positions` already
            // applied it, so this list IS the printed set.
            let positions: Vec<String> = sorted_positions
                .iter()
                .map(|p| {
                    if numberify {
                        ctx.format_amount_number(p.units.number, p.units.currency.as_str())
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
            .map(|(k, v)| format!("{k}: {v}"))
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

/// Convert a metadata value to its canonical JSON form (decimals as strings to
/// preserve precision). Thin wrapper over the single source
/// [`rustledger_core::meta_value_to_json`]; without it the JSON output leaked
/// the Rust Debug form (e.g. `"String(\"good\")"`).
fn meta_value_to_json(v: &rustledger_core::MetaValue) -> serde_json::Value {
    rustledger_core::meta_value_to_json(v)
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
            "positions": inv.positions().map(|p| serde_json::json!({
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
                .map(|(k, v)| (k.clone(), meta_value_to_json(v)))
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

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Cost, Inventory, Position};

    /// The precision histogram must describe the numbers that are PRINTED.
    ///
    /// A running `balance` column carries the same lots forward row after row,
    /// so observing raw lots counts a long-lived one once per row it survives
    /// in. On the `COOL_FUND` ledger that gave 5 samples at 0dp against 4 at
    /// 7dp — mode 0 — and `545.4545455 COOL_FUND_USD` printed as `545`, while
    /// bean-query printed `545.4545455`. Netting first is what makes the two
    /// agree, so this asserts the histogram and the formatter see one list.
    #[test]
    fn test_column_context_observes_netted_positions_not_raw_lots() {
        let cost = Cost {
            number: dec!(1.00),
            currency: "USD".into(),
            date: Some(rustledger_core::NaiveDate::constant(2024, 1, 10)),
            label: None,
        };
        let lot = |n| Position {
            units: Amount::new(n, "COOL_FUND_USD"),
            cost: Some(cost.clone()),
        };
        let inv_of = |lots: &[rust_decimal::Decimal]| {
            let mut inv = Inventory::new();
            for n in lots {
                inv.add(lot(*n)).expect("add");
            }
            inv
        };

        // The cumulative balance as it appears on each row of the COOL_FUND
        // ledger. A single row would NOT expose the bug: its raw lots are one
        // 0dp and one 7dp sample, and `mode()` breaks that tie toward 7
        // anyway. It takes the running column, where the integer lot is
        // re-observed on every row it survives, for 0dp to win the vote.
        let rows = [
            vec![dec!(1000)],
            vec![dec!(1000)],
            vec![dec!(1000), dec!(-454.5454545)],
            vec![dec!(1000), dec!(-454.5454545)],
            vec![dec!(1000), dec!(-454.5454545), dec!(-545.4545455)],
            vec![dec!(1000), dec!(-454.5454545)],
        ];

        let ledger_ctx = DisplayContext::new();
        let mut col_ctx = DisplayContext::new();
        for lots in &rows {
            let value = Value::Inventory(std::sync::Arc::new(inv_of(lots)));
            update_column_context(&mut col_ctx, &value, &ledger_ctx);
        }

        // Netted, the column sees mostly 7dp values. Walking raw lots instead
        // counts `1000` once per row and drives the mode to 0, which printed
        // `545.4545455 COOL_FUND_USD` as `545` where bean-query printed it in
        // full.
        assert_eq!(
            col_ctx.get_precision("COOL_FUND_USD"),
            Some(7),
            "precision must be inferred from the netted values that are printed"
        );

        // The netting itself, and the end-to-end cell.
        let inv = inv_of(&rows[2]);
        let rendered = rendered_inventory_positions(&inv);
        assert_eq!(rendered.len(), 1, "lots at one cost net together");
        assert_eq!(rendered[0].units.number, dec!(545.4545455));
        let out = format_value(&Value::Inventory(std::sync::Arc::new(inv)), false, &col_ctx);
        assert!(out.starts_with("545.4545455 COOL_FUND_USD"), "got: {out}");
    }

    /// Ordering is deterministic for lots that differ only by cost label.
    ///
    /// `Cost`'s `Eq`/`Hash` include `label`, so `{1 USD, "lot-a"}` and
    /// `{1 USD, "lot-b"}` stay separate entries. Before the label tie-break
    /// they compared Equal and their relative order came from `HashMap`
    /// iteration — seeded per process, so a run could print either order.
    /// Rebuilding the inventory many times here is the point: a single
    /// construction cannot observe the instability.
    #[test]
    fn test_label_only_lots_have_deterministic_order() {
        let lot = |label: &str| Position {
            units: Amount::new(dec!(2), "AAA"),
            cost: Some(Cost {
                number: dec!(1),
                currency: "USD".into(),
                date: Some(rustledger_core::NaiveDate::constant(2024, 1, 1)),
                label: Some(label.to_string()),
            }),
        };

        let mut orderings = std::collections::HashSet::new();
        for _ in 0..200 {
            let mut inv = Inventory::new();
            inv.add(lot("lot-b")).expect("add");
            inv.add(lot("lot-a")).expect("add");
            let labels: Vec<String> = rendered_inventory_positions(&inv)
                .into_iter()
                .filter_map(|p| p.cost?.label)
                .collect();
            orderings.insert(labels.join(","));
        }
        assert_eq!(
            orderings,
            std::collections::HashSet::from(["lot-a,lot-b".to_string()]),
            "order must be stable and label-ascending"
        );
    }

    /// Lots whose costs are numerically equal but written at different
    /// scales — `{1.00 USD}` and `{1 USD}` — must still net into one
    /// position.
    ///
    /// This is load-bearing for the typed `(Currency, Option<Cost>)`
    /// aggregation key. The key it replaced stringified `number.normalize()`
    /// precisely to collapse those two; the typed key relies instead on
    /// `rust_decimal`'s `Hash` agreeing with its `Eq`. If that ever stopped
    /// holding, the lots would silently stop netting and the column would
    /// print two rows where beancount prints one.
    #[test]
    fn test_costs_equal_at_different_scales_net_together() {
        let cost = |n| {
            Some(Cost {
                number: n,
                currency: "USD".into(),
                date: Some(rustledger_core::NaiveDate::constant(2024, 1, 1)),
                label: None,
            })
        };
        let mut inv = Inventory::new();
        inv.add(Position {
            units: Amount::new(dec!(2), "AAA"),
            cost: cost(dec!(1.00)),
        })
        .expect("add");
        inv.add(Position {
            units: Amount::new(dec!(3), "AAA"),
            cost: cost(dec!(1)),
        })
        .expect("add");

        let rendered = rendered_inventory_positions(&inv);
        assert_eq!(
            rendered.len(),
            1,
            "`{{1.00 USD}}` and `{{1 USD}}` are the same lot: {rendered:?}"
        );
        assert_eq!(rendered[0].units.number, dec!(5));
    }

    /// Display order of the netted positions: currency, then quantity
    /// descending, then cost-less ahead of held-at-cost, then cost currency
    /// ascending, cost number descending, and acquisition date ascending.
    ///
    /// Covers the comparator arms the netting test above never reaches — it
    /// uses a single currency at a single cost, so every tie-break below was
    /// dead to it. Each lot here is given a DISTINCT cost key on purpose;
    /// sharing one would net the lots together (as the first draft of this
    /// test discovered) and the tie-break would never be compared.
    #[test]
    fn test_rendered_inventory_positions_display_order() {
        let day = |d| Some(rustledger_core::NaiveDate::constant(2024, 1, d));
        let at = |n, ccy: &str, d| {
            Some(Cost {
                number: n,
                currency: ccy.into(),
                date: day(d),
                label: None,
            })
        };
        let pos = |n, ccy: &str, cost| Position {
            units: Amount::new(n, ccy),
            cost,
        };

        let mut inv = Inventory::new();
        // Deliberately inserted out of display order.
        inv.add(pos(dec!(5), "ZZZ", None)).expect("add");
        inv.add(pos(dec!(1), "AAA", at(dec!(2), "USD", 2)))
            .expect("add");
        inv.add(pos(dec!(1), "AAA", at(dec!(2), "USD", 1)))
            .expect("add");
        inv.add(pos(dec!(1), "AAA", at(dec!(3), "USD", 1)))
            .expect("add");
        inv.add(pos(dec!(1), "AAA", at(dec!(2), "EUR", 1)))
            .expect("add");
        inv.add(pos(dec!(1), "AAA", None)).expect("add");
        inv.add(pos(dec!(7), "AAA", None)).expect("add");

        let got: Vec<_> = rendered_inventory_positions(&inv)
            .into_iter()
            .map(|p| {
                (
                    p.units.currency.to_string(),
                    p.units.number,
                    p.cost.map(|c| (c.number, c.currency.to_string(), c.date)),
                )
            })
            .collect();

        let aaa = |n, cost| ("AAA".to_string(), n, cost);
        assert_eq!(
            got,
            vec![
                // Quantity descending within a currency. The two cost-less
                // AAA lots share a key, so they net to 8.
                aaa(dec!(8), None),
                // Equal quantities: cost currency ascending...
                aaa(dec!(1), Some((dec!(2), "EUR".to_string(), day(1)))),
                // ...then cost number DESCENDING...
                aaa(dec!(1), Some((dec!(3), "USD".to_string(), day(1)))),
                // ...then acquisition date ascending.
                aaa(dec!(1), Some((dec!(2), "USD".to_string(), day(1)))),
                aaa(dec!(1), Some((dec!(2), "USD".to_string(), day(2)))),
                ("ZZZ".to_string(), dec!(5), None),
            ]
        );
    }

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
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(8.199), "RGAGX"),
            Cost::new(dec!(131.73), "USD"),
        ))
        .expect("fixture fits in Decimal");
        let value = Value::Inventory(std::sync::Arc::new(inv));
        let ctx = DisplayContext::new();
        let rendered = format_value(&value, false, &ctx);

        assert!(
            rendered.contains("{ 128.99 USD}") && rendered.contains("{ 131.73 USD}"),
            "expected both costs rendered with leading space, got {rendered:?}"
        );
    }

    /// `write_text` must not panic when a single cell renders to more
    /// than `u16::MAX` characters. `std::fmt::rt::Argument::from_usize`
    /// panics with "Formatting argument out of range" if a dynamic
    /// `{:width$}` width parameter exceeds `u16::MAX`, which happens on
    /// JOURNAL queries whose `balance` column holds inventories with
    /// thousands of lots (see #1086 stress workloads). The fix in
    /// `write_text` caps width at `u16::MAX`; cells wider than the cap
    /// are still written verbatim because `write!` does not truncate
    /// when content exceeds the requested width.
    #[test]
    fn test_write_text_does_not_panic_on_cells_wider_than_u16_max() {
        use rustledger_query::QueryResult;

        let mut result = QueryResult::new(vec!["wide".into()]);
        // 70_000 chars > u16::MAX = 65_535
        let wide = "x".repeat(70_000);
        result.add_row(vec![Value::String(wide.clone())]);

        let ctx = DisplayContext::new();
        let mut buf: Vec<u8> = Vec::new();
        write_text(&result, &mut buf, false, &ctx).expect("write_text must not panic on wide cell");

        let text = String::from_utf8(buf).expect("utf8");
        assert!(
            text.contains(&wide),
            "wide cell content must still appear verbatim in output"
        );
    }

    /// A position whose units round to zero at the currency's display
    /// precision is still a position the inventory HOLDS, so it renders —
    /// at that precision, as `0.00 USD`.
    ///
    /// This inverts #1104, which suppressed such cells believing bean-query
    /// blanked them. It does not: bean-query blanks an EMPTY inventory.
    /// Checked against bean-query 3.2.3 — an account holding `0.0003183 USD`
    /// renders `0.00 USD`, while one that netted to nothing renders blank.
    ///
    /// The SIGN survives the rounding: a `-0.0003183 USD` position renders
    /// `-0.00 USD`, not `0.00 USD`. This assertion read `0.00 USD` until the
    /// negative-zero work, because the doc note above was verified on the
    /// POSITIVE value while the fixture below uses the negative one — the
    /// sign was never re-checked against bean-query. It has been now, on a
    /// ledger whose USD precision is 2dp:
    ///
    /// ```text
    /// Assets:Neg  -0.00 USD
    /// ```
    ///
    /// That sign is the only thing distinguishing a small negative balance
    /// from an exactly flat one in the rendered cell.
    ///
    /// Concrete trigger: capital-gains residuals from cost-spec interpolation
    /// land near the noise floor (`-0.0003183 USD`). Suppressing them hid a
    /// real arithmetic divergence — see #2034.
    #[test]
    fn test_value_inventory_renders_sub_precision_positions() {
        let mut ctx = DisplayContext::new();
        // Seed USD precision at 2dp.
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        // Sub-cent residual: -0.0003183 USD is "zero at USD precision".
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(-0.0003183), "USD")))
            .expect("fixture fits in Decimal");

        let rendered = format_value(&Value::Inventory(std::sync::Arc::new(inv)), false, &ctx);
        assert_eq!(
            rendered, "-0.00 USD",
            "a sub-cent USD residual is a position the inventory HOLDS, so \
             bean-query renders it at USD precision rather than blanking it, \
             and keeps its sign; got {rendered:?}"
        );
    }

    #[test]
    fn test_metadata_renders_values_not_debug_form() {
        // Regression: a metadata dict must render its values through the normal
        // value path, not the Rust Debug form `String("good")`, in both the
        // text and JSON output.
        use rustledger_core::{MetaValue, Metadata};
        let mut meta = Metadata::default();
        meta.insert("rating".to_string(), MetaValue::String("good".to_string()));
        let value = Value::Metadata(Box::new(meta));

        let text = format_value(&value, false, &DisplayContext::new());
        assert!(
            !text.contains("String("),
            "Debug form leaked in text: {text:?}"
        );
        assert!(text.contains("rating: \"good\""), "got: {text:?}");

        let json = value_to_json(&value);
        assert_eq!(json["rating"], serde_json::json!("good"));
    }

    /// Sister test: a position that's NOT sub-precision should still render.
    /// Pins the boundary so a future regression that over-broadly suppresses
    /// (e.g., everything below 1 USD) would fail loudly.
    #[test]
    fn test_value_inventory_renders_above_precision() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(-0.01), "USD")))
            .expect("fixture fits in Decimal");

        let rendered = format_value(&Value::Inventory(std::sync::Arc::new(inv)), false, &ctx);
        assert!(
            rendered.contains("-0.01"),
            "-0.01 USD is exactly at USD precision; must still render. Got {rendered:?}"
        );
    }

    /// Pins post-#1113 fix: all three amount-typed values (`Value::Amount`,
    /// `Value::Position`, `Value::Inventory`) must quantize to the
    /// currency's tracked dp under `--numberify`, not preserve raw
    /// arithmetic scale. Was a Copilot-review catch on #1113 — the
    /// `Value::Amount` arm had been left on `format` while the other two
    /// were moved to `format_amount_number`.
    #[test]
    fn test_numberify_quantizes_all_amount_kinds_consistently() {
        let mut ctx = DisplayContext::new();
        // USD tracked at 2dp.
        ctx.update(dec!(100.00), "USD");
        ctx.update(dec!(50.25), "USD");

        let over_scale = dec!(-1202.00896);

        // Each of Amount, Position, Inventory wraps the same scale-5 value.
        let amount_val = Value::Amount(Amount::new(over_scale, "USD"));
        let pos_val = Value::Position(Box::new(Position::simple(Amount::new(over_scale, "USD"))));
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(over_scale, "USD")))
            .expect("fixture fits in Decimal");
        let inv_val = Value::Inventory(std::sync::Arc::new(inv));

        assert_eq!(format_value(&amount_val, true, &ctx), "-1202.01");
        assert_eq!(format_value(&pos_val, true, &ctx), "-1202.01");
        assert_eq!(format_value(&inv_val, true, &ctx), "-1202.01");
    }

    /// Cross-format coverage: a sub-precision position must render in CSV and
    /// beancount output too, not just the human-facing text table — the same
    /// correction as the text case above (#1104 had all three suppressing).
    ///
    /// This is distinct from the #988 AC#4 "lossless" contract for
    /// `Value::Number` (which preserves Decimal scale across non-text
    /// renderers): that contract is about NUMERIC precision; this fix
    /// is about ZERO-POSITION semantic suppression. Both happen to use
    /// `format_value`, but they target different value types and
    /// different concerns.
    #[test]
    fn test_csv_inventory_renders_sub_precision_positions() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(-0.0003183), "USD")))
            .expect("fixture fits in Decimal");

        let mut result = QueryResult::new(vec!["account".into(), "sum".into()]);
        result.add_row(vec![
            Value::String("Income:Capital-Gains".into()),
            Value::Inventory(std::sync::Arc::new(inv)),
        ]);

        let mut buf: Vec<u8> = Vec::new();
        write_csv(&result, &mut buf, false, &ctx).expect("csv ok");
        let csv = String::from_utf8(buf).expect("utf8");

        let data_row = csv
            .lines()
            .find(|l| l.contains("Capital-Gains"))
            .unwrap_or_else(|| panic!("expected data row; raw output:\n{csv}"));

        // The position cell holds the residual, rendered at USD precision.
        // bean-query does NOT blank it: the inventory holds the position, so
        // it is shown as `0.00 USD`.
        let value_cell = data_row
            .split_once(',')
            .map(|(_, rest)| rest)
            .unwrap_or_default();
        assert!(
            value_cell.contains("0.00 USD"),
            "a sub-precision USD position must render at USD precision in the \
             CSV value cell; got cell {value_cell:?} in row {data_row:?}"
        );
    }

    #[test]
    fn test_beancount_inventory_renders_sub_precision_positions() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");

        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(-0.0003183), "USD")))
            .expect("fixture fits in Decimal");

        let mut result = QueryResult::new(vec!["sum".into()]);
        result.add_row(vec![Value::Inventory(std::sync::Arc::new(inv))]);

        let mut buf: Vec<u8> = Vec::new();
        write_beancount(&result, &mut buf, &ctx).expect("beancount ok");
        let out = String::from_utf8(buf).expect("utf8");

        assert!(
            out.contains("0.00 USD"),
            "a sub-precision USD position must render at USD precision in \
             beancount output; got {out:?}"
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

    /// End-to-end integration test (the canary the issue's compat
    /// harness would fire). Drives a real BQL query
    /// `SELECT currency, SUM(number) GROUP BY currency` through the
    /// Executor and the text renderer, then asserts the rendered
    /// output is quantized to USD's tracked precision (2dp) instead of
    /// `rust_decimal`'s natural 3dp.
    ///
    /// This is the only test in the file that exercises the FULL pipeline:
    /// Executor aggregates, `write_text` renders. It used to also pin the
    /// hint wiring (`row_group_keys` -> `currency_hint_for_row` ->
    /// `DisplayContext::format`); that path is gone, and what remains pinned
    /// is the thing that actually matters — the scale SUM produces survives
    /// to the output verbatim.
    #[test]
    fn test_e2e_sum_group_by_currency_text_output_matches_per_currency_precision() {
        use rustledger_core::{Amount, Directive, Posting, Transaction};
        use rustledger_query::{Executor, parse};

        let date = |y, m, d| rustledger_core::naive_date(y, m, d).unwrap();

        // The addends are `5.00, -5.00, 0.000, 0.0`, so the sum carries the
        // widest scale — 3 — and renders `0.000`. USD is tracked at 2dp here
        // deliberately: the renderer must NOT reach for that, in either
        // direction. bean-query 3.2.3 gives `0.000` on this ledger.
        let directives = vec![
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Coffee")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-5.00), "USD"),
                    )),
            ),
            // A scale-3 input that bumps SUM's natural scale to 3.
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "Refund")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(0.000), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(0.0), "USD"),
                    )),
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
        // `0.000`, not `0.00`. The fixture's addends are `5.00, -5.00,
        // 0.000, 0.0`, so Python's sum carries the widest scale — 3 — and
        // bean-query's `DecimalRenderer` prints a decimal at its intrinsic
        // scale without ever quantizing. Measured against bean-query 3.2.3
        // on this exact ledger:
        //
        //     py: USD  0.000
        //
        // This assertion previously read `0.00`, describing the pre-fix
        // accumulation: `rust_decimal`'s addition discards a zero operand's
        // scale, so the running total collapsed to 2dp and the #988 hint
        // padded it back to USD's 2dp. That agreed with neither bean-query
        // nor the arithmetic. See `rustledger_core::add_python_scale`.
        assert_eq!(
            sum_cell, "0.000",
            "SUM cell should carry the widest addend's scale; row was {data_row:?}, raw output:\n{text}"
        );
    }

    /// Implicit GROUP BY: when the SELECT clause mixes aggregate and
    /// non-aggregate exprs without an explicit `GROUP BY`, the executor
    /// implicitly groups by the non-aggregate columns
    /// (`extract_implicit_group_by_exprs` in
    /// `rustledger-query/src/executor/aggregation.rs`). This test
    /// verifies the implicit path also populates `row_group_keys` with
    /// the currency, so the renderer's hint resolution works for
    /// queries that omit `GROUP BY` — bean-query's most common shape.
    /// As with `test_e2e_sum_group_by_currency_*` above, the assertion
    /// holds because the SUM result scale is ≤ USD's tracked 2dp; for
    /// scale > tracked-dp behavior (post-#1106 preserve), see the
    /// `display_context.rs` unit tests.
    #[test]
    fn test_e2e_implicit_group_by_currency_text_output_quantized() {
        use rustledger_core::{Amount, Directive, Posting, Transaction};
        use rustledger_query::{Executor, parse};

        let date = |y, m, d| rustledger_core::naive_date(y, m, d).unwrap();

        let directives = vec![
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "T1")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-5.00), "USD"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "T2")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(0.000), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(0.0), "USD"),
                    )),
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
        // Same fixture, same reasoning as the explicit-GROUP BY test above:
        // bean-query renders `0.000` here.
        assert_eq!(
            sum_cell, "0.000",
            "implicit GROUP BY should render the same as explicit; got {sum_cell:?} \
             in row {data_row:?}\n full output:\n{text}"
        );
    }

    /// A naked Decimal renders at its INTRINSIC scale, whatever the column is
    /// called and whatever precision the currency has.
    ///
    /// This replaces four tests that pinned the opposite — the #988 row hint
    /// and the #1023 column-name fallback, both of which quantized a
    /// `Value::Number` to the currency's tracked dp. Both were compensating
    /// for SUM losing scale during accumulation, which #2046 fixed at the
    /// source; once the arithmetic was right they only padded output that
    /// already matched.
    ///
    /// bean-query 3.2.3 does not quantize a Decimal column at all — its
    /// `DecimalRenderer` pads for decimal-point ALIGNMENT and nothing else.
    /// Measured on ledgers whose USD precision is 2dp:
    ///
    /// ```text
    /// SELECT currency, SUM(number) GROUP BY currency   ->  EUR  -900
    /// PIVOT BY account, currency (a scale-0 cell)      ->  Expenses:B  3
    /// ```
    ///
    /// and, most directly, a single pivoted USD column holding two different
    /// scales at once:
    ///
    /// ```text
    ///                USD
    /// Assets:Bank  -5.00
    /// Expenses:A    5.000
    /// ```
    ///
    /// A column carrying `-5.00` and `5.000` together cannot have a shared
    /// precision to impose, which is the clearest statement of the rule.
    #[test]
    fn a_decimal_column_is_not_quantized_by_currency() {
        use rustledger_query::QueryResult;

        let mut ctx = DisplayContext::new();
        // USD tracked at 2dp, JPY at 0dp — neither may reach a Number cell.
        ctx.update(dec!(1.00), "USD");
        ctx.update(dec!(2.00), "USD");
        ctx.update(dec!(100), "JPY");

        // Shape 1: the #988 row sidecar — GROUP BY currency puts "USD" in the
        // row key, which used to pad the SUM cell to 2dp.
        let mut grouped = QueryResult::new(vec!["currency".into(), "sum".into()]);
        grouped.add_aggregate_row(
            vec![Value::String("USD".into()), Value::Number(dec!(0))],
            vec![Value::String("USD".into())],
        );
        assert_eq!(
            last_cell(&grouped, &ctx),
            "0",
            "a scale-0 SUM must not inherit USD's 2dp from the GROUP BY key",
        );

        // Shape 2: the #1023 column-name fallback — a PIVOT names the column
        // after the currency, which used to pad every cell in it.
        let mut pivoted = QueryResult::new(vec!["account".into(), "USD".into()]);
        pivoted.add_row(vec![
            Value::String("Assets:A".into()),
            Value::Number(dec!(0)),
        ]);
        assert_eq!(
            last_cell(&pivoted, &ctx),
            "0",
            "a column NAMED after a currency must not quantize its cells",
        );

        // Shape 3: mixed scales in one pivoted column each keep their own —
        // the property that makes a per-column precision impossible.
        let mut mixed = QueryResult::new(vec!["account".into(), "USD".into()]);
        mixed.add_row(vec![
            Value::String("Assets:Bank".into()),
            Value::Number(dec!(-5.00)),
        ]);
        mixed.add_row(vec![
            Value::String("Expenses:A".into()),
            Value::Number(dec!(5.000)),
        ]);
        // Exact cell tokens, not `contains`: `-5.000` CONTAINS `-5.00`, so a
        // substring check would pass even if both cells had rendered at the
        // wrong scale. Copilot's catch on #2051.
        assert_eq!(
            data_cells(&mixed, &ctx),
            vec!["-5.00".to_string(), "5.000".to_string()],
            "each cell keeps its own scale",
        );
    }

    /// Render `result` and return the last whitespace-separated token of every
    /// data row — the right-aligned value cell of each.
    ///
    /// Finds the rows by skipping past the `-----` separator rather than
    /// indexing a fixed line, so a change to the header layout cannot silently
    /// point this at the wrong line (or at a header) — Copilot's catch on
    /// #2051. An empty result yields an empty vec, which a caller comparing
    /// against expected cells will fail on loudly.
    fn data_cells(result: &rustledger_query::QueryResult, ctx: &DisplayContext) -> Vec<String> {
        let mut buf: Vec<u8> = Vec::new();
        write_text(result, &mut buf, false, ctx).expect("write_text ok");
        let text = String::from_utf8(buf).expect("utf8");
        text.lines()
            // Past the `-----` separator...
            .skip_while(|l| !l.trim_start().starts_with('-'))
            .skip(1)
            // ...and stop at the blank line before the `N row(s)` footer,
            // which is otherwise picked up as a data row yielding `row(s)`.
            .take_while(|l| !l.trim().is_empty())
            .filter_map(|l| l.split_whitespace().last().map(str::to_string))
            .collect()
    }

    /// The single data cell of a one-row result.
    fn last_cell(result: &rustledger_query::QueryResult, ctx: &DisplayContext) -> String {
        let cells = data_cells(result, ctx);
        assert_eq!(
            cells.len(),
            1,
            "expected exactly one data row, got {cells:?}"
        );
        cells.into_iter().next().expect("checked non-empty")
    }

    // ─── Issue #1023: PIVOT BY currency precision ────────────────────────
    //
    // After PIVOT, the GROUP BY currency moves into column position and
    // each pivoted column's *name* is a currency code. The pivot path
    // uses `add_row` (not `add_aggregate_row`), so the per-row sidecar is
    // `None` for those rows. The renderer needs a column-name fallback
    // to recover the precision context.

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
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-5.00), "USD"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "Refund")
                    .with_flag('*')
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(0.000), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(0.0), "USD"),
                    )),
            ),
        ];

        let mut ctx = DisplayContext::new();
        ctx.update(dec!(5.00), "USD");
        ctx.update(dec!(-5.00), "USD");

        let mut executor = Executor::new(&directives);
        // Two-column PIVOT BY: the first arg is the row key, the second is
        // spread into columns. Here `account` keys the rows and `currency`
        // values (USD) become the pivoted columns.
        let query = parse(
            "SELECT account, currency, SUM(number) \
             GROUP BY account, currency \
             PIVOT BY account, currency",
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

    /// `render_commas` is a property of the TABLE, not of a column's contents:
    /// every column honors it, whatever kind of value it holds (#1892).
    ///
    /// It previously arrived only as a side effect of the Number-column
    /// precision inheritance, so one query printed `SUM(number)` with
    /// separators and `SUM(position)` without them.
    #[test]
    fn render_commas_applies_to_every_column_kind() {
        use rustledger_core::{Amount, Position};
        use rustledger_query::QueryResult;
        let mut ctx = DisplayContext::new();
        ctx.set_render_commas(true);
        ctx.update(rust_decimal_macros::dec!(1234567.89), "USD");

        let mut result = QueryResult::new(vec!["num".into(), "pos".into()]);
        result.add_row(vec![
            Value::Number(rust_decimal_macros::dec!(1234567.89)),
            Value::Position(Box::new(Position::simple(Amount::new(
                rust_decimal_macros::dec!(1234567.89),
                "USD",
            )))),
        ]);

        let mut out = Vec::new();
        write_text(&result, &mut out, false, &ctx).expect("write");
        let text = String::from_utf8(out).expect("utf8");
        assert_eq!(
            text.matches("1,234,567.89").count(),
            2,
            "both the Number and the Position column must carry separators:\n{text}"
        );
    }

    /// `query --format beancount` honors `render_commas`, agreeing with
    /// `rledger format --ledger` on the same ledger (#1896).
    ///
    /// Both emit ledger text, whose reader has a grammar that admits grouped
    /// numerals, so a ledger asking for separators gets them from both. This
    /// arm used to suppress them, which was right while `format` stripped
    /// unconditionally and wrong the moment `format --ledger` learned to
    /// group. Asserted through the SAME surface resolution the dispatcher
    /// performs, so the wiring is covered and not just the writer.
    #[test]
    fn beancount_output_honors_render_commas_like_format() {
        use rustledger_core::OutputSurface;
        use rustledger_query::QueryResult;

        let surface: OutputSurface = super::super::OutputFormat::Beancount.into();
        assert!(
            surface.renders_thousands_separators(),
            "ledger text has a grammar for separators"
        );

        let mut ledger_ctx = DisplayContext::new();
        ledger_ctx.set_render_commas(true);
        ledger_ctx.update(rust_decimal_macros::dec!(1234567.89), "USD");
        let ctx = ledger_ctx.for_surface(surface);

        let mut result = QueryResult::new(vec!["pos".into()]);
        result.add_row(vec![Value::Position(Box::new(
            rustledger_core::Position::simple(rustledger_core::Amount::new(
                rust_decimal_macros::dec!(1234567.89),
                "USD",
            )),
        ))]);

        let mut out = Vec::new();
        write_beancount(&result, &mut out, &ctx).expect("write");
        let text = String::from_utf8(out).expect("utf8");
        assert!(
            text.contains("1,234,567.89 USD"),
            "must group, like `format --ledger` does: {text}"
        );

        // ...and a commodity opting out is still honored on this surface.
        let mut opted_out = DisplayContext::new();
        opted_out.set_render_commas(true);
        opted_out.set_render_commas_for("USD", false);
        opted_out.update(rust_decimal_macros::dec!(1234567.89), "USD");
        let ctx = opted_out.for_surface(surface);
        let mut out = Vec::new();
        write_beancount(&result, &mut out, &ctx).expect("write");
        let text = String::from_utf8(out).expect("utf8");
        assert!(
            text.contains("1234567.89 USD") && !text.contains(','),
            "USD declared render_commas: FALSE: {text}"
        );
    }

    /// A commodity's own `render_commas:` declaration reaches the query
    /// writer, on every column kind.
    ///
    /// The per-column contexts are built fresh and used to inherit only the
    /// ledger-wide flag, so a commodity opting out was grouped anyway (#1896).
    /// `Value::Number` has no currency in scope and necessarily takes the
    /// ledger-wide default — that is why the opted-out commodity is asserted
    /// through the columns that DO carry a currency.
    #[test]
    fn a_commoditys_own_grouping_declaration_reaches_the_query_writer() {
        use rustledger_core::{Amount, Position};
        use rustledger_query::QueryResult;
        let mut ctx = DisplayContext::new();
        ctx.set_render_commas(true);
        ctx.set_render_commas_for("USD", false);
        ctx.update(rust_decimal_macros::dec!(1234567.89), "USD");
        ctx.update(rust_decimal_macros::dec!(1234567.89), "IQD");

        let mut result = QueryResult::new(vec!["amt".into(), "pos".into()]);
        result.add_row(vec![
            Value::Amount(Amount::new(rust_decimal_macros::dec!(1234567.89), "USD")),
            Value::Position(Box::new(Position::simple(Amount::new(
                rust_decimal_macros::dec!(1234567.89),
                "IQD",
            )))),
        ]);

        let mut out = Vec::new();
        write_text(&result, &mut out, false, &ctx).expect("write");
        let text = String::from_utf8(out).expect("utf8");
        assert!(
            text.contains("1234567.89 USD"),
            "USD declared render_commas: FALSE and must not be grouped:\n{text}"
        );
        assert!(
            text.contains("1,234,567.89 IQD"),
            "IQD declared nothing and takes the ledger-wide TRUE:\n{text}"
        );
    }

    /// Machine-readable surfaces must never emit thousands separators, even
    /// when the ledger asks for them (#1892).
    ///
    /// A separator forces the field to be quoted and then breaks ordinary
    /// decimal parsers. Asserted through the SAME surface resolution the
    /// dispatcher performs, so this covers the wiring and not just the
    /// writer: a future format mapped to the wrong `OutputSurface` fails here.
    #[test]
    fn machine_surfaces_never_emit_thousands_separators() {
        use rustledger_core::OutputSurface;
        use rustledger_query::QueryResult;
        let mut ledger_ctx = DisplayContext::new();
        ledger_ctx.set_render_commas(true);
        ledger_ctx.update(rust_decimal_macros::dec!(1234567.89), "USD");

        let mut result = QueryResult::new(vec!["sum".into()]);
        result.add_row(vec![Value::Number(rust_decimal_macros::dec!(1234567.89))]);

        // Beancount is deliberately absent: it is ledger text, whose reader
        // has a grammar for separators, and it groups (#1896). See
        // `beancount_output_honors_render_commas_like_format`.
        for format in [
            super::super::OutputFormat::Csv,
            super::super::OutputFormat::Json,
        ] {
            let surface: OutputSurface = format.into();
            assert!(
                !surface.renders_thousands_separators(),
                "{format:?} is not a human-reading surface"
            );
            let ctx = ledger_ctx.for_surface(surface);

            let mut out = Vec::new();
            write_csv(&result, &mut out, false, &ctx).expect("write");
            let csv = String::from_utf8(out).expect("utf8");
            assert!(
                csv.contains("1234567.89"),
                "{format:?}: value must render unseparated: {csv}"
            );
            assert!(
                !csv.contains("1,234,567.89") && !csv.contains('"'),
                "{format:?}: no separators and therefore no quoting: {csv}"
            );
        }
    }
}
