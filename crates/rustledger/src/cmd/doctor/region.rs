use super::Conversion;
use anyhow::{Context, Result};
use rust_decimal;
use rustledger_core::Directive;
use rustledger_loader::Loader;
use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_region<W: Write>(
    file: &PathBuf,
    start_line: usize,
    end_line: usize,
    conversion: Option<Conversion>,
    writer: &mut W,
) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let conversion_str = match conversion {
        Some(Conversion::Value) => " (converted to value)",
        Some(Conversion::Cost) => " (converted to cost)",
        None => "",
    };
    writeln!(
        writer,
        "Transactions in region {}:{}-{}{}",
        file.display(),
        start_line,
        end_line,
        conversion_str
    )?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Get the source file for line number conversion
    let source_file = load_result.source_map.get(0);

    // Find transactions in the line range
    let mut region_transactions: Vec<&rustledger_core::Transaction> = Vec::new();

    for spanned in &load_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            // Convert byte offset to line number using source map
            let txn_line = match source_file {
                Some(sf) => sf.line_col(spanned.span.start).0,
                None => continue,
            };

            // Check if transaction line falls within the requested range
            if txn_line >= start_line && txn_line <= end_line {
                region_transactions.push(txn);
            }
        }
    }

    if region_transactions.is_empty() {
        writeln!(
            writer,
            "No transactions found in lines {start_line}-{end_line}"
        )?;
        return Ok(());
    }

    writeln!(
        writer,
        "Found {} transaction(s):",
        region_transactions.len()
    )?;
    writeln!(writer)?;

    // Calculate balances for these transactions
    let mut balances: BTreeMap<String, rust_decimal::Decimal> = BTreeMap::new();

    for txn in &region_transactions {
        writeln!(writer, "{} {} \"{}\"", txn.date, txn.flag, txn.narration)?;
        for posting in &txn.postings {
            if let Some(amount) = posting.amount() {
                // Apply conversion if specified
                let (display_number, display_currency) = match conversion {
                    Some(Conversion::Cost) => {
                        // Use cost if available, otherwise fall back to units
                        if let Some(ref cost) = posting.cost {
                            // Calculate total cost from cost spec. The
                            // post-#1164 `CostNumber` enum keeps the
                            // original total when booking derives a
                            // per-unit (`PerUnitFromTotal`), so the
                            // `total()` accessor is preferred here for
                            // precision; the `PerUnit` fallback
                            // multiplies by units, matching the pre-
                            // #1164 branch order (total → per-unit →
                            // none).
                            let total_cost = if let Some(total) = cost
                                .number
                                .as_ref()
                                .and_then(rustledger_core::CostNumber::total)
                            {
                                total
                            } else if let Some(per_unit) = cost
                                .number
                                .as_ref()
                                .and_then(rustledger_core::CostNumber::per_unit)
                            {
                                amount.number * per_unit
                            } else {
                                amount.number
                            };
                            let currency = cost
                                .currency
                                .clone()
                                .unwrap_or_else(|| amount.currency.clone());
                            (total_cost, currency)
                        } else {
                            (amount.number, amount.currency.clone())
                        }
                    }
                    Some(Conversion::Value) => {
                        // For value conversion, we would need a price database
                        // For now, just show a note and use the original values
                        writeln!(
                            writer,
                            "  (Note: value conversion requires price database, showing units)"
                        )?;
                        (amount.number, amount.currency.clone())
                    }
                    None => (amount.number, amount.currency.clone()),
                };
                writeln!(
                    writer,
                    "  {} {} {}",
                    posting.account, display_number, display_currency
                )?;
                *balances
                    .entry(format!("{}:{}", posting.account, display_currency))
                    .or_default() += display_number;
            } else {
                writeln!(writer, "  {}", posting.account)?;
            }
        }
        writeln!(writer)?;
    }

    // Print net balances
    writeln!(writer, "Net changes{conversion_str}:")?;
    for (key, balance) in &balances {
        if !balance.is_zero() {
            writeln!(writer, "  {key}: {balance}")?;
        }
    }

    Ok(())
}
