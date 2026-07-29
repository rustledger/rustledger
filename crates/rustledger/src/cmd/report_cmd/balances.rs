//! Balances report - Show account balances.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rustledger_core::{Directive, DisplayContext};
use std::io::Write;

/// Generate a balances report.
pub(super) fn report_balances<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // Single source of truth for per-account balances (see
    // `super::account_balances`); no report re-derives them itself.
    let balances = super::account_balances(directives)?;

    // Collect data for output. `cost` is the beancount-style lot annotation
    // (e.g. ` {150.00 USD}`) for held commodities, empty for plain currency.
    // Numbers render through the ledger's DisplayContext (per-currency
    // inferred precision, `display_precision` overrides, `render_commas`)
    // — the same context BQL output uses — so `100 USD` in a 2dp ledger
    // prints as `100.00 USD` regardless of booking-arithmetic scale (U4).
    let mut rows: Vec<(&str, String, &str, String)> = Vec::new();
    for (account, inventory) in &balances {
        if let Some(filter) = account_filter
            && !account.starts_with(filter)
        {
            continue;
        }
        if inventory.is_empty() {
            continue;
        }
        for position in inventory.positions() {
            let cost = position
                .cost
                .as_ref()
                .map(|c| format!("{c}"))
                .unwrap_or_default();
            rows.push((
                account,
                ctx.format_amount_number(position.units.number, &position.units.currency),
                &position.units.currency,
                cost,
            ));
        }
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "account,amount,currency,cost")?;
            for (account, amount, currency, cost) in &rows {
                // `csv_escape(amount)`: with `render_commas` the formatted
                // number contains thousands separators (review catch).
                writeln!(
                    writer,
                    "{},{},{},{}",
                    csv_escape(account),
                    csv_escape(amount),
                    currency,
                    csv_escape(cost)
                )?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, (account, amount, currency, cost)) in rows.iter().enumerate() {
                let comma = if i < rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"  {{"account": "{}", "amount": "{}", "currency": "{}", "cost": "{}"}}{}"#,
                    json_escape(account),
                    amount,
                    currency,
                    json_escape(cost),
                    comma
                )?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Account Balances")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;
            let mut current_account = "";
            for (account, amount, currency, cost) in &rows {
                if *account != current_account {
                    writeln!(writer, "{account}")?;
                    current_account = account;
                }
                if cost.is_empty() {
                    writeln!(writer, "  {amount:>15} {currency}")?;
                } else {
                    writeln!(writer, "  {amount:>15} {currency} {cost}")?;
                }
            }
        }
    }

    Ok(())
}
