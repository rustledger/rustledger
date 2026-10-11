//! Balances report - Show account balances.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rustledger_core::{Directive, DisplayContext};
use std::io::Write;

/// Generate a balances report.
pub(super) fn report_balances<W: Write>(
    directives: &[Directive],
    booking_method: rustledger_core::BookingMethod,
    account_filter: Option<&str>,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // Single source of truth for per-account balances (see
    // `super::account_balances`); no report re-derives them itself.
    let balances = super::account_balances(directives, booking_method)?;

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
                .map(|c| format_cost(c, ctx))
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

/// A lot's cost annotation, `{ 166.67 USD, 2024-01-02, "label"}`, with the
/// per-unit cost rendered through the ledger's display context as every
/// other number in the report is.
///
/// `Cost`'s `Display` prints the number at full `Decimal` precision, so an
/// AVERAGE pool's per-unit cost, 500/3, came out as
/// `166.66666666666666666666666667 USD` where BQL renders the same pool as
/// `167 USD` (#2543). The pool keeps its exact total; only the display rounds.
fn format_cost(cost: &rustledger_core::Cost, ctx: &DisplayContext) -> String {
    let date = cost.date.map(|d| format!(", {d}")).unwrap_or_default();
    let label = cost
        .label
        .as_ref()
        .map(|l| format!(", \"{}\"", rustledger_core::format::escape_string(l)))
        .unwrap_or_default();
    format!(
        "{{ {} {}{date}{label}}}",
        ctx.format_amount_number(cost.number, &cost.currency),
        cost.currency
    )
}
