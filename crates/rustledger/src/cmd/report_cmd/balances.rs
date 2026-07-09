//! Balances report - Show account balances.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::Directive;
use std::io::Write;

/// Generate a balances report.
pub(super) fn report_balances<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // Single source of truth for per-account balances (see
    // `super::account_balances`); no report re-derives them itself.
    let balances = super::account_balances(directives);

    // Collect data for output
    let mut rows: Vec<(&str, Decimal, &str)> = Vec::new();
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
            rows.push((account, position.units.number, &position.units.currency));
        }
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "account,amount,currency")?;
            for (account, amount, currency) in &rows {
                writeln!(writer, "{},{},{}", csv_escape(account), amount, currency)?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, (account, amount, currency)) in rows.iter().enumerate() {
                let comma = if i < rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"  {{"account": "{}", "amount": "{}", "currency": "{}"}}{}"#,
                    json_escape(account),
                    amount,
                    currency,
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
            for (account, amount, currency) in &rows {
                if *account != current_account {
                    writeln!(writer, "{account}")?;
                    current_account = account;
                }
                writeln!(writer, "  {amount:>15} {currency}")?;
            }
        }
    }

    Ok(())
}
