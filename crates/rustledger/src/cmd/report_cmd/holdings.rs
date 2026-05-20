//! Holdings report - Investment holdings with cost basis.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::Directive;
use std::collections::BTreeMap;
use std::io::Write;

/// Generate a holdings report with cost basis.
pub(super) fn report_holdings<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // Track holdings: account -> currency -> (units, cost_basis, cost_currency)
    let mut holdings: BTreeMap<
        rustledger_core::Account,
        BTreeMap<String, (Decimal, Decimal, String)>,
    > = BTreeMap::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                if let Some(filter) = account_filter
                    && !posting.account.starts_with(filter)
                {
                    continue;
                }

                let account_str: &str = &posting.account;
                if !account_str.starts_with("Assets:") {
                    continue;
                }

                if let Some(amount) = posting.amount() {
                    let account_holdings = holdings.entry(posting.account.clone()).or_default();

                    let (cost_amount, cost_currency) = if let Some(cost_spec) = &posting.cost {
                        if let Some(cost) = cost_spec.resolve(amount.number, txn.date) {
                            (cost.number * amount.number, cost.currency.to_string())
                        } else {
                            (amount.number, amount.currency.to_string())
                        }
                    } else {
                        (amount.number, amount.currency.to_string())
                    };

                    let entry = account_holdings
                        .entry(amount.currency.to_string())
                        .or_insert((Decimal::ZERO, Decimal::ZERO, cost_currency.clone()));

                    entry.0 += amount.number;
                    entry.1 += cost_amount;
                }
            }
        }
    }

    // Collect rows: (account, units, currency, cost_basis, cost_currency)
    let mut rows: Vec<(String, Decimal, String, Decimal, String)> = Vec::new();
    for (account, currencies) in &holdings {
        for (currency, (units, cost_basis, cost_currency)) in currencies {
            if *units == Decimal::ZERO {
                continue;
            }
            rows.push((
                account.to_string(),
                *units,
                currency.clone(),
                *cost_basis,
                cost_currency.clone(),
            ));
        }
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "account,units,currency,cost_basis,cost_currency")?;
            for (account, units, currency, cost_basis, cost_currency) in &rows {
                writeln!(
                    writer,
                    "{},{},{},{},{}",
                    csv_escape(account),
                    units,
                    currency,
                    cost_basis,
                    cost_currency
                )?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, (account, units, currency, cost_basis, cost_currency)) in
                rows.iter().enumerate()
            {
                let comma = if i < rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"  {{"account": "{}", "units": "{}", "currency": "{}", "cost_basis": "{}", "cost_currency": "{}"}}{}"#,
                    json_escape(account),
                    units,
                    currency,
                    cost_basis,
                    cost_currency,
                    comma
                )?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Holdings")?;
            writeln!(writer, "{}", "=".repeat(80))?;
            writeln!(writer)?;
            writeln!(
                writer,
                "{:50} {:>12} {:>6} {:>12} {:>6}",
                "Account", "Units", "Curr", "Cost Basis", "Curr"
            )?;
            writeln!(writer, "{}", "-".repeat(80))?;

            for (account, units, currency, cost_basis, cost_currency) in &rows {
                writeln!(
                    writer,
                    "{account:50} {units:>12} {currency:>6} {cost_basis:>12} {cost_currency:>6}"
                )?;
            }
        }
    }

    Ok(())
}
