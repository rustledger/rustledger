//! Income statement report - Income and Expenses.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::{Directive, InternedStr, Inventory};
use std::collections::BTreeMap;
use std::io::Write;

/// Generate an income statement report (Income and Expenses).
pub(super) fn report_income<W: Write>(
    directives: &[Directive],
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut income: BTreeMap<InternedStr, Inventory> = BTreeMap::new();
    let mut expenses: BTreeMap<InternedStr, Inventory> = BTreeMap::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                if let Some(amount) = posting.amount() {
                    let account_str: &str = &posting.account;
                    let balances = if account_str.starts_with("Income:") {
                        &mut income
                    } else if account_str.starts_with("Expenses:") {
                        &mut expenses
                    } else {
                        continue;
                    };

                    let inv = balances.entry(posting.account.clone()).or_default();
                    let position = rustledger_core::Position::simple(amount.clone());
                    inv.add(position);
                }
            }
        }
    }

    fn sum_by_currency(
        balances: &BTreeMap<InternedStr, Inventory>,
    ) -> BTreeMap<rustledger_core::Currency, Decimal> {
        let mut totals: BTreeMap<rustledger_core::Currency, Decimal> = BTreeMap::new();
        for inv in balances.values() {
            for pos in inv.positions() {
                *totals.entry(pos.units.currency.clone()).or_default() += pos.units.number;
            }
        }
        totals
    }

    fn collect_rows(
        section: &str,
        balances: &BTreeMap<InternedStr, Inventory>,
    ) -> Vec<(String, String, Decimal, String)> {
        let mut rows = Vec::new();
        for (account, inventory) in balances {
            if inventory.is_empty() {
                continue;
            }
            for position in inventory.positions() {
                rows.push((
                    section.to_string(),
                    account.to_string(),
                    position.units.number,
                    position.units.currency.to_string(),
                ));
            }
        }
        rows
    }

    let mut all_rows = Vec::new();
    all_rows.extend(collect_rows("Income", &income));
    all_rows.extend(collect_rows("Expenses", &expenses));

    // Net income = -(Income) - Expenses (income is negative in double-entry)
    let income_totals = sum_by_currency(&income);
    let expense_totals = sum_by_currency(&expenses);
    let mut net_income: BTreeMap<rustledger_core::Currency, Decimal> = BTreeMap::new();
    for (currency, amount) in &income_totals {
        *net_income.entry(currency.clone()).or_default() -= amount;
    }
    for (currency, amount) in &expense_totals {
        *net_income.entry(currency.clone()).or_default() -= amount;
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "section,account,amount,currency")?;
            for (section, account, amount, currency) in &all_rows {
                writeln!(
                    writer,
                    "{},{},{},{}",
                    section,
                    csv_escape(account),
                    amount,
                    currency
                )?;
            }
            for (currency, total) in &net_income {
                writeln!(writer, "Net Income,TOTAL,{total},{currency}")?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "{{")?;
            writeln!(writer, r#"  "accounts": ["#)?;
            for (i, (section, account, amount, currency)) in all_rows.iter().enumerate() {
                let comma = if i < all_rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"    {{"section": "{}", "account": "{}", "amount": "{}", "currency": "{}"}}{}"#,
                    section,
                    json_escape(account),
                    amount,
                    currency,
                    comma
                )?;
            }
            writeln!(writer, "  ],")?;
            writeln!(writer, r#"  "net_income": {{"#)?;
            let ni_vec: Vec<_> = net_income.iter().collect();
            for (i, (currency, total)) in ni_vec.iter().enumerate() {
                let comma = if i < ni_vec.len() - 1 { "," } else { "" };
                writeln!(writer, r#"    "{currency}": "{total}"{comma}"#)?;
            }
            writeln!(writer, "  }}")?;
            writeln!(writer, "}}")?;
        }
        OutputFormat::Text => {
            fn write_section<W: Write>(
                writer: &mut W,
                title: &str,
                balances: &BTreeMap<InternedStr, Inventory>,
            ) -> Result<BTreeMap<rustledger_core::Currency, Decimal>> {
                writeln!(writer, "{title}")?;
                writeln!(writer, "{}", "-".repeat(60))?;
                for (account, inventory) in balances {
                    if inventory.is_empty() {
                        continue;
                    }
                    for position in inventory.positions() {
                        writeln!(
                            writer,
                            "  {:>12} {:>4}  {}",
                            position.units.number, position.units.currency, account
                        )?;
                    }
                }
                let mut totals: BTreeMap<rustledger_core::Currency, Decimal> = BTreeMap::new();
                for inv in balances.values() {
                    for pos in inv.positions() {
                        *totals.entry(pos.units.currency.clone()).or_default() += pos.units.number;
                    }
                }
                writeln!(writer)?;
                for (currency, total) in &totals {
                    writeln!(writer, "  {total:>12} {currency:>4}  Total {title}")?;
                }
                writeln!(writer)?;
                Ok(totals)
            }

            writeln!(writer, "Income Statement")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            write_section(writer, "Income", &income)?;
            write_section(writer, "Expenses", &expenses)?;

            writeln!(writer, "Net Income")?;
            writeln!(writer, "{}", "-".repeat(60))?;
            for (currency, total) in &net_income {
                writeln!(writer, "  {total:>12} {currency:>4}")?;
            }
        }
    }

    Ok(())
}
