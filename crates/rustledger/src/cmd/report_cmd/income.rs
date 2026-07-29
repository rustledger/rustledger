//! Income statement report - Income and Expenses.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::{Directive, DisplayContext, Inventory};
use std::collections::BTreeMap;
use std::io::Write;

/// Generate an income statement report (Income and Expenses).
pub(super) fn report_income<W: Write>(
    directives: &[Directive],
    account_types: &rustledger_core::AccountTypes,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut income: BTreeMap<rustledger_core::Account, Inventory> = BTreeMap::new();
    let mut expenses: BTreeMap<rustledger_core::Account, Inventory> = BTreeMap::new();

    // Partition the single source-of-truth balances (see
    // `super::account_balances`) into income and expense sections by prefix.
    // No balance re-derivation here.
    // Route by CONFIGURED account type (honors `name_*` renames — L5: a
    // ledger with `option "name_income" "Revenue"` previously rendered an
    // EMPTY income statement here).
    use rustledger_core::AccountTypeKind as K;
    for (account, inv) in super::account_balances(directives)? {
        let section = match account_types.kind(&account) {
            Some(K::Income) => &mut income,
            Some(K::Expenses) => &mut expenses,
            _ => continue,
        };
        section.insert(account, inv);
    }

    fn sum_by_currency(
        balances: &BTreeMap<rustledger_core::Account, Inventory>,
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
        balances: &BTreeMap<rustledger_core::Account, Inventory>,
        ctx: &DisplayContext,
    ) -> Vec<(String, String, String, String)> {
        let mut rows = Vec::new();
        for (account, inventory) in balances {
            if inventory.is_empty() {
                continue;
            }
            for position in inventory.positions() {
                rows.push((
                    section.to_string(),
                    account.to_string(),
                    ctx.format_amount_number(position.units.number, &position.units.currency),
                    position.units.currency.to_string(),
                ));
            }
        }
        rows
    }

    let mut all_rows = Vec::new();
    all_rows.extend(collect_rows("Income", &income, ctx));
    all_rows.extend(collect_rows("Expenses", &expenses, ctx));

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
                // `csv_escape(amount)`: with `render_commas` the formatted
                // number contains thousands separators (review catch).
                writeln!(
                    writer,
                    "{},{},{},{}",
                    section,
                    csv_escape(account),
                    csv_escape(amount),
                    currency
                )?;
            }
            for (currency, total) in &net_income {
                let total = csv_escape(&ctx.format_amount_number(*total, currency));
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
                let total = ctx.format_amount_number(**total, currency);
                writeln!(writer, r#"    "{currency}": "{total}"{comma}"#)?;
            }
            writeln!(writer, "  }}")?;
            writeln!(writer, "}}")?;
        }
        OutputFormat::Text => {
            fn write_section<W: Write>(
                writer: &mut W,
                title: &str,
                balances: &BTreeMap<rustledger_core::Account, Inventory>,
                ctx: &DisplayContext,
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
                            ctx.format_amount_number(
                                position.units.number,
                                &position.units.currency
                            ),
                            position.units.currency,
                            account
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
                    let total = ctx.format_amount_number(*total, currency);
                    writeln!(writer, "  {total:>12} {currency:>4}  Total {title}")?;
                }
                writeln!(writer)?;
                Ok(totals)
            }

            writeln!(writer, "Income Statement")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            write_section(writer, "Income", &income, ctx)?;
            write_section(writer, "Expenses", &expenses, ctx)?;

            writeln!(writer, "Net Income")?;
            writeln!(writer, "{}", "-".repeat(60))?;
            for (currency, total) in &net_income {
                let total = ctx.format_amount_number(*total, currency);
                writeln!(writer, "  {total:>12} {currency:>4}")?;
            }
        }
    }

    Ok(())
}
