//! Balance sheet report - Assets, Liabilities, and Equity.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::{Directive, InternedStr, Inventory};
use std::collections::BTreeMap;
use std::io::Write;

/// Generate a balance sheet report (Assets, Liabilities, Equity).
pub(super) fn report_balsheet<W: Write>(
    directives: &[Directive],
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut assets: BTreeMap<InternedStr, Inventory> = BTreeMap::new();
    let mut liabilities: BTreeMap<InternedStr, Inventory> = BTreeMap::new();
    let mut equity: BTreeMap<InternedStr, Inventory> = BTreeMap::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                if let Some(amount) = posting.amount() {
                    let account_str: &str = &posting.account;
                    let balances = if account_str.starts_with("Assets:") {
                        &mut assets
                    } else if account_str.starts_with("Liabilities:") {
                        &mut liabilities
                    } else if account_str.starts_with("Equity:") {
                        &mut equity
                    } else {
                        continue;
                    };

                    let inv = balances.entry(posting.account.clone()).or_default();
                    let position = if let Some(cost_spec) = &posting.cost {
                        if let Some(cost) = cost_spec.resolve(amount.number, txn.date) {
                            rustledger_core::Position::with_cost(amount.clone(), cost)
                        } else {
                            rustledger_core::Position::simple(amount.clone())
                        }
                    } else {
                        rustledger_core::Position::simple(amount.clone())
                    };
                    inv.add(position);
                }
            }
        }
    }

    // Helper to sum inventory by currency (uses InternedStr to avoid allocations)
    fn sum_by_currency(
        balances: &BTreeMap<InternedStr, Inventory>,
    ) -> BTreeMap<InternedStr, Decimal> {
        let mut totals: BTreeMap<InternedStr, Decimal> = BTreeMap::new();
        for inv in balances.values() {
            for pos in inv.positions() {
                *totals.entry(pos.units.currency.clone()).or_default() += pos.units.number;
            }
        }
        totals
    }

    // Collect rows: (section, account, amount, currency)
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
    all_rows.extend(collect_rows("Assets", &assets));
    all_rows.extend(collect_rows("Liabilities", &liabilities));
    all_rows.extend(collect_rows("Equity", &equity));

    // Net worth = Assets - Liabilities
    let asset_totals = sum_by_currency(&assets);
    let liability_totals = sum_by_currency(&liabilities);
    let mut net_worth: BTreeMap<InternedStr, Decimal> = asset_totals;
    for (currency, amount) in &liability_totals {
        *net_worth.entry(currency.clone()).or_default() += amount;
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
            // Add net worth rows
            for (currency, total) in &net_worth {
                writeln!(writer, "Net Worth,TOTAL,{total},{currency}")?;
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
            writeln!(writer, r#"  "net_worth": {{"#)?;
            let nw_vec: Vec<_> = net_worth.iter().collect();
            for (i, (currency, total)) in nw_vec.iter().enumerate() {
                let comma = if i < nw_vec.len() - 1 { "," } else { "" };
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
            ) -> Result<BTreeMap<InternedStr, Decimal>> {
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
                let mut totals: BTreeMap<InternedStr, Decimal> = BTreeMap::new();
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

            writeln!(writer, "Balance Sheet")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            write_section(writer, "Assets", &assets)?;
            write_section(writer, "Liabilities", &liabilities)?;
            write_section(writer, "Equity", &equity)?;

            writeln!(writer, "Net Worth")?;
            writeln!(writer, "{}", "-".repeat(60))?;
            for (currency, total) in &net_worth {
                writeln!(writer, "  {total:>12} {currency:>4}")?;
            }
        }
    }

    Ok(())
}
