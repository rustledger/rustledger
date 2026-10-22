//! Balance sheet report - Assets, Liabilities, and Equity.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::{Directive, DisplayContext, Inventory};
use std::collections::BTreeMap;
use std::io::Write;

/// Where the balance sheet books what makes it balance: the ledger's
/// `account_current_earnings` and `account_current_conversions`, resolved
/// under the equity root.
pub(super) struct CapAccounts<'a> {
    pub current_earnings: &'a str,
    pub current_conversions: &'a str,
}

/// Generate a balance sheet report (Assets, Liabilities, Equity).
///
/// The sheet BALANCES: at cost, assets + liabilities + equity is zero. As
/// Fava's balance sheet does (`Tree.cap`), the equity section carries two
/// lines the ledger's own accounts lack: the net income of the period
/// (income and expenses, booked to `account_current_earnings`) and the
/// conversion residual that `@` price conversions leave between currencies
/// (booked to `account_current_conversions`). Each is shown only when it is
/// not zero. Over a date window the period is the window, and the income
/// before it is already in `account_previous_earnings` (the clamp put it
/// there).
pub(super) fn report_balsheet<W: Write>(
    directives: &[Directive],
    booking_method: rustledger_core::BookingMethod,
    account_types: &rustledger_core::AccountTypes,
    cap: &CapAccounts<'_>,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut assets: BTreeMap<rustledger_core::Account, Inventory> = BTreeMap::new();
    let mut liabilities: BTreeMap<rustledger_core::Account, Inventory> = BTreeMap::new();
    let mut equity: BTreeMap<rustledger_core::Account, Inventory> = BTreeMap::new();

    // Partition the single source-of-truth balances (see
    // `super::account_balances`) into the three balance-sheet sections by
    // account prefix. No balance re-derivation here.
    // Route by CONFIGURED account type (honors `name_*` renames — L5: a
    // ledger with `option "name_assets" "Activa"` must still fill the
    // balance sheet), never by hardcoded root prefixes.
    use rustledger_core::AccountTypeKind as K;
    let overflow = |e: rustledger_core::OverflowError| {
        anyhow::anyhow!(
            "the balance sheet's {} total is too large to represent",
            e.currency
        )
    };
    // The period's net income (Fava inserts the Income and the Expenses
    // subtrees into `account_current_earnings`), and every account's balance
    // at cost, whose residual is the conversions line.
    let mut earnings = Inventory::new();
    let mut at_cost = Inventory::new();
    for (account, inv) in super::account_balances(directives, booking_method)? {
        at_cost
            .merge(&inv.at_cost().map_err(overflow)?)
            .map_err(overflow)?;
        let section = match account_types.kind(&account) {
            Some(K::Assets) => &mut assets,
            Some(K::Liabilities) => &mut liabilities,
            Some(K::Equity) => &mut equity,
            Some(K::Income | K::Expenses) => {
                earnings.merge(&inv).map_err(overflow)?;
                continue;
            }
            None => continue,
        };
        section.insert(account, inv);
    }
    let mut conversions = Inventory::new();
    for pos in at_cost.positions() {
        conversions.add(pos.neg()).map_err(overflow)?;
    }
    // Into the configured accounts, adding to whatever the ledger itself
    // booked there (as Fava's `Tree.insert` does).
    for (name, inv) in [
        (cap.current_earnings, earnings),
        (cap.current_conversions, conversions),
    ] {
        if inv.is_empty() {
            continue;
        }
        equity
            .entry(name.into())
            .or_default()
            .merge(&inv)
            .map_err(overflow)?;
    }

    // Helper to sum inventory by currency, keyed by the Currency newtype
    // so the BTreeMap insert path doesn't allocate.
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

    // Collect rows: (section, account, formatted amount, currency)
    fn collect_rows(
        section: &str,
        balances: &BTreeMap<rustledger_core::Account, Inventory>,
        ctx: &DisplayContext,
    ) -> Vec<(String, String, String, String, String)> {
        let mut rows = Vec::new();
        for (account, inventory) in balances {
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
                    section.to_string(),
                    account.to_string(),
                    ctx.format_amount_number(position.units.number, &position.units.currency),
                    position.units.currency.to_string(),
                    cost,
                ));
            }
        }
        rows
    }

    let mut all_rows = Vec::new();
    all_rows.extend(collect_rows("Assets", &assets, ctx));
    all_rows.extend(collect_rows("Liabilities", &liabilities, ctx));
    all_rows.extend(collect_rows("Equity", &equity, ctx));

    // Net worth = Assets - Liabilities
    let asset_totals = sum_by_currency(&assets);
    let liability_totals = sum_by_currency(&liabilities);
    let mut net_worth: BTreeMap<rustledger_core::Currency, Decimal> = asset_totals;
    for (currency, amount) in &liability_totals {
        *net_worth.entry(currency.clone()).or_default() += amount;
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "section,account,amount,currency,cost")?;
            for (section, account, amount, currency, cost) in &all_rows {
                // `csv_escape(amount)`: with `render_commas` the formatted
                // number contains thousands separators (review catch).
                writeln!(
                    writer,
                    "{},{},{},{},{}",
                    section,
                    csv_escape(account),
                    csv_escape(amount),
                    currency,
                    csv_escape(cost)
                )?;
            }
            // Add net worth rows
            for (currency, total) in &net_worth {
                let total = csv_escape(&ctx.format_amount_number(*total, currency));
                // Trailing comma: empty `cost` field keeps the row at the
                // header's five columns (review catch — was four wide).
                writeln!(writer, "Net Worth,TOTAL,{total},{currency},")?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "{{")?;
            writeln!(writer, r#"  "accounts": ["#)?;
            for (i, (section, account, amount, currency, cost)) in all_rows.iter().enumerate() {
                let comma = if i < all_rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"    {{"section": "{}", "account": "{}", "amount": "{}", "currency": "{}", "cost": "{}"}}{}"#,
                    section,
                    json_escape(account),
                    amount,
                    currency,
                    json_escape(cost),
                    comma
                )?;
            }
            writeln!(writer, "  ],")?;
            writeln!(writer, r#"  "net_worth": {{"#)?;
            let nw_vec: Vec<_> = net_worth.iter().collect();
            for (i, (currency, total)) in nw_vec.iter().enumerate() {
                let comma = if i < nw_vec.len() - 1 { "," } else { "" };
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
                        let cost = position
                            .cost
                            .as_ref()
                            .map(|c| format!(" {c}"))
                            .unwrap_or_default();
                        writeln!(
                            writer,
                            "  {:>12} {:>4}{}  {}",
                            ctx.format_amount_number(
                                position.units.number,
                                &position.units.currency
                            ),
                            position.units.currency,
                            cost,
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

            writeln!(writer, "Balance Sheet")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            write_section(writer, "Assets", &assets, ctx)?;
            write_section(writer, "Liabilities", &liabilities, ctx)?;
            write_section(writer, "Equity", &equity, ctx)?;

            writeln!(writer, "Net Worth")?;
            writeln!(writer, "{}", "-".repeat(60))?;
            for (currency, total) in &net_worth {
                let total = ctx.format_amount_number(*total, currency);
                writeln!(writer, "  {total:>12} {currency:>4}")?;
            }
        }
    }

    Ok(())
}
