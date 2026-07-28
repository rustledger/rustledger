//! Net worth report - Net worth over time.

use super::{OutputFormat, csv_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::Directive;
use std::collections::BTreeMap;
use std::io::Write;

/// Generate a net worth over time report.
///
/// # Arguments
/// * `directives` - The ledger directives
/// * `period` - Grouping period (daily, weekly, monthly, yearly)
/// * `currency_filter` - Optional currency to filter to (e.g., "USD")
/// * `account_filter` - Optional account prefix to filter to (e.g., "Assets:Investments")
/// * `no_zero` - If true, hide zero balances from output
/// * `format` - Output format (text, csv, json)
/// * `writer` - Output writer
// Nine parameters: the report's five filters/knobs plus the four
// threading params every balance report takes (directives, account
// types, display context, writer). Bundling them into a struct would
// obscure the call site more than it helps — allowed deliberately.
#[allow(clippy::too_many_arguments)]
pub(super) fn report_networth<W: Write>(
    directives: &[Directive],
    account_types: &rustledger_core::AccountTypes,
    ctx: &rustledger_core::DisplayContext,
    period: &str,
    currency_filter: Option<&str>,
    account_filter: Option<&str>,
    no_zero: bool,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut transactions: Vec<_> = directives
        .iter()
        .filter_map(|d| {
            if let Directive::Transaction(txn) = d {
                Some(txn)
            } else {
                None
            }
        })
        .collect();

    transactions.sort_by_key(|t| t.date);

    if transactions.is_empty() {
        match format {
            OutputFormat::Csv => writeln!(writer, "period,currency,amount")?,
            OutputFormat::Json => writeln!(writer, "[]")?,
            OutputFormat::Text => writeln!(writer, "No transactions found.")?,
        }
        return Ok(());
    }

    let mut asset_balance: BTreeMap<rustledger_core::Currency, Decimal> = BTreeMap::new();
    let mut liability_balance: BTreeMap<rustledger_core::Currency, Decimal> = BTreeMap::new();
    let mut period_results: Vec<(String, BTreeMap<rustledger_core::Currency, Decimal>)> =
        Vec::new();

    let format_period = |date: rustledger_core::NaiveDate, period: &str| -> String {
        match period {
            "daily" => date.to_string(),
            // Bucket by the ISO week's Monday, then label from THAT date.
            //
            // Two bugs lived in the previous spelling. It paired the ISO week
            // number (`%V`) with the CALENDAR year, and those disagree across a
            // year boundary: 2024-12-31 is ISO 2025-W01 but was labeled
            // `2024-W01`, colliding with the real 2024-W01 and silently summing
            // two different weeks into one row (#1864). And it went through
            // `format(...).unwrap_or_default().parse().unwrap_or(0)` — two
            // silent fallbacks, either of which would have labeled every row
            // `W00` and collapsed the whole report into a single bucket.
            //
            // `CalendarPeriod::Week` is the shared definition of "which week is
            // this", already used by BQL's `DATE_TRUNC('WEEK', ...)`. Deriving
            // both the bucket and its label from one `start_of` makes them
            // agree by construction rather than by coincidence.
            "weekly" => {
                let start = rustledger_core::CalendarPeriod::Week.start_of(date);
                let iso = start.iso_week_date();
                format!("{}-W{:02}", iso.year(), iso.week())
            }
            "yearly" => format!("{}", date.year()),
            _ => format!("{}-{:02}", date.year(), date.month()),
        }
    };

    // Helper to check if an account matches the filter
    let account_matches = |account: &str| -> bool {
        match account_filter {
            Some(filter) => account.starts_with(filter),
            None => true,
        }
    };

    let mut current_period = String::new();

    for txn in transactions {
        let txn_period = format_period(txn.date, period);

        if txn_period != current_period && !current_period.is_empty() {
            let mut net_worth: BTreeMap<rustledger_core::Currency, Decimal> = asset_balance.clone();
            for (currency, amount) in &liability_balance {
                *net_worth.entry(currency.clone()).or_default() += amount;
            }
            period_results.push((current_period.clone(), net_worth));
        }
        current_period = txn_period;

        for posting in &txn.postings {
            if let Some(amount) = posting.amount() {
                let account_str: &str = &posting.account;

                // Apply currency filter if specified
                if let Some(curr_filter) = currency_filter {
                    let currency_str: &str = &amount.currency;
                    if !currency_str.eq_ignore_ascii_case(curr_filter) {
                        continue;
                    }
                }

                // Configured roots, not hardcoded prefixes (L5).
                use rustledger_core::AccountTypeKind as K;
                if account_types.kind(account_str) == Some(K::Assets)
                    && account_matches(account_str)
                {
                    *asset_balance.entry(amount.currency.clone()).or_default() += amount.number;
                } else if account_types.kind(account_str) == Some(K::Liabilities)
                    && account_matches(account_str)
                {
                    *liability_balance
                        .entry(amount.currency.clone())
                        .or_default() += amount.number;
                }
            }
        }
    }

    if !current_period.is_empty() {
        let mut net_worth: BTreeMap<rustledger_core::Currency, Decimal> = asset_balance.clone();
        for (currency, amount) in &liability_balance {
            *net_worth.entry(currency.clone()).or_default() += amount;
        }
        period_results.push((current_period, net_worth));
    }

    // Apply no_zero filter if requested
    if no_zero {
        for (_, net_worth) in &mut period_results {
            net_worth.retain(|_, amount| !amount.is_zero());
        }
        // Also remove periods with no remaining currencies
        period_results.retain(|(_, net_worth)| !net_worth.is_empty());
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "period,currency,amount")?;
            for (period_label, net_worth) in &period_results {
                for (currency, amount) in net_worth {
                    // Escaped: `render_commas` puts separators in the number
                    // (review catch).
                    let amount = csv_escape(&ctx.format_amount_number(*amount, currency));
                    writeln!(writer, "{period_label},{currency},{amount}")?;
                }
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            let total_entries: usize = period_results.iter().map(|(_, nw)| nw.len()).sum();
            let mut entry_idx = 0;
            for (period_label, net_worth) in &period_results {
                for (currency, amount) in net_worth {
                    entry_idx += 1;
                    let comma = if entry_idx < total_entries { "," } else { "" };
                    let amount = ctx.format_amount_number(*amount, currency);
                    writeln!(
                        writer,
                        r#"  {{"period": "{period_label}", "currency": "{currency}", "amount": "{amount}"}}{comma}"#
                    )?;
                }
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Net Worth Over Time ({period})")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            for (period_label, net_worth) in &period_results {
                write!(writer, "{period_label:12}")?;
                for (currency, amount) in net_worth {
                    let amount = ctx.format_amount_number(*amount, currency);
                    write!(writer, "  {amount:>12} {currency}")?;
                }
                writeln!(writer)?;
            }
        }
    }

    Ok(())
}
