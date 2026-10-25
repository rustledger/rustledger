//! Journal report - Transaction journal/register.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::{Directive, OverflowError, checked_add_exact};
use std::collections::BTreeMap;
use std::io::Write;

/// A clamp-synthesized opening-balance summary (#2643): what a windowed
/// report shows for the history before the window. The journal sorts these
/// ahead of the window's own same-date rows (they ARE the pre-window history),
/// which is also what makes the running total already carry the balances in
/// when the first real row is read (#2741). Recognized by the flag and
/// narration `clamp` writes; a user-authored row of exactly that shape sorts
/// first too, which costs it nothing but its position.
fn is_opening_summary(txn: &rustledger_core::Transaction) -> bool {
    txn.flag == 'S' && txn.narration.as_str() == "Opening balance"
}

/// The running inventory as `200.00 EUR, -220.00 USD` (#2741): every currency
/// seen, sorted, zero balances dropped (hledger's mixed amount).
fn format_inventory(inventory: &BTreeMap<String, Decimal>) -> String {
    inventory
        .iter()
        .map(|(currency, number)| format!("{number} {currency}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Generate a journal/register report.
///
/// `running` adds the running-balance column (#2741): the mixed inventory of
/// the postings `--account` matched (every posting when there is no filter),
/// shown after each posting. The totals walk the whole report before
/// `--limit` drops rows from the top, so a limited report still shows the
/// total as of each row.
pub(super) fn report_journal<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    limit: Option<usize>,
    format: &OutputFormat,
    running: bool,
    title: &str,
    writer: &mut W,
) -> Result<()> {
    let mut entries: Vec<_> = directives
        .iter()
        .filter_map(|d| {
            if let Directive::Transaction(txn) = d {
                if let Some(filter) = account_filter
                    && !txn.postings.iter().any(|p| p.account.starts_with(filter))
                {
                    return None;
                }
                Some(txn)
            } else {
                None
            }
        })
        .collect();

    // Opening-balance summaries sort first among same-date rows (see
    // [`is_opening_summary`]); otherwise `sort_by_key` is stable and the
    // same-date order stays the order booking itself uses (#2093).
    entries.sort_by_key(|t| (t.date, !is_opening_summary(t)));

    // The running balances (#2741), over the WHOLE report rather than the
    // rows `--limit` keeps: the column is the total as of each row, so a
    // limited register still shows real balances, not a subtotal of its own
    // tail. Only the postings the account filter matched move the total —
    // without a filter that is every posting. Computed only when asked for.
    let mut totals: Vec<Vec<String>> = Vec::new();
    if running {
        let mut inventory: BTreeMap<String, Decimal> = BTreeMap::new();
        for txn in &entries {
            let mut row = Vec::with_capacity(txn.postings.len());
            for posting in &txn.postings {
                if let Some(amount) = posting.amount()
                    && account_filter.is_none_or(|f| posting.account.starts_with(f))
                {
                    let currency = amount.currency.to_string();
                    let total = inventory.entry(currency.clone()).or_default();
                    // `Decimal`'s `+` PANICS past ±7.9e28 and rounds silently
                    // near the digit ceiling; report the overflow like every
                    // other balance path does (see `decimal_overflow_test`).
                    *total =
                        checked_add_exact(*total, amount.number).ok_or_else(|| OverflowError {
                            currency: amount.currency.clone(),
                        })?;
                    if total.is_zero() {
                        inventory.remove(&currency);
                    }
                }
                row.push(format_inventory(&inventory));
            }
            totals.push(row);
        }
    }

    // Take the last N without reversing them. `--limit` means "the most
    // recent N", but reaching them with `.rev().take(n)` left the ROWS
    // reversed too, so adding a limit silently flipped the report from
    // oldest-first to newest-first (#2122). `sort_by_key` is stable, so the
    // same reversal also undid the file order of same-date transactions —
    // the order booking itself uses (#2093), which makes it more than
    // cosmetic. `tail` does not print its lines backwards either.
    let skip = match limit {
        Some(n) => entries.len().saturating_sub(n),
        None => 0,
    };
    let entries_to_show = entries.split_off(skip);
    let totals_to_show = if running {
        totals.split_off(skip)
    } else {
        Vec::new()
    };
    let running_at = |i: usize, j: usize| -> &str {
        totals_to_show
            .get(i)
            .and_then(|row| row.get(j))
            .map_or("", String::as_str)
    };

    match format {
        OutputFormat::Csv => {
            if running {
                writeln!(
                    writer,
                    "date,flag,payee,narration,account,amount,currency,running_total"
                )?;
            } else {
                writeln!(writer, "date,flag,payee,narration,account,amount,currency")?;
            }
            for (i, txn) in entries_to_show.iter().enumerate() {
                let payee = txn.payee.as_deref().unwrap_or("");
                for (j, posting) in txn.postings.iter().enumerate() {
                    let (amount, currency) = if let Some(amt) = posting.amount() {
                        (amt.number.to_string(), amt.currency.to_string())
                    } else {
                        (String::new(), String::new())
                    };
                    // The running total is a mixed amount (`200.00 EUR,
                    // -220.00 USD`), so it carries a comma and is escaped.
                    let running_col = if running {
                        format!(",{}", csv_escape(running_at(i, j)))
                    } else {
                        String::new()
                    };
                    writeln!(
                        writer,
                        "{},{},{},{},{},{},{}{}",
                        txn.date,
                        txn.flag,
                        csv_escape(payee),
                        csv_escape(&txn.narration),
                        csv_escape(&posting.account),
                        amount,
                        currency,
                        running_col
                    )?;
                }
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, txn) in entries_to_show.iter().enumerate() {
                let payee = txn.payee.as_deref().unwrap_or("");
                let comma = if i < entries_to_show.len() - 1 {
                    ","
                } else {
                    ""
                };
                writeln!(writer, "  {{")?;
                writeln!(writer, r#"    "date": "{}","#, txn.date)?;
                writeln!(writer, r#"    "flag": "{}","#, txn.flag)?;
                writeln!(writer, r#"    "payee": "{}","#, json_escape(payee))?;
                writeln!(
                    writer,
                    r#"    "narration": "{}","#,
                    json_escape(&txn.narration)
                )?;
                writeln!(writer, r#"    "postings": ["#)?;
                for (j, posting) in txn.postings.iter().enumerate() {
                    let pcomma = if j < txn.postings.len() - 1 { "," } else { "" };
                    let (amount, currency) = if let Some(amt) = posting.amount() {
                        (amt.number.to_string(), amt.currency.to_string())
                    } else {
                        (String::new(), String::new())
                    };
                    let running_col = if running {
                        format!(r#", "running_total": "{}""#, json_escape(running_at(i, j)))
                    } else {
                        String::new()
                    };
                    writeln!(
                        writer,
                        r#"      {{"account": "{}", "amount": "{}", "currency": "{}"{running_col}}}{}"#,
                        json_escape(&posting.account),
                        amount,
                        currency,
                        pcomma
                    )?;
                }
                writeln!(writer, "    ]")?;
                writeln!(writer, "  }}{comma}")?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "{title}")?;
            writeln!(writer, "{}", "=".repeat(80))?;
            writeln!(writer)?;

            // The currency column widens to the longest one shown, so the
            // running total's `|` lines up down the register.
            let currency_width = entries_to_show
                .iter()
                .flat_map(|t| t.postings.iter())
                .filter_map(|p| p.amount())
                .map(|a| a.currency.to_string().chars().count())
                .max()
                .unwrap_or(3);

            for (i, txn) in entries_to_show.iter().enumerate() {
                let payee = txn.payee.as_ref().map_or("", |p| p.as_str());
                let narration = txn.narration.as_str();
                let desc = if payee.is_empty() {
                    narration.to_string()
                } else {
                    format!("{payee} | {narration}")
                };
                // The ledger's text, shown on a terminal (#2538).
                let desc = super::sanitize_display(&desc);
                writeln!(writer, "{} {} {}", txn.date, txn.flag, desc)?;

                for (j, posting) in txn.postings.iter().enumerate() {
                    if running {
                        let (number, currency) = match posting.amount() {
                            Some(amount) => {
                                (amount.number.to_string(), amount.currency.to_string())
                            }
                            None => (String::new(), String::new()),
                        };
                        // `trim_end`: an empty total would otherwise leave
                        // the separator's trailing space on the line.
                        let line = format!(
                            "  {:50} {:>12} {:<width$} | {}",
                            posting.account.as_str(),
                            number,
                            currency,
                            running_at(i, j),
                            width = currency_width
                        );
                        writeln!(writer, "{}", line.trim_end())?;
                    } else if let Some(amount) = posting.amount() {
                        writeln!(
                            writer,
                            "  {:50} {:>12} {}",
                            posting.account.as_str(),
                            amount.number,
                            amount.currency
                        )?;
                    } else {
                        writeln!(writer, "  {:50}", posting.account.as_str())?;
                    }
                }
                writeln!(writer)?;
            }
        }
    }

    Ok(())
}
