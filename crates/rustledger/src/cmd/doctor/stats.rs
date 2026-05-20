use anyhow::{Context, Result};
use rustledger_core::{Currency, Directive, NaiveDate};
use rustledger_loader::Loader;
use std::collections::BTreeSet;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_stats<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let mut transactions = 0;
    let mut postings = 0;
    let mut accounts = 0;
    let mut commodities_set: BTreeSet<Currency> = BTreeSet::new();
    let mut balance_assertions = 0;
    let mut prices = 0;
    let mut first_date: Option<NaiveDate> = None;
    let mut last_date: Option<NaiveDate> = None;

    for spanned in &load_result.directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                transactions += 1;
                postings += txn.postings.len();
                for posting in &txn.postings {
                    if let Some(amount) = posting.amount() {
                        commodities_set.insert(amount.currency.clone());
                    }
                }
                if first_date.is_none() || Some(txn.date) < first_date {
                    first_date = Some(txn.date);
                }
                if last_date.is_none() || Some(txn.date) > last_date {
                    last_date = Some(txn.date);
                }
            }
            Directive::Open(_) => accounts += 1,
            Directive::Balance(bal) => {
                balance_assertions += 1;
                commodities_set.insert(bal.amount.currency.clone());
            }
            Directive::Commodity(comm) => {
                commodities_set.insert(comm.currency.clone());
            }
            Directive::Price(price) => {
                prices += 1;
                commodities_set.insert(price.currency.clone());
                commodities_set.insert(price.amount.currency.clone());
            }
            _ => {}
        }
    }

    writeln!(writer, "Ledger Statistics for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    if let (Some(first), Some(last)) = (first_date, last_date) {
        writeln!(writer, "Date range: {first} to {last}")?;
        writeln!(writer)?;
    }

    writeln!(
        writer,
        "Directives:       {:>8}",
        load_result.directives.len()
    )?;
    writeln!(writer, "  Transactions:   {transactions:>8}")?;
    writeln!(writer, "  Postings:       {postings:>8}")?;
    writeln!(writer, "  Accounts:       {accounts:>8}")?;
    writeln!(writer, "  Commodities:    {:>8}", commodities_set.len())?;
    writeln!(writer, "  Balances:       {balance_assertions:>8}")?;
    writeln!(writer, "  Prices:         {prices:>8}")?;
    writeln!(writer)?;
    writeln!(writer, "Parse errors:     {:>8}", load_result.errors.len())?;

    Ok(())
}
