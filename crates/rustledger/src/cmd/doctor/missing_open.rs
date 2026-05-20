use anyhow::{Context, Result};
use rustledger_core::{Account, Directive, NaiveDate};
use rustledger_loader::Loader;
use std::collections::{BTreeMap, HashSet};
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_missing_open<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Collect all accounts that are opened
    let mut opened_accounts: HashSet<Account> = HashSet::new();

    // Collect all accounts that are used and their first use date
    let mut used_accounts: BTreeMap<Account, NaiveDate> = BTreeMap::new();

    for spanned in &load_result.directives {
        match &spanned.value {
            Directive::Open(open) => {
                opened_accounts.insert(open.account.clone());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    used_accounts
                        .entry(posting.account.clone())
                        .or_insert(txn.date);
                }
            }
            Directive::Balance(bal) => {
                used_accounts.entry(bal.account.clone()).or_insert(bal.date);
            }
            Directive::Pad(pad) => {
                used_accounts.entry(pad.account.clone()).or_insert(pad.date);
                used_accounts
                    .entry(pad.source_account.clone())
                    .or_insert(pad.date);
            }
            _ => {}
        }
    }

    // Find accounts that are used but not opened
    let missing: Vec<_> = used_accounts
        .iter()
        .filter(|(account, _)| !opened_accounts.contains(*account))
        .collect();

    if missing.is_empty() {
        writeln!(writer, "; No missing Open directives")?;
    } else {
        writeln!(
            writer,
            "; Missing Open directives ({} accounts)",
            missing.len()
        )?;
        writeln!(writer)?;
        for (account, first_use_date) in missing {
            writeln!(writer, "{first_use_date} open {account}")?;
        }
    }

    Ok(())
}
