use anyhow::{Context, Result};
use rustledger_core::Directive;
use rustledger_loader::Loader;
use std::collections::HashSet;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_linked<W: Write>(file: &PathBuf, location: &str, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let directives: Vec<_> = load_result.directives.iter().map(|s| &s.value).collect();

    let linked: Vec<_> = if let Some(link_name) = location.strip_prefix('^') {
        // Link name
        directives
            .iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    txn.links.iter().any(|l| l.as_str() == link_name)
                } else {
                    false
                }
            })
            .copied()
            .collect()
    } else if let Some(tag_name) = location.strip_prefix('#') {
        // Tag name
        directives
            .iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    txn.tags.iter().any(|t| t.as_str() == tag_name)
                } else {
                    false
                }
            })
            .copied()
            .collect()
    } else {
        // Line number - find transaction and its links
        let line: usize = location
            .parse()
            .with_context(|| format!("invalid line number: {location}"))?;

        // Find the transaction at this line, then find all linked transactions
        let mut links_to_find: HashSet<String> = HashSet::new();

        for spanned in &load_result.directives {
            if spanned.span.start <= line
                && spanned.span.end >= line
                && let Directive::Transaction(txn) = &spanned.value
            {
                links_to_find.extend(txn.links.iter().map(ToString::to_string));
            }
        }

        if links_to_find.is_empty() {
            writeln!(writer, "No transaction found at line {line}")?;
            return Ok(());
        }

        directives
            .iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    txn.links.iter().any(|l| links_to_find.contains(l.as_str()))
                } else {
                    false
                }
            })
            .copied()
            .collect()
    };

    writeln!(writer, "Found {} linked entries:", linked.len())?;
    writeln!(writer, "{}", "=".repeat(60))?;

    for directive in linked {
        if let Directive::Transaction(txn) = directive {
            writeln!(writer)?;
            // One line: a newline in the narration is escaped too
            // (#2714); the doctor's writer escapes the other controls.
            writeln!(
                writer,
                "{} {} \"{}\"",
                txn.date,
                txn.flag,
                rustledger_plugin::escape_untrusted_line(&txn.narration)
            )?;
            if !txn.links.is_empty() {
                writeln!(
                    writer,
                    "  Links: {}",
                    txn.links
                        .iter()
                        .map(|l| format!("^{l}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                )?;
            }
            for posting in &txn.postings {
                if let Some(amount) = posting.amount() {
                    writeln!(
                        writer,
                        "  {} {} {}",
                        posting.account, amount.number, amount.currency
                    )?;
                } else {
                    writeln!(writer, "  {}", posting.account)?;
                }
            }
        }
    }

    Ok(())
}
