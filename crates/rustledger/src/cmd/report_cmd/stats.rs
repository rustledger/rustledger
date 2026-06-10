//! Stats report - Show ledger statistics.

use super::LedgerStats;
use anyhow::Result;
use rustledger_core::Directive;
use std::io::Write;
use std::path::PathBuf;

/// Generate ledger statistics.
pub(super) fn report_stats<W: Write>(
    directives: &[Directive],
    file_path: &PathBuf,
    writer: &mut W,
) -> Result<()> {
    let mut stats = LedgerStats::default();

    for directive in directives {
        match directive {
            Directive::Transaction(txn) => {
                // Synthesized P-flag transactions are pad-expanded
                // entries (see `Ledger.directives` rustdoc; #1288).
                // Recognize them via the booking-crate helper, NOT
                // a bare `flag == 'P'` check: `P` is a valid
                // user-written flag in beancount, and conflating
                // user `P`-flag transactions with synth pads
                // would misattribute them in the stats output and
                // suppress their postings count below.
                if rustledger_booking::is_synthesized_pad(txn) {
                    stats.pads += 1;
                    // Synth pads' postings are accounting-internal,
                    // not user-authored. Counting them here would
                    // double-count the same logical activity twice
                    // (once via the pad row, once via the postings
                    // row) and inflate the postings figure on every
                    // padded ledger.
                } else {
                    stats.transactions += 1;
                    stats.postings += txn.postings.len();
                }
                if stats.first_date.is_none() || Some(txn.date) < stats.first_date {
                    stats.first_date = Some(txn.date);
                }
                if stats.last_date.is_none() || Some(txn.date) > stats.last_date {
                    stats.last_date = Some(txn.date);
                }
            }
            Directive::Open(_) => stats.accounts += 1,
            Directive::Balance(_) => stats.balance_assertions += 1,
            Directive::Commodity(_) => stats.commodities += 1,
            Directive::Price(_) => stats.prices += 1,
            // `Directive::Pad(_)` would only fire if a downstream
            // consumer skipped loader-side expansion. The loader
            // now replaces every Pad with a P-flag Transaction
            // (see above), so this arm is dead in the normal
            // pipeline — but keep it for defensive parity in case
            // a future caller hands stats a pre-load directive
            // list.
            Directive::Pad(_) => stats.pads += 1,
            Directive::Event(_) => stats.events += 1,
            Directive::Note(_) => stats.notes += 1,
            Directive::Document(_) => stats.documents += 1,
            Directive::Query(_) => stats.queries += 1,
            Directive::Custom(_) => stats.custom += 1,
            Directive::Close(_) => {}
        }
    }

    writeln!(writer, "Ledger Statistics")?;
    writeln!(writer, "{}", "=".repeat(40))?;
    writeln!(writer)?;
    writeln!(writer, "File: {}", file_path.display())?;
    writeln!(writer)?;
    writeln!(writer, "Date Range:")?;
    if let (Some(first), Some(last)) = (stats.first_date, stats.last_date) {
        writeln!(writer, "  First: {first}")?;
        writeln!(writer, "  Last:  {last}")?;
    }
    writeln!(writer)?;
    writeln!(writer, "Directives:")?;
    writeln!(writer, "  Transactions:       {:>6}", stats.transactions)?;
    writeln!(writer, "  Postings:           {:>6}", stats.postings)?;
    writeln!(writer, "  Accounts:           {:>6}", stats.accounts)?;
    writeln!(writer, "  Commodities:        {:>6}", stats.commodities)?;
    writeln!(
        writer,
        "  Balance Assertions: {:>6}",
        stats.balance_assertions
    )?;
    writeln!(writer, "  Prices:             {:>6}", stats.prices)?;
    writeln!(writer, "  Pads:               {:>6}", stats.pads)?;
    writeln!(writer, "  Events:             {:>6}", stats.events)?;
    writeln!(writer, "  Notes:              {:>6}", stats.notes)?;
    writeln!(writer, "  Documents:          {:>6}", stats.documents)?;
    writeln!(writer, "  Queries:            {:>6}", stats.queries)?;
    writeln!(writer, "  Custom:             {:>6}", stats.custom)?;
    writeln!(writer)?;
    writeln!(writer, "Total Directives:     {:>6}", directives.len())?;

    Ok(())
}
