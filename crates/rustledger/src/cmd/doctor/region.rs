use super::Conversion;
use anyhow::{Context, Result};
use rust_decimal;
use rustledger_core::Directive;
use rustledger_loader::Loader;
use std::collections::BTreeMap;
use std::fmt;
use std::io::Write;
use std::path::PathBuf;

/// A number this command prints: a `Decimal` while one holds it exactly, the
/// exact `BigDecimal` once none does (#2572).
///
/// A lot's cost total, `units × per-unit`, and the running net of a region
/// both leave `Decimal`'s range on ledgers well inside it, and a bare `*` or
/// `+=` there panicked. A clamped or rounded figure would be worse: this
/// command exists to show what a region of the ledger adds up to. Ordinary
/// numbers stay `Decimal` and print exactly as they always did.
enum Number {
    Fast(rust_decimal::Decimal),
    Exact(bigdecimal::BigDecimal),
}

impl Number {
    fn add(&mut self, other: &Self) {
        if let (Self::Fast(a), Self::Fast(b)) = (&*self, other)
            && let Some(sum) = rustledger_core::checked_add_exact(*a, *b)
        {
            *self = Self::Fast(sum);
            return;
        }
        *self = Self::Exact(self.exact() + other.exact());
    }

    fn exact(&self) -> bigdecimal::BigDecimal {
        match self {
            Self::Fast(d) => rustledger_core::to_bigdecimal(*d),
            Self::Exact(b) => b.clone(),
        }
    }

    fn is_zero(&self) -> bool {
        match self {
            Self::Fast(d) => d.is_zero(),
            Self::Exact(b) => bigdecimal::Zero::is_zero(b),
        }
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fast(d) => write!(f, "{d}"),
            // Back to `Decimal` when a sum returns to its range, so it prints
            // as the ordinary figures beside it; `to_plain_string`, not
            // `Display`, which switches to exponent form.
            Self::Exact(b) => match rustledger_core::decimal_from_big_exact(b) {
                Some(d) => write!(f, "{d}"),
                None => f.write_str(&b.to_plain_string()),
            },
        }
    }
}

pub(super) fn cmd_region<W: Write>(
    file: &PathBuf,
    start_line: usize,
    end_line: usize,
    conversion: Option<Conversion>,
    writer: &mut W,
) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let conversion_str = match conversion {
        Some(Conversion::Value) => " (converted to value)",
        Some(Conversion::Cost) => " (converted to cost)",
        None => "",
    };
    writeln!(
        writer,
        "Transactions in region {}:{}-{}{}",
        file.display(),
        start_line,
        end_line,
        conversion_str
    )?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Get the source file for line number conversion
    let source_file = load_result.source_map.get(0);

    // Find transactions in the line range
    let mut region_transactions: Vec<&rustledger_core::Transaction> = Vec::new();

    for spanned in &load_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            // Convert byte offset to line number using source map
            let txn_line = match source_file {
                Some(sf) => sf.line_col(spanned.span.start).0,
                None => continue,
            };

            // Check if transaction line falls within the requested range
            if txn_line >= start_line && txn_line <= end_line {
                region_transactions.push(txn);
            }
        }
    }

    if region_transactions.is_empty() {
        writeln!(
            writer,
            "No transactions found in lines {start_line}-{end_line}"
        )?;
        return Ok(());
    }

    writeln!(
        writer,
        "Found {} transaction(s):",
        region_transactions.len()
    )?;
    writeln!(writer)?;

    // Calculate balances for these transactions
    let mut balances: BTreeMap<String, Number> = BTreeMap::new();

    for txn in &region_transactions {
        // One line: a newline in the narration is escaped too
        // (#2714); the doctor's writer escapes the other controls.
        writeln!(
            writer,
            "{} {} \"{}\"",
            txn.date,
            txn.flag,
            rustledger_plugin::escape_untrusted_line(&txn.narration)
        )?;
        for posting in &txn.postings {
            if let Some(amount) = posting.amount() {
                // Apply conversion if specified
                let (display_number, display_currency) = match conversion {
                    Some(Conversion::Cost) => {
                        // Use cost if available, otherwise fall back to units
                        if let Some(ref cost) = posting.cost
                            && let Some(number) = cost.number.as_ref()
                        {
                            // Total cost via the exhaustive helper: stored
                            // totals stay precision-exact (PerUnitFromTotal /
                            // Total, the post-#1164 preference) and Compound
                            // costs `N·a + b`. The previous total()/per_unit()
                            // accessor chain returned None for Compound and
                            // fell through to bare units mislabeled as the
                            // cost currency (L3 — this command reads the RAW
                            // load stream, where Compound survives as-written).
                            //
                            // A cost spec WITHOUT a number (`{}`, bare
                            // `{USD}` lot matching) has no determinable cost
                            // here, so it falls through to the units display
                            // below — labeling the unit count with the cost
                            // currency would be the same mislabel bug in a
                            // different coat (review catch).
                            // Exact past `Decimal`'s range (#2572): `total_for`
                            // answers only where a `Decimal` holds the total.
                            let total_cost = number.total_for(amount.number).map_or_else(
                                || Number::Exact(number.total_for_exact(amount.number)),
                                Number::Fast,
                            );
                            let currency = cost
                                .currency
                                .clone()
                                .unwrap_or_else(|| amount.currency.clone());
                            (total_cost, currency)
                        } else {
                            (Number::Fast(amount.number), amount.currency.clone())
                        }
                    }
                    Some(Conversion::Value) => {
                        // For value conversion, we would need a price database
                        // For now, just show a note and use the original values
                        writeln!(
                            writer,
                            "  (Note: value conversion requires price database, showing units)"
                        )?;
                        (Number::Fast(amount.number), amount.currency.clone())
                    }
                    None => (Number::Fast(amount.number), amount.currency.clone()),
                };
                writeln!(
                    writer,
                    "  {} {} {}",
                    posting.account, display_number, display_currency
                )?;
                balances
                    .entry(format!("{}:{}", posting.account, display_currency))
                    .or_insert(Number::Fast(rust_decimal::Decimal::ZERO))
                    .add(&display_number);
            } else {
                writeln!(writer, "  {}", posting.account)?;
            }
        }
        writeln!(writer)?;
    }

    // Print net balances
    writeln!(writer, "Net changes{conversion_str}:")?;
    for (key, balance) in &balances {
        if !balance.is_zero() {
            writeln!(writer, "  {key}: {balance}")?;
        }
    }

    Ok(())
}
