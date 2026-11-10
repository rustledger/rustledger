use anyhow::{Context, Result};
use rustledger_loader::{Loader, is_read_only_option, known_options, option_value_kind};
use std::io::Write;
use std::path::PathBuf;

/// One line describing each option. The NAMES and value kinds come from the
/// loader (`known_options`, `option_value_kind`), the one list of what
/// `Options::set` accepts; only the prose lives here, and
/// `test_option_description_covers_exactly_the_loader_options` keeps the two
/// in step.
fn option_description(key: &str) -> Option<&'static str> {
    let description = match key {
        "title" => "The title of the ledger",
        "filename" => "The top-level file name, set by the loader",
        "operating_currency" => "Operating currencies (can be specified multiple times)",
        "name_assets" => "Root name for Assets accounts (default: Assets)",
        "name_liabilities" => "Root name for Liabilities accounts (default: Liabilities)",
        "name_equity" => "Root name for Equity accounts (default: Equity)",
        "name_income" => "Root name for Income accounts (default: Income)",
        "name_expenses" => "Root name for Expenses accounts (default: Expenses)",
        "account_rounding" => "Account for rounding errors (inert, as in beancount 3)",
        "account_previous_balances" => "Account for opening balances",
        "account_previous_earnings" => "Account for previous earnings",
        "account_previous_conversions" => "Account for previous conversions",
        "account_current_earnings" => "Account for current earnings",
        "account_current_conversions" => "Account for current conversions",
        "account_unrealized_gains" => "Account for unrealized gains",
        "conversion_currency" => "Currency for conversions",
        "inferred_tolerance_default" => "Default tolerance per currency (e.g. USD:0.005)",
        "inferred_tolerance_multiplier" => "Deprecated name of tolerance_multiplier",
        "tolerance_multiplier" => "Multiplier for inferred tolerances",
        "infer_tolerance_from_cost" => "Infer tolerance from cost and price",
        "use_precise_interpolation" => "Accepted; rustledger always interpolates precisely",
        "booking_method" => "Default booking method (STRICT, FIFO, LIFO, etc.)",
        "render_commas" => "Render commas in numbers",
        "display_precision" => "Display precision per currency (e.g. USD:0.01)",
        "allow_pipe_separator" => "Allow the pipe separator (deprecated)",
        "long_string_maxlines" => "Maximum lines for long strings (inert, as in beancount 3)",
        "documents" => "Directories to search for documents",
        "insert_pythonpath" => "Prepend the ledger's directory to the Python path",
        "plugin_processing_mode" => "Plugin processing mode",
        "plugin" => "Use the plugin directive instead",
        _ => return None,
    };
    Some(description)
}

pub(super) fn cmd_list_options<W: Write>(writer: &mut W) -> Result<()> {
    writeln!(writer, "Available beancount options:")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    for &name in known_options() {
        let kind = option_value_kind(name).unwrap_or("string");
        let description = option_description(name).unwrap_or_default();
        if is_read_only_option(name) {
            writeln!(writer, "option \"{name}\" <{kind}> (read-only)")?;
        } else {
            writeln!(writer, "option \"{name}\" <{kind}>")?;
        }
        writeln!(writer, "  {description}")?;
        writeln!(writer)?;
    }

    Ok(())
}

pub(super) fn cmd_print_options<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    writeln!(writer, "Options from {}:", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    let options = &load_result.options;

    if let Some(title) = &options.title {
        writeln!(writer, "title: {title:?}")?;
    }
    if !options.operating_currency.is_empty() {
        writeln!(
            writer,
            "operating_currency: {:?}",
            options.operating_currency
        )?;
    }
    writeln!(writer, "name_assets: {:?}", options.name_assets)?;
    writeln!(writer, "name_liabilities: {:?}", options.name_liabilities)?;
    writeln!(writer, "name_equity: {:?}", options.name_equity)?;
    writeln!(writer, "name_income: {:?}", options.name_income)?;
    writeln!(writer, "name_expenses: {:?}", options.name_expenses)?;

    writeln!(
        writer,
        "account_previous_balances: {:?}",
        options.account_previous_balances
    )?;
    writeln!(
        writer,
        "account_previous_earnings: {:?}",
        options.account_previous_earnings
    )?;
    writeln!(
        writer,
        "account_current_earnings: {:?}",
        options.account_current_earnings
    )?;
    if let Some(acct) = &options.account_unrealized_gains {
        writeln!(writer, "account_unrealized_gains: {acct:?}")?;
    }

    writeln!(writer, "booking_method: {:?}", options.booking_method)?;

    if !options.documents.is_empty() {
        writeln!(writer, "documents: {:?}", options.documents)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The doctor's list is the loader's list: every option the loader knows
    /// is described, and nothing it does not know is (#2925 review). It used
    /// to be a hand-written copy that called `insert_pythonpath` a string.
    #[test]
    fn test_option_description_covers_exactly_the_loader_options() {
        for name in known_options() {
            assert!(
                option_description(name).is_some(),
                "{name} is not described"
            );
        }
        for name in [
            "experiment_explicit_tolerances",
            "use_legacy_fixed_tolerances",
        ] {
            assert_eq!(option_description(name), None, "{name}");
        }

        let mut out = Vec::new();
        cmd_list_options(&mut out).expect("listing writes to a Vec");
        let out = String::from_utf8(out).expect("utf-8");
        let listed: Vec<&str> = out
            .lines()
            .filter_map(|line| line.strip_prefix("option \""))
            .filter_map(|rest| rest.split('"').next())
            .collect();
        assert_eq!(listed, known_options());
        assert!(out.contains("option \"insert_pythonpath\" <bool>"), "{out}");
        assert!(
            out.contains("option \"plugin\" <string> (read-only)"),
            "{out}"
        );
    }
}
