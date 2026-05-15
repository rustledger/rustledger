//! Forecast plugin - generate recurring transactions.
//!
//! This plugin generates recurring transactions from template transactions
//! marked with the "#" flag. The periodicity is specified in the narration.
//!
//! Example:
//! ```beancount
//! 2014-03-08 # "Electricity bill [MONTHLY]"
//!   Expenses:Electricity  50.10 USD
//!   Assets:Checking      -50.10 USD
//! ```
//!
//! Supported patterns:
//! - `[MONTHLY]` - Repeat monthly until end of current year
//! - `[WEEKLY]` - Repeat weekly until end of current year
//! - `[DAILY]` - Repeat daily until end of current year
//! - `[YEARLY]` - Repeat yearly until end of current year
//! - `[MONTHLY REPEAT 3 TIMES]` - Repeat 3 times
//! - `[MONTHLY UNTIL 2020-12-31]` - Repeat until specified date
//! - `[MONTHLY SKIP 1 TIME]` - Skip every other month

use regex::Regex;
use rustledger_core::NaiveDate;
use std::sync::LazyLock;

use crate::types::{DirectiveData, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Regex for parsing forecast patterns in narrations.
/// Matches: `[MONTHLY]`, `[WEEKLY SKIP 2 TIMES]`, `[MONTHLY UNTIL 2025-12-31]`, etc.
static FORECAST_PATTERN_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"(?x)
        (^.*?)                             # narration prefix
        \[
        (MONTHLY|YEARLY|WEEKLY|DAILY)     # interval type
        (?:\s+SKIP\s+(\d+)\s+TIMES?)?     # optional SKIP n TIMES
        (?:\s+REPEAT\s+(\d+)\s+TIMES?)?   # optional REPEAT n TIMES
        (?:\s+UNTIL\s+(\d{4}-\d{2}-\d{2}))? # optional UNTIL date
        \]
    ",
    )
    .expect("FORECAST_PATTERN_RE: invalid regex pattern")
});

/// Plugin for generating recurring forecast transactions.
pub struct ForecastPlugin;

#[derive(Debug, Clone, Copy, PartialEq)]
enum Interval {
    Daily,
    Weekly,
    Monthly,
    Yearly,
}

impl NativePlugin for ForecastPlugin {
    fn name(&self) -> &'static str {
        "forecast"
    }

    fn description(&self) -> &'static str {
        "Generate recurring forecast transactions"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Get current year end as default until date
        let today = jiff::Zoned::now().date();
        let default_until = rustledger_core::naive_date(i32::from(today.year()), 12, 31).unwrap();

        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());

        for (i, directive) in input.directives.into_iter().enumerate() {
            // Only `#`-flagged transactions are forecast templates; all
            // others pass through unchanged.
            let is_forecast = matches!(&directive.data,
                DirectiveData::Transaction(t) if t.flag == "#");
            if !is_forecast {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            if let DirectiveData::Transaction(ref txn) = directive.data {
                if let Some(caps) = FORECAST_PATTERN_RE.captures(&txn.narration) {
                    let narration_prefix = caps.get(1).map_or("", |m| m.as_str().trim());
                    let interval_str = caps.get(2).map_or("MONTHLY", |m| m.as_str());
                    let skip_count: usize = caps
                        .get(3)
                        .and_then(|m| m.as_str().parse().ok())
                        .unwrap_or(0);
                    let repeat_count: Option<usize> =
                        caps.get(4).and_then(|m| m.as_str().parse().ok());
                    let until_date: Option<NaiveDate> = caps
                        .get(5)
                        .and_then(|m| m.as_str().parse::<NaiveDate>().ok());

                    let interval = match interval_str {
                        "DAILY" => Interval::Daily,
                        "WEEKLY" => Interval::Weekly,
                        "YEARLY" => Interval::Yearly,
                        _ => Interval::Monthly,
                    };

                    // Parse start date
                    let start_date = if let Ok(date) = directive.date.parse::<NaiveDate>() {
                        date
                    } else {
                        // Skip if date is unparsable — keep original template.
                        ops.push(PluginOp::Keep(i));
                        continue;
                    };

                    // Determine end condition
                    let until = until_date.unwrap_or(default_until);

                    // Generate dates
                    let dates =
                        generate_dates(start_date, interval, skip_count, repeat_count, until);

                    // Drop the template (Delete) and Insert one transaction per date.
                    ops.push(PluginOp::Delete(i));
                    for date in dates {
                        let mut new_directive = directive.clone();
                        new_directive.date = date.to_string();
                        new_directive.filename = None;
                        new_directive.lineno = None;

                        if let DirectiveData::Transaction(ref mut new_txn) = new_directive.data {
                            new_txn.narration = narration_prefix.to_string();
                        }

                        ops.push(PluginOp::Insert(new_directive));
                    }
                } else {
                    // No pattern match, keep original
                    ops.push(PluginOp::Keep(i));
                }
            } else {
                ops.push(PluginOp::Keep(i));
            }
        }

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

/// Generate dates according to the specified interval and constraints.
fn generate_dates(
    start: NaiveDate,
    interval: Interval,
    skip: usize,
    repeat: Option<usize>,
    until: NaiveDate,
) -> Vec<NaiveDate> {
    let mut dates = Vec::new();
    let mut current = start;
    let step = skip + 1; // Skip means interval multiplier

    loop {
        dates.push(current);

        // Check repeat count
        if let Some(max_count) = repeat
            && dates.len() >= max_count
        {
            break;
        }

        // Advance to next date
        current = match interval {
            Interval::Daily => current
                .checked_add(jiff::ToSpan::days(step as i64))
                .unwrap_or(current),
            Interval::Weekly => current
                .checked_add(jiff::ToSpan::weeks(step as i64))
                .unwrap_or(current),
            Interval::Monthly => current
                .checked_add(jiff::ToSpan::months(step as i64))
                .unwrap_or(current),
            Interval::Yearly => current
                .checked_add(jiff::ToSpan::years(step as i64))
                .unwrap_or(current),
        };

        // Check until date
        if current > until {
            break;
        }

        // Safety limit
        if dates.len() > 1000 {
            break;
        }
    }

    dates
}

#[cfg(test)]
/// Add months to a date, handling month-end overflow.
fn add_months(date: NaiveDate, months: i32) -> NaiveDate {
    date.checked_add(jiff::ToSpan::months(i64::from(months)))
        .unwrap_or(date)
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_forecast_transaction(date: &str, narration: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "#".to_string(),
                payee: None,
                narration: narration.to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Expenses:Test".to_string(),
                        units: Some(AmountData {
                            number: "100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    },
                    PostingData {
                        account: "Assets:Cash".to_string(),
                        units: Some(AmountData {
                            number: "-100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    },
                ],
            }),
        }
    }

    #[test]
    fn test_forecast_monthly_repeat() {
        let plugin = ForecastPlugin;

        let input = PluginInput {
            directives: vec![create_forecast_transaction(
                "2024-01-15",
                "Electric bill [MONTHLY REPEAT 3 TIMES]",
            )],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 3);

        // Check dates
        assert_eq!(directives[0].date, "2024-01-15");
        assert_eq!(directives[1].date, "2024-02-15");
        assert_eq!(directives[2].date, "2024-03-15");

        // Check narration is cleaned
        if let DirectiveData::Transaction(txn) = &directives[0].data {
            assert_eq!(txn.narration, "Electric bill");
        }
    }

    #[test]
    fn test_forecast_weekly_repeat() {
        let plugin = ForecastPlugin;

        let input = PluginInput {
            directives: vec![create_forecast_transaction(
                "2024-01-01",
                "Groceries [WEEKLY REPEAT 4 TIMES]",
            )],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 4);

        assert_eq!(directives[0].date, "2024-01-01");
        assert_eq!(directives[1].date, "2024-01-08");
        assert_eq!(directives[2].date, "2024-01-15");
        assert_eq!(directives[3].date, "2024-01-22");
    }

    #[test]
    fn test_forecast_until_date() {
        let plugin = ForecastPlugin;

        let input = PluginInput {
            directives: vec![create_forecast_transaction(
                "2024-01-15",
                "Rent [MONTHLY UNTIL 2024-03-15]",
            )],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 3);

        assert_eq!(directives[0].date, "2024-01-15");
        assert_eq!(directives[1].date, "2024-02-15");
        assert_eq!(directives[2].date, "2024-03-15");
    }

    #[test]
    fn test_forecast_skip() {
        let plugin = ForecastPlugin;

        let input = PluginInput {
            directives: vec![create_forecast_transaction(
                "2024-01-01",
                "Insurance [MONTHLY SKIP 1 TIME REPEAT 3 TIMES]",
            )],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 3);

        // With SKIP 1 TIME, it should skip every other month (bi-monthly)
        assert_eq!(directives[0].date, "2024-01-01");
        assert_eq!(directives[1].date, "2024-03-01");
        assert_eq!(directives[2].date, "2024-05-01");
    }

    #[test]
    fn test_forecast_preserves_non_forecast_transactions() {
        let plugin = ForecastPlugin;

        let mut regular_txn = create_forecast_transaction("2024-01-15", "Regular purchase");
        if let DirectiveData::Transaction(ref mut txn) = regular_txn.data {
            txn.flag = "*".to_string(); // Regular transaction, not forecast
        }

        let input = PluginInput {
            directives: vec![regular_txn],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 1);

        if let DirectiveData::Transaction(txn) = &directives[0].data {
            assert_eq!(txn.flag, "*");
            assert_eq!(txn.narration, "Regular purchase");
        }
    }

    #[test]
    fn test_add_months() {
        // Regular case
        assert_eq!(
            add_months(rustledger_core::naive_date(2024, 1, 15).unwrap(), 1),
            rustledger_core::naive_date(2024, 2, 15).unwrap()
        );

        // Month-end overflow (Jan 31 -> Feb 28/29)
        assert_eq!(
            add_months(rustledger_core::naive_date(2024, 1, 31).unwrap(), 1),
            rustledger_core::naive_date(2024, 2, 29).unwrap() // 2024 is leap year
        );

        // Year overflow
        assert_eq!(
            add_months(rustledger_core::naive_date(2024, 11, 15).unwrap(), 3),
            rustledger_core::naive_date(2025, 2, 15).unwrap()
        );
    }
}
