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

use crate::types::{DirectiveData, PluginInput, PluginOutput};

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
        let mut forecast_entries = Vec::new();
        let mut filtered_entries = Vec::new();

        // Separate forecast entries from regular entries
        for directive in input.directives {
            if directive.directive_type == "transaction"
                && let DirectiveData::Transaction(ref txn) = directive.data
                && txn.flag == "#"
            {
                forecast_entries.push(directive);
            } else {
                filtered_entries.push(directive);
            }
        }

        // Get current year end as default until date
        let today = rustledger_core::NaiveDate::today();
        let default_until = NaiveDate::from_ymd_opt(today.year(), 12, 31).unwrap();

        // Generate recurring transactions
        let mut new_entries = Vec::new();

        for directive in forecast_entries {
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
                        .and_then(|m| NaiveDate::parse_from_str(m.as_str(), "%Y-%m-%d").ok());

                    let interval = match interval_str {
                        "DAILY" => Interval::Daily,
                        "WEEKLY" => Interval::Weekly,
                        "YEARLY" => Interval::Yearly,
                        _ => Interval::Monthly,
                    };

                    // Parse start date
                    let start_date =
                        if let Ok(date) = NaiveDate::parse_from_str(&directive.date, "%Y-%m-%d") {
                            date
                        } else {
                            // Skip if date is unparsable
                            new_entries.push(directive);
                            continue;
                        };

                    // Determine end condition
                    let until = until_date.unwrap_or(default_until);

                    // Generate dates
                    let dates =
                        generate_dates(start_date, interval, skip_count, repeat_count, until);

                    // Create a transaction for each date
                    for date in dates {
                        let mut new_directive = directive.clone();
                        new_directive.date = date.format("%Y-%m-%d").to_string();

                        if let DirectiveData::Transaction(ref mut new_txn) = new_directive.data {
                            new_txn.narration = narration_prefix.to_string();
                        }

                        new_entries.push(new_directive);
                    }
                } else {
                    // No pattern match, keep original
                    new_entries.push(directive);
                }
            }
        }

        // Sort new entries by date
        new_entries.sort_by(|a, b| a.date.cmp(&b.date));

        // Combine filtered entries with new entries
        filtered_entries.extend(new_entries);

        PluginOutput {
            directives: filtered_entries,
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
            Interval::Daily => current + rustledger_core::Duration::days(step as i64),
            Interval::Weekly => current + rustledger_core::Duration::weeks(step as i64),
            Interval::Monthly => add_months(current, step as i32),
            Interval::Yearly => add_months(current, (step * 12) as i32),
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

/// Add months to a date, handling month-end overflow.
fn add_months(date: NaiveDate, months: i32) -> NaiveDate {
    let total_months = date.month0() as i32 + months;
    let new_year = date.year() + total_months / 12;
    // Normalize total_months to a 0–11 month index even when total_months is negative
    // (Rust's % operator can return a negative remainder, so we use a double modulo).
    let new_month = (total_months % 12 + 12) % 12 + 1;

    // Try to keep the same day, but clamp to valid days in the new month
    let max_day = days_in_month(new_year, new_month as u32);
    let new_day = date.day().min(max_day);

    NaiveDate::from_ymd_opt(new_year, new_month as u32, new_day).unwrap_or(date)
}

/// Get the number of days in a month.
const fn days_in_month(year: i32, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0) {
                29
            } else {
                28
            }
        }
        _ => 30, // Fallback
    }
}

#[cfg(test)]
mod tests {
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

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        assert_eq!(output.directives.len(), 3);

        // Check dates
        assert_eq!(output.directives[0].date, "2024-01-15");
        assert_eq!(output.directives[1].date, "2024-02-15");
        assert_eq!(output.directives[2].date, "2024-03-15");

        // Check narration is cleaned
        if let DirectiveData::Transaction(txn) = &output.directives[0].data {
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

        let output = plugin.process(input);
        assert_eq!(output.directives.len(), 4);

        assert_eq!(output.directives[0].date, "2024-01-01");
        assert_eq!(output.directives[1].date, "2024-01-08");
        assert_eq!(output.directives[2].date, "2024-01-15");
        assert_eq!(output.directives[3].date, "2024-01-22");
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

        let output = plugin.process(input);
        assert_eq!(output.directives.len(), 3);

        assert_eq!(output.directives[0].date, "2024-01-15");
        assert_eq!(output.directives[1].date, "2024-02-15");
        assert_eq!(output.directives[2].date, "2024-03-15");
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

        let output = plugin.process(input);
        assert_eq!(output.directives.len(), 3);

        // With SKIP 1 TIME, it should skip every other month (bi-monthly)
        assert_eq!(output.directives[0].date, "2024-01-01");
        assert_eq!(output.directives[1].date, "2024-03-01");
        assert_eq!(output.directives[2].date, "2024-05-01");
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

        let output = plugin.process(input);
        assert_eq!(output.directives.len(), 1);

        if let DirectiveData::Transaction(txn) = &output.directives[0].data {
            assert_eq!(txn.flag, "*");
            assert_eq!(txn.narration, "Regular purchase");
        }
    }

    #[test]
    fn test_add_months() {
        // Regular case
        assert_eq!(
            add_months(NaiveDate::from_ymd_opt(2024, 1, 15).unwrap(), 1),
            NaiveDate::from_ymd_opt(2024, 2, 15).unwrap()
        );

        // Month-end overflow (Jan 31 -> Feb 28/29)
        assert_eq!(
            add_months(NaiveDate::from_ymd_opt(2024, 1, 31).unwrap(), 1),
            NaiveDate::from_ymd_opt(2024, 2, 29).unwrap() // 2024 is leap year
        );

        // Year overflow
        assert_eq!(
            add_months(NaiveDate::from_ymd_opt(2024, 11, 15).unwrap(), 3),
            NaiveDate::from_ymd_opt(2025, 2, 15).unwrap()
        );
    }
}
