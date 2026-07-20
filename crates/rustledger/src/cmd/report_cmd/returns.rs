//! Returns report — the money-weighted (XIRR) investment return for an account
//! scope.
//!
//! This is the CLI consumer of the `rustledger-returns` engine. It defines the
//! portfolio boundary from `--investments` / `--income` account prefixes, builds
//! a price index from the ledger, and reports the annualized money-weighted
//! return along with the supporting figures (capital invested, distributions
//! received, and current market value).
//!
//! Time-weighted return and per-commodity grouping are not yet implemented; this
//! reports a single money-weighted return for the whole scope (see #1814).

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, DisplayContext, NaiveDate};
use rustledger_query::PriceDatabase;
use rustledger_returns::{PriceOracle, Scope, extract_flows, terminal_value, xirr};
use std::io::Write;

/// Adapts the query engine's [`PriceDatabase`] to the returns engine's
/// [`PriceOracle`] trait.
///
/// The `convert` signatures are identical, so this is a pass-through. It lives
/// here at the composition root — where the CLI is the only place the two crates
/// meet — deliberately: `rustledger-returns` stays a leaf (no dependency on the
/// query engine that owns the price index), and `rustledger-query` stays free of
/// a returns dependency.
pub(super) struct PriceDbOracle<'a>(pub(super) &'a PriceDatabase);

impl PriceOracle for PriceDbOracle<'_> {
    fn convert(&self, amount: &Amount, to_currency: &str, date: NaiveDate) -> Option<Amount> {
        self.0.convert(amount, to_currency, date)
    }
}

/// Generate the returns report.
///
/// `directives` must be the booked, pad-expanded stream (the returns engine's
/// input contract); the dispatcher passes `balance_input` for exactly this
/// reason.
///
/// # Errors
///
/// Returns an error if no reporting currency can be determined (neither
/// `--currency` nor an `operating_currency` option), if `--end` is not a valid
/// `YYYY-MM-DD` date, or if a cash flow or held position cannot be priced in the
/// reporting currency (a [`rustledger_returns::ExtractError`]).
#[allow(clippy::too_many_arguments)]
pub(super) fn report_returns<W: Write>(
    directives: &[Directive],
    operating_currency: &[String],
    investments: &[String],
    income: &[String],
    currency_arg: Option<&str>,
    end_arg: Option<&str>,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // Reporting currency: --currency, else the ledger's first operating currency,
    // else an actionable error (the return is single-currency by construction).
    let reporting_currency: String = match currency_arg {
        Some(c) => c.to_string(),
        None => operating_currency.first().cloned().context(
            "no reporting currency: pass --currency or set `option \"operating_currency\" \"…\"`",
        )?,
    };

    // Valuation date: --end (ISO YYYY-MM-DD), else today. This is both the
    // horizon (later flows are excluded) and the terminal-value date.
    let end_date: NaiveDate = match end_arg {
        Some(s) => s
            .parse()
            .with_context(|| format!("invalid --end date {s:?} (expected YYYY-MM-DD)"))?,
        None => jiff::Zoned::now().date(),
    };

    let scope = Scope::new(investments.to_vec(), income.to_vec());
    // Price index built from the same stream, so implicit transaction prices and
    // explicit `price` directives both feed the valuation.
    let price_db = PriceDatabase::from_directives(directives);
    let oracle = PriceDbOracle(&price_db);

    // Extract boundary flows and the terminal value separately, so the summary
    // can report capital-in / distributions / current-value independently. xirr
    // then runs over the combined, date-sorted series.
    let flows = extract_flows(directives, &scope, &reporting_currency, &oracle, end_date)
        .context("extracting investment cash flows")?;
    let terminal = terminal_value(directives, &scope, &reporting_currency, &oracle, end_date)
        .context("valuing the held position at the report date")?;

    // Supporting figures, all in the reporting currency:
    //   invested      — capital the investor put in (magnitude of outflows)
    //   distributions — cash received during the period (dividends, sale proceeds)
    //   current_value — market value of the position still held (terminal)
    let invested: Decimal = flows
        .iter()
        .filter(|f| f.amount.is_sign_negative())
        .map(|f| -f.amount)
        .sum();
    let distributions: Decimal = flows
        .iter()
        .filter(|f| f.amount.is_sign_positive())
        .map(|f| f.amount)
        .sum();
    let current_value: Decimal = terminal.map_or(Decimal::ZERO, |t| t.amount);

    // Combine into the series xirr consumes. This mirrors the engine's
    // canonical `extract_cash_flows` (flows + terminal, date-sorted); we build it
    // from the parts here only because the summary above needs `flows` and
    // `terminal` separately. The `series_matches_extract_cash_flows` test pins
    // this against the canonical so it can't drift.
    let mut series = flows;
    if let Some(t) = terminal {
        series.push(t);
    }
    series.sort_by_key(|f| f.date);
    let flow_count = series.len();
    // xirr is `None` when the series has no sign change or is otherwise
    // degenerate — a genuinely undefined return, reported as "n/a".
    let rate = xirr(&series);

    let currency = reporting_currency.as_str();
    let money = |n: Decimal| ctx.format_amount_number(n, currency);
    let rate_pct = |r: f64| {
        let pct = r * 100.0;
        // A 0% return (e.g. capital returned unchanged) converges to a tiny
        // signed epsilon that would render as "-0.00"; show a clean "0.00".
        let pct = if pct.abs() < 0.005 { 0.0 } else { pct };
        format!("{pct:.2}")
    };

    match format {
        OutputFormat::Csv => {
            writeln!(
                writer,
                "reporting_currency,as_of,cash_flows,invested,distributions,current_value,money_weighted_return_pct"
            )?;
            writeln!(
                writer,
                "{},{},{},{},{},{},{}",
                currency,
                end_date,
                flow_count,
                csv_escape(&money(invested)),
                csv_escape(&money(distributions)),
                csv_escape(&money(current_value)),
                rate.map_or_else(|| "n/a".to_string(), rate_pct),
            )?;
        }
        OutputFormat::Json => {
            // Same 2-decimal precision as text/csv (a bare JSON number, `null`
            // when undefined) so the rate agrees across every output format.
            let rate_field = rate.map_or_else(|| "null".to_string(), rate_pct);
            writeln!(
                writer,
                r#"{{"reporting_currency": "{}", "as_of": "{}", "cash_flows": {}, "invested": "{}", "distributions": "{}", "current_value": "{}", "money_weighted_return_pct": {}}}"#,
                json_escape(currency),
                end_date,
                flow_count,
                money(invested),
                money(distributions),
                money(current_value),
                rate_field,
            )?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Returns")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;
            writeln!(
                writer,
                "{:24}{} (as of {end_date})",
                "Reporting currency", currency
            )?;
            writeln!(writer, "{:24}{flow_count}", "Cash flows")?;
            writeln!(writer, "{:24}{} {currency}", "Invested", money(invested))?;
            writeln!(
                writer,
                "{:24}{} {currency}",
                "Distributions",
                money(distributions)
            )?;
            writeln!(
                writer,
                "{:24}{} {currency}",
                "Current value",
                money(current_value)
            )?;
            writeln!(writer)?;
            match rate {
                Some(r) => writeln!(writer, "{:24}{}%", "Money-weighted return", rate_pct(r))?,
                None => writeln!(
                    writer,
                    "{:24}n/a (undefined — need at least one inflow and one outflow)",
                    "Money-weighted return"
                )?,
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_core::{Posting, Price, Transaction, naive_date};

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn money(n: i64, ccy: &str) -> Amount {
        Amount::new(Decimal::from(n), ccy)
    }

    /// Drift guard (CLAUDE.md Canonical-Function Discipline): `terminal_value`
    /// deliberately re-derives `report_cmd::account_balances`' realization loop
    /// (a leaf crate cannot call this CLI-side helper). Pin that the two still
    /// agree — the returns terminal value must equal the market valuation of
    /// `account_balances`' inventories for the same scope and date. If the
    /// realization in either place changes, this trips.
    #[test]
    fn terminal_value_matches_account_balances_realization() {
        let dirs = vec![
            Directive::Transaction(
                Transaction::new(d(2020, 1, 1), "buy lot 1")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Broker:Stock",
                        money(10, "AAPL"),
                    ))
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-1000, "USD"))),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 3, 1), "buy lot 2")
                    .with_synthesized_posting(Posting::new("Assets:Broker:Stock", money(5, "AAPL")))
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-600, "USD"))),
            ),
            Directive::Price(Price::new(d(2020, 12, 31), "AAPL", money(150, "USD"))),
        ];
        let end = d(2020, 12, 31);
        let price_db = PriceDatabase::from_directives(&dirs);
        let oracle = PriceDbOracle(&price_db);

        // Independently value `account_balances`' inventories at market for the
        // same scope, then compare to `terminal_value`.
        let mut ab_total = Decimal::ZERO;
        for (account, inv) in super::super::account_balances(&dirs) {
            if !rustledger_core::is_subaccount_or_equal(account.as_str(), "Assets:Broker") {
                continue;
            }
            for pos in inv.positions() {
                if pos.units.number.is_zero() {
                    continue;
                }
                ab_total += oracle.convert(&pos.units, "USD", end).unwrap().number;
            }
        }

        let scope = Scope::new(vec!["Assets:Broker".to_string()], vec![]);
        let tv = terminal_value(&dirs, &scope, "USD", &oracle, end)
            .unwrap()
            .expect("a position is held");
        assert_eq!(
            tv.amount, ab_total,
            "terminal_value drifted from account_balances realization",
        );
        // Sanity: 15 AAPL @ 150 = 2250 USD.
        assert_eq!(tv.amount, Decimal::from(2250));
    }

    /// Drift guard: `report_returns` builds the xirr series by hand from
    /// `extract_flows` + `terminal_value` (it needs the parts for the summary
    /// breakdown). That manual combine must stay equal to the engine's canonical
    /// `extract_cash_flows`; if the engine changes how it assembles the series
    /// (coalescing, a sort tie-break, …), this trips so the CLI is updated in
    /// lockstep rather than silently drifting.
    #[test]
    fn series_matches_extract_cash_flows() {
        let dirs = vec![
            Directive::Transaction(
                Transaction::new(d(2020, 1, 1), "buy")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Broker:Stock",
                        money(10, "AAPL"),
                    ))
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-1000, "USD"))),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 6, 1), "dividend")
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(20, "USD")))
                    .with_synthesized_posting(Posting::new("Income:Dividends", money(-20, "USD"))),
            ),
            Directive::Price(Price::new(d(2020, 12, 31), "AAPL", money(130, "USD"))),
        ];
        let end = d(2020, 12, 31);
        let scope = Scope::new(
            vec!["Assets:Broker".to_string()],
            vec!["Income:Dividends".to_string()],
        );
        let price_db = PriceDatabase::from_directives(&dirs);
        let oracle = PriceDbOracle(&price_db);

        // Reproduce report_returns' hand-built series.
        let flows = extract_flows(&dirs, &scope, "USD", &oracle, end).unwrap();
        let terminal = terminal_value(&dirs, &scope, "USD", &oracle, end).unwrap();
        let mut manual = flows;
        if let Some(t) = terminal {
            manual.push(t);
        }
        manual.sort_by_key(|f| f.date);

        let canonical =
            rustledger_returns::extract_cash_flows(&dirs, &scope, "USD", &oracle, end).unwrap();
        assert_eq!(
            manual, canonical,
            "report_returns' manual combine drifted from extract_cash_flows",
        );
        // Guard against a vacuous pass: the series is the three expected flows.
        assert_eq!(canonical.len(), 3);
    }
}
