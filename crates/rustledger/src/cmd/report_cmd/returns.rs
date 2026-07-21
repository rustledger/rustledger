//! Returns report — money-weighted (XIRR) and time-weighted (TWR) investment
//! return for an account scope, optionally broken down per group.
//!
//! This is the CLI consumer of the `rustledger-returns` engine. It defines the
//! portfolio boundary from `--investments` / `--income` account prefixes, builds
//! a price index from the ledger, and reports the annualized returns plus the
//! supporting figures (capital invested, distributions received, current market
//! value).
//!
//! # Grouping (#1820)
//!
//! By default the report is the single whole-scope summary. With **`--by-group`**
//! it breaks down per `returns-group:` group: tag `open` directives with
//! `returns-group: "Name"`, and each group's members are classified by the whole
//! scope — accounts under `--investments` form the group's investment scope,
//! accounts under `--income` its income scope — so a group that tags its dividend
//! account reports a **dividend-inclusive** return. This is beangrow's group
//! model, declared in the ledger rather than an external config file.
//!
//! Groups are constrained to the scope and reconcile with the total: a tagged
//! account outside `--investments`/`--income` (or an Equity/Liability account) is
//! ignored with a warning, and in-scope accounts left untagged collect into an
//! `(ungrouped)` residual, so every in-scope holding appears in exactly one row.
//! Grouping is opt-in, so the default output shape is unchanged.
//!
//! Auto per-account and true per-commodity attribution are deliberately *not*
//! offered: a dividend booked to a shared cash/income account cannot be
//! attributed to one holding automatically — which is why every reference tool
//! (beangrow, fava-portfolio-summary) uses declared groups that bundle their
//! income accounts.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, DisplayContext, MetaValue, NaiveDate};
use rustledger_query::PriceDatabase;
use rustledger_returns::{
    AccountRole, PriceOracle, Scope, extract_flows, terminal_value, twr, xirr,
};
use std::collections::BTreeMap;
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

/// The computed return figures for one scope (a group, or the whole portfolio).
struct GroupResult {
    label: String,
    flow_count: usize,
    invested: Decimal,
    distributions: Decimal,
    current_value: Decimal,
    /// Money-weighted return (annualized XIRR); `None` when undefined.
    mwr: Option<f64>,
    /// Time-weighted return (annualized); `None` when undefined or unpriceable.
    twr: Option<f64>,
}

/// Compute the return summary for one scope.
///
/// Extracts the boundary flows and terminal value separately (so the summary can
/// report capital-in / distributions / current-value), then runs xirr over the
/// combined, date-sorted series and twr over the same directives. The manual
/// flows+terminal combine mirrors the engine's canonical `extract_cash_flows`
/// and is pinned by the `series_matches_extract_cash_flows` test.
fn compute_group(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
    label: String,
) -> Result<GroupResult> {
    let flows = extract_flows(directives, scope, reporting_currency, prices, end_date)
        .context("extracting investment cash flows")?;
    let terminal = terminal_value(directives, scope, reporting_currency, prices, end_date)
        .context("valuing the held position at the report date")?;

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

    let mut series = flows;
    if let Some(t) = terminal {
        series.push(t);
    }
    series.sort_by_key(|f| f.date);
    let flow_count = series.len();
    let mwr = xirr(&series);
    // TWR needs a price at every flow date; degrade to n/a rather than error.
    let twr_rate = twr(directives, scope, reporting_currency, prices, end_date).unwrap_or(None);

    Ok(GroupResult {
        label,
        flow_count,
        invested,
        distributions,
        current_value,
        mwr,
        twr: twr_rate,
    })
}

/// Build the `--by-group` breakdown from `returns-group:` metadata on `open`
/// directives, sorted by group name, plus an `(ungrouped)` residual.
///
/// Each tagged account is classified by the **whole scope** — accounts under
/// `--investments` form their group's investment scope, accounts under
/// `--income` its income scope — so a group that tags its dividend account is
/// dividend-inclusive (the beangrow model, in-ledger). Two things make the rows
/// coherent with the TOTAL:
///
/// - Groups are constrained to the scope: a tagged account that is neither
///   investment nor income (an Equity/Liability account, or one outside
///   `--investments`/`--income`) is **out of scope** and ignored (with a
///   warning), never valued as a holding.
/// - In-scope accounts left untagged collect into `(ungrouped)`, so every
///   in-scope holding appears in exactly one row and the group rows partition
///   the total.
///
/// A non-string `returns-group:` value is ignored with a warning. Returns
/// `(rows, any_declared)`; `any_declared` is false when no in-scope account
/// carried a usable tag, in which case the caller reports the plain total.
fn build_groups(
    directives: &[Directive],
    whole_scope: &Scope,
    warn: &mut dyn FnMut(String),
) -> (Vec<(String, Scope)>, bool) {
    // group name -> (investment accounts, income accounts)
    let mut groups: BTreeMap<String, (Vec<String>, Vec<String>)> = BTreeMap::new();
    let mut ungrouped: (Vec<String>, Vec<String>) = (Vec::new(), Vec::new());
    let mut any_declared = false;

    for directive in directives {
        let Directive::Open(open) = directive else {
            continue;
        };
        let account = open.account.to_string();
        let role = whole_scope.classify(&account);
        if role == AccountRole::External {
            if open.meta.contains_key("returns-group") {
                warn(format!(
                    "returns-group on {account} ignored: not under --investments or --income"
                ));
            }
            continue;
        }
        let tag = match open.meta.get("returns-group") {
            Some(MetaValue::String(name)) => Some(name.clone()),
            Some(_) => {
                warn(format!(
                    "returns-group on {account} ignored: value must be a quoted string"
                ));
                None
            }
            None => None,
        };
        let bucket = match tag {
            Some(name) => {
                any_declared = true;
                groups.entry(name).or_default()
            }
            None => &mut ungrouped,
        };
        if role == AccountRole::Income {
            bucket.1.push(account);
        } else {
            bucket.0.push(account);
        }
    }

    let mut rows: Vec<(String, Scope)> = groups
        .into_iter()
        .map(|(name, (investment, income))| (name, Scope::new(investment, income)))
        .collect();
    // The residual only makes sense once at least one group was declared.
    if any_declared && (!ungrouped.0.is_empty() || !ungrouped.1.is_empty()) {
        rows.push((
            "(ungrouped)".to_string(),
            Scope::new(ungrouped.0, ungrouped.1),
        ));
    }
    (rows, any_declared)
}

/// Generate the returns report.
///
/// `directives` must be the booked, pad-expanded stream (the returns engine's
/// input contract); the dispatcher passes `balance_input` for exactly this
/// reason. With `by_group`, the report breaks down per `returns-group:` group
/// (constrained to `--investments`/`--income`) plus an `(ungrouped)` residual
/// and the TOTAL; otherwise it is the single whole-scope summary. Grouping is
/// opt-in, so the default output shape never changes.
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
    by_group: bool,
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

    let whole_scope = Scope::new(investments.to_vec(), income.to_vec());
    // Price index built from the same stream, so implicit transaction prices and
    // explicit `price` directives both feed the valuation.
    let price_db = PriceDatabase::from_directives(directives);
    let oracle = PriceDbOracle(&price_db);

    let total = compute_group(
        directives,
        &whole_scope,
        &reporting_currency,
        &oracle,
        end_date,
        "TOTAL".to_string(),
    )?;

    let currency = reporting_currency.as_str();
    if !by_group {
        return render_single(&total, currency, end_date, ctx, format, writer);
    }

    // Grouping is opt-in; warnings (bad tags, out-of-scope tags) go to stderr so
    // they never pollute the report on stdout.
    let (group_scopes, any_declared) =
        build_groups(directives, &whole_scope, &mut |w| eprintln!("warning: {w}"));
    if !any_declared {
        eprintln!(
            "warning: --by-group but no in-scope `returns-group:` metadata found; reporting the ungrouped total"
        );
        return render_single(&total, currency, end_date, ctx, format, writer);
    }

    let groups: Vec<GroupResult> = group_scopes
        .iter()
        .map(|(label, scope)| {
            compute_group(
                directives,
                scope,
                &reporting_currency,
                &oracle,
                end_date,
                label.clone(),
            )
        })
        .collect::<Result<_>>()?;

    render_grouped(&groups, &total, currency, end_date, ctx, format, writer)
}

/// Format a rate as a 2-decimal percentage string, or `"n/a"` when undefined.
/// A rate rounding to zero renders a clean `"0.00"` (not `"-0.00"`).
fn fmt_rate(rate: Option<f64>) -> String {
    rate.map_or_else(
        || "n/a".to_string(),
        |r| {
            let pct = r * 100.0;
            let pct = if pct.abs() < 0.005 { 0.0 } else { pct };
            format!("{pct:.2}")
        },
    )
}

/// The single whole-scope summary (no grouping) — the original report shape.
fn render_single<W: Write>(
    r: &GroupResult,
    currency: &str,
    end_date: NaiveDate,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let money = |n: Decimal| ctx.format_amount_number(n, currency);
    match format {
        OutputFormat::Csv => {
            writeln!(
                writer,
                "reporting_currency,as_of,cash_flows,invested,distributions,current_value,money_weighted_return_pct,time_weighted_return_pct"
            )?;
            writeln!(
                writer,
                "{},{},{},{},{},{},{},{}",
                currency,
                end_date,
                r.flow_count,
                csv_escape(&money(r.invested)),
                csv_escape(&money(r.distributions)),
                csv_escape(&money(r.current_value)),
                fmt_rate(r.mwr),
                fmt_rate(r.twr),
            )?;
        }
        OutputFormat::Json => {
            writeln!(
                writer,
                r#"{{"reporting_currency": "{}", "as_of": "{}", "cash_flows": {}, "invested": "{}", "distributions": "{}", "current_value": "{}", "money_weighted_return_pct": {}, "time_weighted_return_pct": {}}}"#,
                json_escape(currency),
                end_date,
                r.flow_count,
                money(r.invested),
                money(r.distributions),
                money(r.current_value),
                json_rate(r.mwr),
                json_rate(r.twr),
            )?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Returns")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;
            writeln!(
                writer,
                "{:24}{currency} (as of {end_date})",
                "Reporting currency"
            )?;
            writeln!(writer, "{:24}{}", "Cash flows", r.flow_count)?;
            writeln!(writer, "{:24}{} {currency}", "Invested", money(r.invested))?;
            writeln!(
                writer,
                "{:24}{} {currency}",
                "Distributions",
                money(r.distributions)
            )?;
            writeln!(
                writer,
                "{:24}{} {currency}",
                "Current value",
                money(r.current_value)
            )?;
            writeln!(writer)?;
            match r.mwr {
                Some(rate) => writeln!(
                    writer,
                    "{:24}{}%",
                    "Money-weighted return",
                    fmt_rate(Some(rate))
                )?,
                None => writeln!(
                    writer,
                    "{:24}n/a (undefined — need at least one inflow and one outflow)",
                    "Money-weighted return"
                )?,
            }
            match r.twr {
                Some(rate) => writeln!(
                    writer,
                    "{:24}{}%",
                    "Time-weighted return",
                    fmt_rate(Some(rate))
                )?,
                None => writeln!(writer, "{:24}n/a", "Time-weighted return")?,
            }
        }
    }
    Ok(())
}

/// A JSON rate field: a bare 2-decimal number, or `null` when undefined.
fn json_rate(rate: Option<f64>) -> String {
    rate.map_or_else(|| "null".to_string(), |r| fmt_rate(Some(r)))
}

/// Per-group rows plus a TOTAL, when grouping is active.
fn render_grouped<W: Write>(
    groups: &[GroupResult],
    total: &GroupResult,
    currency: &str,
    end_date: NaiveDate,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let money = |n: Decimal| ctx.format_amount_number(n, currency);
    let rows = groups.iter().chain(std::iter::once(total));
    match format {
        OutputFormat::Csv => {
            writeln!(
                writer,
                "group,as_of,reporting_currency,cash_flows,invested,distributions,current_value,money_weighted_return_pct,time_weighted_return_pct"
            )?;
            for r in rows {
                writeln!(
                    writer,
                    "{},{},{},{},{},{},{},{},{}",
                    csv_escape(&r.label),
                    end_date,
                    currency,
                    r.flow_count,
                    csv_escape(&money(r.invested)),
                    csv_escape(&money(r.distributions)),
                    csv_escape(&money(r.current_value)),
                    fmt_rate(r.mwr),
                    fmt_rate(r.twr),
                )?;
            }
        }
        OutputFormat::Json => {
            let obj = |r: &GroupResult| {
                format!(
                    r#"{{"group": "{}", "cash_flows": {}, "invested": "{}", "distributions": "{}", "current_value": "{}", "money_weighted_return_pct": {}, "time_weighted_return_pct": {}}}"#,
                    json_escape(&r.label),
                    r.flow_count,
                    money(r.invested),
                    money(r.distributions),
                    money(r.current_value),
                    json_rate(r.mwr),
                    json_rate(r.twr),
                )
            };
            let group_objs: Vec<String> = groups.iter().map(obj).collect();
            writeln!(
                writer,
                r#"{{"reporting_currency": "{}", "as_of": "{}", "groups": [{}], "total": {}}}"#,
                json_escape(currency),
                end_date,
                group_objs.join(", "),
                obj(total),
            )?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Returns  ({currency}, as of {end_date})")?;
            writeln!(writer, "{}", "=".repeat(72))?;
            writeln!(writer)?;
            writeln!(
                writer,
                "{:32}{:>9}{:>9}{:>12}{:>12}",
                "Group", "MWR", "TWR", "Invested", "Current"
            )?;
            writeln!(writer, "{}", "-".repeat(72))?;
            let row = |w: &mut W, r: &GroupResult| -> Result<()> {
                writeln!(
                    w,
                    "{:32}{:>8}%{:>8}%{:>12}{:>12}",
                    truncate(&r.label, 32),
                    fmt_rate(r.mwr),
                    fmt_rate(r.twr),
                    money(r.invested),
                    money(r.current_value),
                )?;
                Ok(())
            };
            for r in groups {
                row(writer, r)?;
            }
            writeln!(writer, "{}", "-".repeat(72))?;
            row(writer, total)?;
        }
    }
    Ok(())
}

/// Truncate a label to fit a text column (keeps the informative tail).
fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        let tail: String = s
            .chars()
            .rev()
            .take(width - 1)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        format!("…{tail}")
    }
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
