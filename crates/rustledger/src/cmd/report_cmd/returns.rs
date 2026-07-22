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
//! it additionally reports one row per `returns-group:` group: tag `open`
//! directives with `returns-group: "Name"`, and each group's members are
//! classified by the whole scope — accounts under `--investments` form the
//! group's investment scope, accounts under `--income` its income scope — so a
//! group that tags its dividend account reports a **dividend-inclusive** return.
//! This is beangrow's group model, declared in the ledger rather than an external
//! config file.
//!
//! Each group is an **independent sub-portfolio**: its return is computed over
//! just that group's accounts, exactly as if you had run the report with
//! `--investments`/`--income` narrowed to them. This matches how beangrow and
//! hledger `roi` present grouped returns — and, deliberately, the groups are
//! **not** claimed to sum to the TOTAL. They can't be in general: whenever two
//! groups share an in-scope account (most often a pooled settlement-cash account
//! under `--investments`), the boundary flow into that shared account cannot be
//! attributed to one group, so a partition into reconciling slices is not
//! well-defined. The TOTAL row is the whole-portfolio figure (every in-scope
//! account), reported alongside for reference, not as the sum of the rows above.
//!
//! Grouping is opt-in, so the default output shape is unchanged. Only tagged
//! accounts appear; an untagged in-scope holding is simply omitted from the
//! breakdown (it is still in the TOTAL). Warnings (to stderr) flag the cases a
//! reader would otherwise misread: a tag on an out-of-scope account, a non-string
//! tag value, two groups whose accounts overlap by prefix (the shared holding is
//! counted in both), and a group that is not self-contained (it shares an
//! in-scope account with the rest of the portfolio, so its return counts an
//! internal transfer as a flow).
//!
//! Auto per-account and true per-commodity attribution are deliberately *not*
//! offered: a dividend booked to a shared cash/income account cannot be
//! attributed to one holding automatically — which is why every reference tool
//! (beangrow, fava-portfolio-summary) uses declared groups that bundle their
//! income accounts.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Directive, DisplayContext, MetaValue, NaiveDate, is_subaccount_or_equal,
};
use rustledger_query::PriceDatabase;
use rustledger_returns::{AccountRole, PriceOracle, Scope, compute_returns, compute_returns_multi};
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
/// Delegates to the engine's `compute_returns`, which extracts the boundary flows
/// and realizes the portfolio ONCE. Previously this consumer composed
/// `extract_flows` + `terminal_value` + `twr`, and `twr` itself re-ran
/// `extract_flows` and a second realization — so each group did ~2 extractions and
/// ~2 realizations. This adds only the row `label`.
fn compute_group(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    prices: &impl PriceOracle,
    end_date: NaiveDate,
    label: String,
) -> Result<GroupResult> {
    let r = compute_returns(directives, scope, reporting_currency, prices, end_date)
        .with_context(|| format!("computing investment returns for {label}"))?;
    Ok(GroupResult {
        label,
        flow_count: r.cash_flows,
        invested: r.invested,
        distributions: r.distributions,
        current_value: r.current_value,
        mwr: r.money_weighted,
        twr: r.time_weighted,
    })
}

/// Build the `--by-group` breakdown from `returns-group:` metadata on `open`
/// directives, one [`Scope`] per group, sorted by group name.
///
/// Each tagged account is classified by the **whole scope** — accounts under
/// `--investments` form their group's investment scope, accounts under
/// `--income` its income scope — so a group that tags its dividend account is
/// dividend-inclusive (the beangrow model, in-ledger). Every group is an
/// independent sub-portfolio; only tagged accounts appear (there is no residual),
/// and the rows are deliberately not a partition of the total (see the module
/// docs). Warns — but still returns the group — for the cases a reader would
/// otherwise misread:
///
/// - a `returns-group:` tag on an account that is neither investment nor income
///   (an Equity/Liability account, or one outside `--investments`/`--income`) —
///   out of scope, dropped so it is never valued as a phantom holding;
/// - a non-string `returns-group:` value;
/// - two groups whose accounts overlap by prefix — `Scope` matches by prefix, so
///   a tagged ancestor (or a duplicate `open`) values another group's holding
///   twice;
/// - a group that is not self-contained: it shares an in-scope account with the
///   rest of the portfolio, so its flows count an internal transfer as a
///   contribution/withdrawal.
///
/// Bounded by `end_date`, exactly as extraction is: an `open` (or a transaction,
/// for the self-containment check) dated after the report horizon is ignored, so
/// a historical report shows no group for an account that does not exist yet.
///
/// An empty result means no in-scope account carried a usable tag; the caller
/// still emits the grouped output shape (an empty group list plus the
/// whole-portfolio total), just with no group rows.
fn build_groups(
    directives: &[Directive],
    whole_scope: &Scope,
    end_date: NaiveDate,
    warn: &mut dyn FnMut(String),
) -> Vec<(String, Scope)> {
    // group name -> (investment accounts, income accounts)
    let mut groups: BTreeMap<String, (Vec<String>, Vec<String>)> = BTreeMap::new();
    // (account, group) for every tagged in-scope account, for the overlap check.
    let mut tagged: Vec<(String, String)> = Vec::new();

    for directive in directives {
        let Directive::Open(open) = directive else {
            continue;
        };
        // Bound grouping by the report horizon, exactly as flow extraction and
        // valuation are: an account opened after `--end` does not exist yet in
        // the reported period, so it must not form a (spurious, all-zero) group.
        if open.date > end_date {
            continue;
        }
        let account = open.account.to_string();
        let name = match open.meta.get("returns-group") {
            Some(MetaValue::String(name)) => name.clone(),
            Some(_) => {
                warn(format!(
                    "returns-group on {account} ignored: value must be a quoted string"
                ));
                continue;
            }
            None => continue,
        };
        let role = whole_scope.classify(&account);
        if role == AccountRole::External {
            warn(format!(
                "returns-group on {account} ignored: not under --investments or --income"
            ));
            continue;
        }
        let bucket = groups.entry(name.clone()).or_default();
        if role == AccountRole::Income {
            bucket.1.push(account.clone());
        } else {
            bucket.0.push(account.clone());
        }
        tagged.push((account, name));
    }

    // Cross-group prefix overlap: `Scope` classifies by prefix, so a tagged
    // account that is an ancestor of (or identical to) another group's tagged
    // account silently values the same holding in both groups.
    for (i, (a, group_a)) in tagged.iter().enumerate() {
        for (b, group_b) in &tagged[i + 1..] {
            if group_a != group_b && (is_subaccount_or_equal(a, b) || is_subaccount_or_equal(b, a))
            {
                let (group_a, group_b) = (sanitize_display(group_a), sanitize_display(group_b));
                warn(format!(
                    "accounts {a} (group {group_a}) and {b} (group {group_b}) overlap by prefix; \
                     the shared holding is counted in both groups"
                ));
            }
        }
    }

    let rows: Vec<(String, Scope)> = groups
        .into_iter()
        .map(|(name, (investment, income))| (name, Scope::new(investment, income)))
        .collect();

    // Self-containment: a group that shares an in-scope account with the rest of
    // the portfolio (typically a pooled cash account) counts intra-portfolio
    // transfers as flows, so its return is a standalone view that will not agree
    // with the total. We can't attribute the pooled flow, so we name it. The check
    // for every group runs in ONE pass over the transactions (rather than
    // re-walking the stream per group).
    let shared = shared_inscope_accounts(directives, &rows, whole_scope, end_date);
    for (index, (name, _)) in rows.iter().enumerate() {
        // `TOTAL` is the label of the whole-portfolio row; a group of the same
        // name is indistinguishable from it in the text and CSV output (JSON
        // keeps them structurally separate).
        if name == "TOTAL" {
            warn(
                "group named \"TOTAL\" collides with the whole-portfolio total row in text/CSV output"
                    .to_string(),
            );
        }
        if let Some(account) = &shared[index] {
            let name = sanitize_display(name);
            warn(format!(
                "group {name} is not self-contained: it shares in-scope account {account} with the \
                 rest of the portfolio, so its return counts internal transfers as flows"
            ));
        }
    }

    rows
}

/// Replace control characters and the Unicode line/paragraph separators
/// (U+2028/U+2029) with a space. A `returns-group:` label is arbitrary
/// user-controlled text; on the human-facing surfaces (the text table, CSV, and
/// stderr warnings) such bytes could inject terminal escapes or extra lines, so
/// they are neutralized. The JSON path does not use this — it keeps the label
/// intact and valid via `escape_json` (C0 control bytes become `\uXXXX`;
/// U+2028/U+2029 stay as-is, which is already valid inside a JSON string).
fn sanitize_display(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_control() || c == '\u{2028}' || c == '\u{2029}' {
                ' '
            } else {
                c
            }
        })
        .collect()
}

/// The first shared in-scope account for EACH group in `rows`, computed in ONE
/// pass over the transactions instead of re-walking the directive stream once per
/// group. Entry `i` is `Some(account)` when some transaction touching `rows[i]`
/// also touches an account external to that group but still in the whole portfolio
/// scope (see `first_shared_inscope_account`, the per-group reference this
/// reproduces; pinned by `shared_inscope_accounts_matches_per_group`).
fn shared_inscope_accounts(
    directives: &[Directive],
    rows: &[(String, Scope)],
    whole_scope: &Scope,
    end_date: NaiveDate,
) -> Vec<Option<String>> {
    let mut shared: Vec<Option<String>> = vec![None; rows.len()];
    let mut unresolved = rows.len();
    for directive in directives {
        if unresolved == 0 {
            break;
        }
        let Directive::Transaction(txn) = directive else {
            continue;
        };
        // Only activity within the report horizon can affect the reported figures,
        // so a post-`--end` transfer must not raise a false warning.
        if txn.date > end_date {
            continue;
        }
        for (index, (_, scope)) in rows.iter().enumerate() {
            if shared[index].is_some() {
                continue; // this group is already resolved
            }
            // One pass over the postings: the group is touched if any posting is
            // non-external to it, and the shared account is the first posting that
            // is external to the group but still in the whole scope. Resolve only
            // when both hold (a group with no in-group posting isn't touched).
            let mut touches_group = false;
            let mut shared_account: Option<&str> = None;
            for posting in &txn.postings {
                let account = posting.account.as_str();
                if scope.classify(account) != AccountRole::External {
                    touches_group = true;
                } else if shared_account.is_none()
                    && whole_scope.classify(account) != AccountRole::External
                {
                    shared_account = Some(account);
                }
            }
            if touches_group && let Some(account) = shared_account {
                shared[index] = Some(account.to_string());
                unresolved -= 1;
                if unresolved == 0 {
                    break; // every group resolved; skip the rest of this txn's groups
                }
            }
        }
    }
    shared
}

/// The first account, if any, that makes `group_scope` not self-contained: an
/// account that some transaction touching the group also touches, which is
/// external to the group but still in the whole portfolio scope. Such an account
/// (a shared cash/settlement account under `--investments`, say) turns an
/// intra-portfolio transfer into a boundary flow for the group.
///
/// The per-group reference for the batched `shared_inscope_accounts` (which the
/// production path uses); kept as the drift-guard oracle.
#[cfg(test)]
fn first_shared_inscope_account(
    directives: &[Directive],
    group_scope: &Scope,
    whole_scope: &Scope,
    end_date: NaiveDate,
) -> Option<String> {
    for directive in directives {
        let Directive::Transaction(txn) = directive else {
            continue;
        };
        // Only activity within the report horizon can affect the reported
        // figures, so a post-`--end` transfer must not raise a false warning.
        if txn.date > end_date {
            continue;
        }
        let touches_group = txn
            .postings
            .iter()
            .any(|p| group_scope.classify(p.account.as_str()) != AccountRole::External);
        if !touches_group {
            continue;
        }
        for posting in &txn.postings {
            let account = posting.account.as_str();
            if group_scope.classify(account) == AccountRole::External
                && whole_scope.classify(account) != AccountRole::External
            {
                return Some(account.to_string());
            }
        }
    }
    None
}

/// Generate the returns report.
///
/// `directives` must be the booked, pad-expanded stream (the returns engine's
/// input contract); the dispatcher passes `balance_input` for exactly this
/// reason. With `by_group`, the report adds one independent-sub-portfolio row per
/// `returns-group:` group (constrained to `--investments`/`--income`) alongside
/// the whole-portfolio TOTAL; otherwise it is the single whole-scope summary.
/// Grouping is opt-in, so the default output shape never changes.
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

    let currency = reporting_currency.as_str();
    if !by_group {
        let total = compute_group(
            directives,
            &whole_scope,
            &reporting_currency,
            &oracle,
            end_date,
            "TOTAL".to_string(),
        )?;
        return render_single(&total, currency, end_date, ctx, format, writer);
    }

    // Grouping is opt-in; warnings (bad tags, overlaps, non-self-contained
    // groups) go to stderr so they never pollute the report on stdout.
    let group_scopes = build_groups(directives, &whole_scope, end_date, &mut |w| {
        eprintln!("warning: {w}");
    });
    if group_scopes.is_empty() {
        // Still emit the grouped shape (an empty `groups` list plus the TOTAL):
        // `--by-group` must produce one stable schema regardless of ledger
        // content, so a JSON/CSV consumer never has to branch on it.
        eprintln!(
            "warning: --by-group but no in-scope `returns-group:` metadata found; reporting only the whole-portfolio total"
        );
        let total = compute_group(
            directives,
            &whole_scope,
            &reporting_currency,
            &oracle,
            end_date,
            "TOTAL".to_string(),
        )?;
        return render_grouped(&[], &total, currency, end_date, ctx, format, writer);
    }

    // Compute the whole-portfolio TOTAL and every group in ONE shared realization:
    // the booking pass is scope-independent, so `compute_returns_multi` pays it
    // once for all scopes instead of once per group. Scope order is TOTAL first,
    // then the groups; the results come back in the same order.
    let mut labels: Vec<String> = Vec::with_capacity(group_scopes.len() + 1);
    let mut scopes: Vec<Scope> = Vec::with_capacity(group_scopes.len() + 1);
    labels.push("TOTAL".to_string());
    scopes.push(whole_scope);
    for (label, scope) in group_scopes {
        labels.push(label);
        scopes.push(scope);
    }
    let computed =
        compute_returns_multi(directives, &scopes, &reporting_currency, &oracle, end_date);

    let mut rows: Vec<GroupResult> = Vec::with_capacity(computed.len());
    for (result, label) in computed.into_iter().zip(labels) {
        let r = result.with_context(|| format!("computing investment returns for {label}"))?;
        rows.push(GroupResult {
            label,
            flow_count: r.cash_flows,
            invested: r.invested,
            distributions: r.distributions,
            current_value: r.current_value,
            mwr: r.money_weighted,
            twr: r.time_weighted,
        });
    }
    let (total, groups) = rows
        .split_first()
        .expect("scopes always contains the whole-portfolio TOTAL");

    render_grouped(groups, total, currency, end_date, ctx, format, writer)
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

/// A rate for the grouped **text** table: the numeric rate carries its own `%`,
/// but an undefined rate is `n/a` (not `n/a%`). Matches `render_single`'s
/// single-scope text output, where the `%` hangs off the value, not the column.
fn fmt_rate_pct(rate: Option<f64>) -> String {
    match rate {
        Some(_) => format!("{}%", fmt_rate(rate)),
        None => "n/a".to_string(),
    }
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
                    csv_escape(&sanitize_display(&r.label)),
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
            // Rule width must match the column layout below (kept under 80 cols;
            // the Distributions column is 14 so its header keeps a leading gap).
            const RULE: usize = 23 + 9 + 9 + 12 + 14 + 12;
            writeln!(writer, "Returns  ({currency}, as of {end_date})")?;
            writeln!(writer, "{}", "=".repeat(RULE))?;
            writeln!(writer)?;
            writeln!(
                writer,
                "{:23}{:>9}{:>9}{:>12}{:>14}{:>12}",
                "Group", "MWR", "TWR", "Invested", "Distributions", "Current"
            )?;
            writeln!(writer, "{}", "-".repeat(RULE))?;
            let row = |w: &mut W, r: &GroupResult| -> Result<()> {
                writeln!(
                    w,
                    "{:23}{:>9}{:>9}{:>12}{:>14}{:>12}",
                    truncate(&r.label, 23),
                    fmt_rate_pct(r.mwr),
                    fmt_rate_pct(r.twr),
                    money(r.invested),
                    money(r.distributions),
                    money(r.current_value),
                )?;
                Ok(())
            };
            for r in groups {
                row(writer, r)?;
            }
            // Separate the group rows from the TOTAL — but not when there are no
            // group rows (the no-tags case), which would print two rules back to
            // back.
            if !groups.is_empty() {
                writeln!(writer, "{}", "-".repeat(RULE))?;
            }
            row(writer, total)?;
            // The TOTAL is the whole portfolio, not the sum of the group rows
            // (groups are independent and untagged holdings are omitted).
            writeln!(
                writer,
                "Note: TOTAL is the whole portfolio, not the sum of the groups."
            )?;
        }
    }
    Ok(())
}

/// Truncate a label to fit a text column (keeps the informative tail).
///
/// The label is first run through `sanitize_display` (control chars → space),
/// so it can neither split the fixed-width row across lines nor inject a spoofed
/// second line into the text report.
fn truncate(s: &str, width: usize) -> String {
    let s = sanitize_display(s);
    let s = s.as_str();
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
    // The drift guards below compare against the engine's individual primitives,
    // which the production path no longer imports (it uses `compute_returns`).
    use rustledger_returns::{extract_flows, terminal_value};

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn money(n: i64, ccy: &str) -> Amount {
        Amount::new(Decimal::from(n), ccy)
    }

    /// An undefined rate renders as `n/a`, not `n/a%`: the `%` hangs off the
    /// value (as in `render_single`), so the grouped text table stays consistent
    /// with the single-scope output.
    #[test]
    fn undefined_rate_renders_without_a_percent_sign() {
        assert_eq!(fmt_rate_pct(None), "n/a");
        assert_eq!(fmt_rate_pct(Some(0.3236)), "32.36%");
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

    /// Drift guard for the money-weighted series assembly `flows + terminal + sort`.
    ///
    /// The production series now lives in the engine's `compute_returns` (which
    /// open-codes this combine to avoid re-extracting); that copy is pinned against
    /// `extract_cash_flows` by the engine's own
    /// `compute_returns_matches_manual_composition`. This test keeps a second,
    /// independent check that the canonical `extract_cash_flows` assembler itself
    /// still equals `flows + terminal + sort` — the shape both the engine and any
    /// future consumer rely on.
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

    /// Drift guard (CLAUDE.md Canonical-Function Discipline): the batched
    /// `shared_inscope_accounts` (one pass over the transactions, used in
    /// production) must return, per group, exactly what the per-group
    /// `first_shared_inscope_account` reference returns. Covers the order-sensitive
    /// cases: two groups resolved at their first touching transaction (pooled cash),
    /// one never resolved (funded from outside the scope), and one (`Mixed`) whose
    /// first touching transaction is self-contained so it must resolve at a LATER
    /// transaction — whose two qualifying postings also pin first-match selection.
    #[test]
    fn shared_inscope_accounts_matches_per_group() {
        let dirs = vec![
            Directive::Transaction(
                Transaction::new(d(2020, 1, 1), "fund the brokerage")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Broker:Cash",
                        money(1500, "USD"),
                    ))
                    .with_synthesized_posting(Posting::new("Equity:Open", money(-1500, "USD"))),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 1, 2), "buy aapl from pooled cash")
                    .with_synthesized_posting(Posting::new("Assets:Broker:AAPL", money(10, "AAPL")))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Broker:Cash",
                        money(-1000, "USD"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 1, 3), "buy bnd from pooled cash")
                    .with_synthesized_posting(Posting::new("Assets:Broker:BND", money(10, "BND")))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Broker:Cash",
                        money(-500, "USD"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 1, 4), "buy msft from an outside bank")
                    .with_synthesized_posting(Posting::new("Assets:Broker:MSFT", money(10, "MSFT")))
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-500, "USD"))),
            ),
            // The `Mixed` group's FIRST touching transaction is self-contained
            // (funded from the outside bank, no in-scope account outside the
            // group), so it must NOT resolve here — only at the later transaction.
            Directive::Transaction(
                Transaction::new(d(2020, 1, 5), "buy mix from an outside bank")
                    .with_synthesized_posting(Posting::new("Assets:Broker:MIX", money(10, "MIX")))
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-300, "USD"))),
            ),
            // A LATER transaction shares the pooled cash. It has TWO qualifying
            // postings (Cash and Cash2, both in the whole scope, both external to
            // `Mixed`); the first in posting order (Cash) must be the one named.
            Directive::Transaction(
                Transaction::new(d(2020, 1, 6), "rebalance mix into pooled cash")
                    .with_synthesized_posting(Posting::new("Assets:Broker:MIX", money(-4, "MIX")))
                    .with_synthesized_posting(Posting::new("Assets:Broker:Cash", money(80, "USD")))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Broker:Cash2",
                        money(40, "USD"),
                    )),
            ),
        ];
        let whole = Scope::new(vec!["Assets:Broker".to_string()], vec![]);
        let rows = vec![
            (
                "Tech".to_string(),
                Scope::new(vec!["Assets:Broker:AAPL".to_string()], vec![]),
            ),
            (
                "Bonds".to_string(),
                Scope::new(vec!["Assets:Broker:BND".to_string()], vec![]),
            ),
            (
                "Solo".to_string(),
                Scope::new(vec!["Assets:Broker:MSFT".to_string()], vec![]),
            ),
            (
                "Mixed".to_string(),
                Scope::new(vec!["Assets:Broker:MIX".to_string()], vec![]),
            ),
        ];
        let end = d(2020, 12, 31);

        let batch = shared_inscope_accounts(&dirs, &rows, &whole, end);
        let reference: Vec<Option<String>> = rows
            .iter()
            .map(|(_, scope)| first_shared_inscope_account(&dirs, scope, &whole, end))
            .collect();
        assert_eq!(batch, reference, "batched fold diverged from per-group");
        // Not vacuous, and pins the order-sensitive cases:
        assert_eq!(batch[0], Some("Assets:Broker:Cash".to_string())); // Tech shares Cash
        assert_eq!(batch[1], Some("Assets:Broker:Cash".to_string())); // Bonds shares Cash
        assert_eq!(batch[2], None); // Solo self-contained
        // Mixed: resolved at the LATER rebalance txn, naming Cash (the FIRST of that
        // txn's two qualifying postings) — not the earlier self-contained buy.
        assert_eq!(batch[3], Some("Assets:Broker:Cash".to_string()));
    }
}
