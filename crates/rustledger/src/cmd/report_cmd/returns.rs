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

use super::{OutputFormat, csv_escape, json_escape, sanitize_display};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::{Directive, DisplayContext, MetaValue, NaiveDate, is_subaccount_or_equal};
use rustledger_query::{scope_returns, scopes_returns};
use rustledger_returns::{AccountRole, Scope};
use std::collections::BTreeMap;
use std::io::Write;

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

/// One row of the `--by-group` report: either computed figures, or a marker that
/// the scope hit an unvaluable input.
///
/// Net-units valuation isolates scopes — each sums only its own accounts — so one
/// group hitting an unvaluable input (an in-scope account with an elided posting,
/// or a commodity with no price) leaves the others computable. The report renders
/// the computable rows and marks the unvaluable ones with `n/a`, rather than
/// aborting the whole report on the first error (#1850 §4).
enum GroupRow {
    Ok(GroupResult),
    /// The scope could not be valued; carries its label and the reason (shown as a
    /// stderr warning, and — in JSON — on the row itself).
    Unvaluable {
        label: String,
        reason: String,
    },
}

/// Compute the return summary for one scope.
///
/// Delegates to [`rustledger_query::scope_returns`] — the composition shared with
/// the component's `session.returns`, which builds the price index and calls the
/// engine's `compute_returns` (one extraction + one realization per scope). This
/// adds only the row `label`.
fn compute_group(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    end_date: NaiveDate,
    label: String,
) -> Result<GroupResult> {
    let r = scope_returns(directives, scope, reporting_currency, end_date)
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

/// Whether a rendered returns report covered every scope, or left some unvaluable.
///
/// Returned only on `Ok(_)` (the report is written to the `writer` in that case);
/// this reports the *completeness* of what was written, so the CLI boundary can
/// decide the process exit code. Keeping the exit-code policy at the call site
/// (rather than having `report_returns` return `Err` after it has already produced
/// output) separates "produce the report" from "decide the exit status". An
/// unvaluable scope renders as an `n/a` row in text/CSV, and as a row with `null`
/// figures plus a populated `error` field in JSON.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ReturnsOutcome {
    /// Every scope was valued.
    Complete,
    /// `unvaluable` of `total` scopes could not be valued (rendered `n/a` in
    /// text/CSV, or `null` figures with an `error` field in JSON). The report was
    /// still written; the caller should exit non-zero.
    Partial { unvaluable: usize, total: usize },
}

/// Generate the returns report.
///
/// `directives` must be the interpolated, pad-expanded stream (the returns
/// engine's input contract; booking is not required, net units are valued at
/// market); the dispatcher passes `balance_input` for exactly this reason. With
/// `by_group`, the report adds one independent-sub-portfolio row per
/// `returns-group:` group (constrained to `--investments`/`--income`) alongside
/// the whole-portfolio TOTAL; otherwise it is the single whole-scope summary.
/// Grouping is opt-in, so the default output shape never changes.
///
/// # Returns
///
/// [`ReturnsOutcome`], reporting whether the written report covered every scope
/// or left some `--by-group` rows unvaluable (`n/a` in text/CSV, or `null` figures
/// with an `error` field in JSON). On `Ok(_)` the report is written to `writer`
/// either way; the caller maps [`ReturnsOutcome::Partial`] to a non-zero exit.
///
/// # Errors
///
/// Returns an error if no reporting currency can be determined (neither
/// `--currency` nor an `operating_currency` option), if `--end` is not a valid
/// `YYYY-MM-DD` date, or if a cash flow or held position cannot be priced in the
/// reporting currency (a [`rustledger_returns::ExtractError`]). Also errors if
/// *every* scope is unvaluable (there is nothing to render).
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
    warnings: &mut dyn super::Diagnostics,
) -> Result<ReturnsOutcome> {
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
    let currency = reporting_currency.as_str();
    if !by_group {
        let total = compute_group(
            directives,
            &whole_scope,
            &reporting_currency,
            end_date,
            "TOTAL".to_string(),
        )?;
        render_single(&total, currency, end_date, ctx, format, writer)?;
        return Ok(ReturnsOutcome::Complete);
    }

    // Grouping is opt-in; warnings (bad tags, overlaps, non-self-contained
    // groups) go to stderr so they never pollute the report on stdout.
    let group_scopes = build_groups(directives, &whole_scope, end_date, &mut |w| {
        warnings.emit(super::Diagnostic::message(w));
    });
    if group_scopes.is_empty() {
        // Still emit the grouped shape (an empty `groups` list plus the TOTAL):
        // `--by-group` must produce one stable schema regardless of ledger
        // content, so a JSON/CSV consumer never has to branch on it.
        warnings.emit(super::Diagnostic::message(
            "--by-group but no in-scope `returns-group:` metadata found; reporting \
             only the whole-portfolio total",
        ));
        // No groups to partially render, so an unvaluable TOTAL still fails loudly
        // (via `?`), matching the all-unvaluable rule below.
        let total = compute_group(
            directives,
            &whole_scope,
            &reporting_currency,
            end_date,
            "TOTAL".to_string(),
        )?;
        render_grouped(
            &[],
            &GroupRow::Ok(total),
            currency,
            end_date,
            ctx,
            format,
            writer,
        )?;
        return Ok(ReturnsOutcome::Complete);
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
    let computed = scopes_returns(directives, &scopes, &reporting_currency, end_date);

    // Each scope is valued independently (net-units isolates them), so a scope that
    // hits an unvaluable input becomes an `n/a` row with a stderr warning rather
    // than aborting the whole report — figures for the computable groups still
    // render (#1850 §4). Only if EVERY row (TOTAL included) is unvaluable is there
    // nothing to show, and the report fails loudly.
    let mut rows: Vec<GroupRow> = Vec::with_capacity(computed.len());
    for (result, label) in computed.into_iter().zip(labels) {
        match result {
            Ok(r) => rows.push(GroupRow::Ok(GroupResult {
                label,
                flow_count: r.cash_flows,
                invested: r.invested,
                distributions: r.distributions,
                current_value: r.current_value,
                mwr: r.money_weighted,
                twr: r.time_weighted,
            })),
            Err(e) => {
                // `label` is a user-controlled `returns-group` value; sanitize it
                // for this stderr warning so it cannot inject control chars / extra
                // lines (same guard the grouping warnings use). The error text is
                // grammar-constrained (account names / currencies), so it needs no
                // sanitizing.
                warnings.emit(super::Diagnostic::message(format!(
                    "returns for {} are unavailable: {e}",
                    sanitize_display(&label)
                )));
                rows.push(GroupRow::Unvaluable {
                    label,
                    reason: e.to_string(),
                });
            }
        }
    }
    let unvaluable = rows
        .iter()
        .filter(|r| matches!(r, GroupRow::Unvaluable { .. }))
        .count();
    if unvaluable == rows.len() {
        // Nothing is computable — surface the TOTAL's reason as the failure.
        let reason = match rows.first() {
            Some(GroupRow::Unvaluable { reason, .. }) => reason.clone(),
            _ => "no valuable scope".to_string(),
        };
        anyhow::bail!("no returns could be computed: {reason}");
    }
    let (total, groups) = rows
        .split_first()
        .expect("scopes always contains the whole-portfolio TOTAL");

    render_grouped(groups, total, currency, end_date, ctx, format, writer)?;

    // The report is written (computable rows + `n/a` markers). Report completeness
    // to the caller as data rather than erroring after producing output; the CLI
    // boundary maps `Partial` to a non-zero exit so a pipeline gating on exit
    // status does not treat an incomplete report as a full success (the CSV/text
    // formats carry no error column, so the exit code is their only machine-readable
    // "incomplete" signal; JSON also has a per-row `error` field).
    if unvaluable > 0 {
        Ok(ReturnsOutcome::Partial {
            unvaluable,
            total: rows.len(),
        })
    } else {
        Ok(ReturnsOutcome::Complete)
    }
}

/// Format a rate as a 2-decimal percentage string, or `"n/a"` when undefined.
/// A rate rounding to zero renders a clean `"0.00"` (not `"-0.00"`).
///
/// Shared with the capgains report's realized-IRR columns so every rate this CLI
/// prints uses one unit (percent) and one precision.
pub(super) fn fmt_rate(rate: Option<f64>) -> String {
    rate.map_or_else(
        || "n/a".to_string(),
        |r| {
            let pct = r * 100.0;
            let pct = if pct.abs() < 0.005 { 0.0 } else { pct };
            format!("{pct:.2}")
        },
    )
}

/// A rate for a **text** table: the numeric rate carries its own `%`, but an
/// undefined rate is `n/a` (not `n/a%`). Matches `render_single`'s single-scope
/// text output, where the `%` hangs off the value, not the column.
///
/// Shared with the capgains report's realized-IRR column so the two rate columns
/// cannot drift in formatting.
pub(super) fn fmt_rate_pct(rate: Option<f64>) -> String {
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
pub(super) fn json_rate(rate: Option<f64>) -> String {
    rate.map_or_else(|| "null".to_string(), |r| fmt_rate(Some(r)))
}

/// Per-group rows plus a TOTAL, when grouping is active.
///
/// A row that hit an unvaluable input renders `n/a` figures rather than aborting
/// the report (#1850 §4); in JSON it also carries an `error` field (`null` on a
/// computed row) so the failure is machine-distinguishable.
fn render_grouped<W: Write>(
    groups: &[GroupRow],
    total: &GroupRow,
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
            for row in rows {
                match row {
                    GroupRow::Ok(r) => writeln!(
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
                    )?,
                    // An unvaluable row keeps the column count stable with `n/a` in
                    // every figure column; the reason is on stderr.
                    GroupRow::Unvaluable { label, .. } => writeln!(
                        writer,
                        "{},{},{},n/a,n/a,n/a,n/a,n/a,n/a",
                        csv_escape(&sanitize_display(label)),
                        end_date,
                        currency,
                    )?,
                }
            }
        }
        OutputFormat::Json => {
            let obj = |row: &GroupRow| match row {
                GroupRow::Ok(r) => format!(
                    r#"{{"group": "{}", "cash_flows": {}, "invested": "{}", "distributions": "{}", "current_value": "{}", "money_weighted_return_pct": {}, "time_weighted_return_pct": {}, "error": null}}"#,
                    json_escape(&r.label),
                    r.flow_count,
                    money(r.invested),
                    money(r.distributions),
                    money(r.current_value),
                    json_rate(r.mwr),
                    json_rate(r.twr),
                ),
                // Stable schema: same keys, figures `null`, plus the reason string.
                GroupRow::Unvaluable { label, reason } => format!(
                    r#"{{"group": "{}", "cash_flows": null, "invested": null, "distributions": null, "current_value": null, "money_weighted_return_pct": null, "time_weighted_return_pct": null, "error": "{}"}}"#,
                    json_escape(label),
                    json_escape(reason),
                ),
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
            let row = |w: &mut W, row: &GroupRow| -> Result<()> {
                match row {
                    GroupRow::Ok(r) => writeln!(
                        w,
                        "{:23}{:>9}{:>9}{:>12}{:>14}{:>12}",
                        truncate(&r.label, 23),
                        fmt_rate_pct(r.mwr),
                        fmt_rate_pct(r.twr),
                        money(r.invested),
                        money(r.distributions),
                        money(r.current_value),
                    )?,
                    // `n/a` in every figure column; the reason is on stderr.
                    GroupRow::Unvaluable { label, .. } => writeln!(
                        w,
                        "{:23}{:>9}{:>9}{:>12}{:>14}{:>12}",
                        truncate(label, 23),
                        "n/a",
                        "n/a",
                        "n/a",
                        "n/a",
                        "n/a",
                    )?,
                }
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
/// Delegates to the shared [`super::truncate_label`], which sanitizes control
/// characters so a label can neither split the fixed-width row across lines nor
/// inject a spoofed second line into the text report.
fn truncate(s: &str, width: usize) -> String {
    super::truncate_label(s, width)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_core::{Amount, Posting, Price, Transaction, naive_date};
    use rustledger_query::PriceDatabase;
    // The drift guards below exercise the engine's individual primitives
    // (`terminal_value` / `extract_flows` / `extract_cash_flows`), which the
    // production path no longer imports (it uses the shared
    // `rustledger_query::scope_returns`). They obtain a `PriceOracle` from the
    // canonical `PriceDatabase::as_oracle()`; `PriceOracle` is in scope to call
    // `.convert` on it directly.
    use rustledger_returns::{PriceOracle, extract_flows, terminal_value};

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
    /// (net units) deliberately re-derives `report_cmd::account_balances`'
    /// lot-matching realization (a leaf crate cannot call this CLI-side helper).
    /// Pin that the two still agree — the returns terminal value must equal the
    /// market valuation of `account_balances`' inventories for the same scope and
    /// date. Includes a **reduction** (an empty-cost `{}` sell that lot-matches):
    /// that is the exact shape where net-units and the lot-matching engine keep
    /// different intermediate state, so a buy-only fixture could not catch a
    /// divergence on the reduction path. If either realization changes, this trips.
    #[test]
    fn terminal_value_matches_account_balances_realization() {
        use rustledger_core::{CostNumber, CostSpec};
        let cost = |n: i64| {
            CostSpec::empty()
                .with_number(CostNumber::PerUnit {
                    value: Decimal::from(n),
                })
                .with_currency("USD")
        };
        let dirs = vec![
            Directive::Transaction(
                Transaction::new(d(2020, 1, 1), "buy lot 1")
                    .with_synthesized_posting(
                        Posting::new("Assets:Broker:Stock", money(10, "AAPL")).with_cost(cost(100)),
                    )
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-1000, "USD"))),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 3, 1), "buy lot 2")
                    .with_synthesized_posting(
                        Posting::new("Assets:Broker:Stock", money(5, "AAPL")).with_cost(cost(120)),
                    )
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-600, "USD"))),
            ),
            // Reduction: sell 4 with an empty cost that lot-matches lot 1 (FIFO).
            // Net units and the lot-matching engine must agree the residual is 11.
            Directive::Transaction(
                Transaction::new(d(2020, 6, 1), "sell 4")
                    .with_synthesized_posting(
                        Posting::new("Assets:Broker:Stock", money(-4, "AAPL"))
                            .with_cost(CostSpec::empty()),
                    )
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(600, "USD"))),
            ),
            Directive::Price(Price::new(d(2020, 12, 31), "AAPL", money(150, "USD"))),
        ];
        let end = d(2020, 12, 31);
        let price_db = PriceDatabase::from_directives(&dirs);
        let oracle = price_db.as_oracle();

        // Independently value `account_balances`' inventories at market for the
        // same scope, then compare to `terminal_value`.
        let mut ab_total = Decimal::ZERO;
        for (account, inv) in super::super::account_balances(&dirs).expect("fixture fits") {
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
        // Sanity: net 10 + 5 − 4 = 11 AAPL @ 150 = 1650 USD.
        assert_eq!(tv.amount, Decimal::from(1650));
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
        let oracle = price_db.as_oracle();

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

    /// The CLI `report returns` path (`compute_group` -> `scope_returns`) values
    /// **net units at market**, so a booking-failed (un-booked, re-merged)
    /// transaction — the common state of imported brokerage data — must NOT trap
    /// and must NOT refuse the report. Over-reducing an empty-cost lot (sell 10 of
    /// a 5-lot) nets to −5 units, valued at the terminal price. `rledger check`
    /// remains the validator (see #1850); without the net-units rewrite this native
    /// test would abort in the lot-matching booking engine.
    #[test]
    fn compute_group_tolerates_unbooked_oversell_not_traps() {
        use rustledger_core::{CostNumber, CostSpec};
        let dirs = vec![
            Directive::Transaction(
                Transaction::new(d(2020, 1, 1), "buy")
                    .with_synthesized_posting(
                        Posting::new("Assets:Broker:Stock", money(5, "AAPL")).with_cost(
                            CostSpec::empty()
                                .with_number(CostNumber::PerUnit {
                                    value: Decimal::from(100),
                                })
                                .with_currency("USD"),
                        ),
                    )
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-500, "USD"))),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 6, 1), "oversell")
                    .with_synthesized_posting(
                        Posting::new("Assets:Broker:Stock", money(-10, "AAPL"))
                            .with_cost(CostSpec::empty()),
                    )
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(1000, "USD"))),
            ),
            Directive::Price(Price::new(d(2020, 12, 31), "AAPL", money(120, "USD"))),
        ];
        let scope = Scope::new(vec!["Assets:Broker".to_string()], vec![]);
        let r = compute_group(&dirs, &scope, "USD", d(2020, 12, 31), "TOTAL".to_string())
            .expect("the CLI report path values net units, tolerating an over-sell");
        // Net −5 AAPL × 120 = −600; not a trap, not a refusal.
        assert_eq!(r.current_value, Decimal::from(-600));
    }

    /// #1850 §4: `render_grouped` marks an unvaluable row `n/a` (never aborts) and,
    /// in JSON, carries a machine-readable `error` on that row while a computed
    /// row's `error` is `null` — the schema stays stable across both shapes.
    #[test]
    fn render_grouped_marks_unvaluable_rows() {
        let ctx = DisplayContext::new();
        let end = d(2020, 12, 31);
        let groups = vec![
            GroupRow::Ok(GroupResult {
                label: "Tech".to_string(),
                flow_count: 2,
                invested: Decimal::from(1000),
                distributions: Decimal::ZERO,
                current_value: Decimal::from(1300),
                mwr: Some(0.30),
                twr: Some(0.30),
            }),
            GroupRow::Unvaluable {
                label: "Broken".to_string(),
                reason: "cannot compute returns: account Assets:Broker:Broken has an un-booked (elided) posting".to_string(),
            },
        ];
        let total = GroupRow::Unvaluable {
            label: "TOTAL".to_string(),
            reason: "cannot compute returns: account Assets:Broker:Broken has an un-booked (elided) posting".to_string(),
        };

        // Text: Tech's figures render; the Broken and TOTAL rows are `n/a`.
        let mut text = Vec::new();
        render_grouped(
            &groups,
            &total,
            "USD",
            end,
            &ctx,
            &OutputFormat::Text,
            &mut text,
        )
        .unwrap();
        let text = String::from_utf8(text).unwrap();
        assert!(
            text.contains("1300"),
            "computed group renders its figures:\n{text}"
        );
        let broken = text
            .lines()
            .find(|l| l.starts_with("Broken"))
            .expect("Broken row");
        assert!(
            broken.contains("n/a"),
            "unvaluable group is n/a: {broken:?}"
        );
        assert!(!broken.contains("1300"));
        let total_line = text
            .lines()
            .find(|l| l.starts_with("TOTAL"))
            .expect("TOTAL row");
        assert!(
            total_line.contains("n/a"),
            "unvaluable TOTAL is n/a: {total_line:?}"
        );

        // JSON: stable schema — computed row `error: null`, unvaluable row carries
        // the reason with `null` figures.
        let mut json = Vec::new();
        render_grouped(
            &groups,
            &total,
            "USD",
            end,
            &ctx,
            &OutputFormat::Json,
            &mut json,
        )
        .unwrap();
        let json = String::from_utf8(json).unwrap();
        // Parse structurally so the assertions pin the `error` FIELD, not a
        // substring floating anywhere in the blob (CLAUDE.md: assert the exact
        // observable, not a proxy).
        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("render_grouped must emit valid JSON");
        let rows = parsed["groups"].as_array().expect("groups array");
        let tech = &rows[0];
        let broken = &rows[1];
        let reason = "cannot compute returns: account Assets:Broker:Broken has an un-booked (elided) posting";

        // Computed row: figures present, `error` explicitly null.
        assert_eq!(tech["group"], "Tech");
        assert!(
            tech["current_value"].is_string(),
            "computed figure present: {tech}"
        );
        assert!(
            tech["error"].is_null(),
            "computed row error must be null: {tech}"
        );

        // Unvaluable row: the reason is on the `error` FIELD, and every figure is
        // null — the stable schema a consumer branches on.
        assert_eq!(broken["group"], "Broken");
        assert_eq!(
            broken["error"].as_str(),
            Some(reason),
            "reason on the error field: {broken}"
        );
        assert!(
            broken["current_value"].is_null(),
            "unvaluable figures null: {broken}"
        );
        assert!(
            broken["cash_flows"].is_null(),
            "unvaluable figures null: {broken}"
        );

        // The TOTAL row is likewise unvaluable, same schema.
        assert_eq!(parsed["total"]["error"].as_str(), Some(reason));
        assert!(parsed["total"]["current_value"].is_null());
    }

    /// #1850 §4 end-to-end: a `--by-group` report with one valuable group and one
    /// unvaluable group (an elided in-scope posting) renders the valuable group's
    /// figures and marks the unvaluable one — and the whole-portfolio TOTAL, which
    /// includes the elided account — `n/a`, instead of aborting on the first error
    /// (the pre-fix `?`). The partial report IS still written to the writer, and the
    /// call returns `Ok(ReturnsOutcome::Partial)`; the CLI boundary maps that to a
    /// non-zero exit (review pass 2, finding [0]).
    #[test]
    fn report_returns_by_group_partial_renders() {
        use rustledger_core::{Metadata, Open};
        let group_meta = |name: &str| {
            let mut m = Metadata::default();
            m.insert(
                "returns-group".to_string(),
                MetaValue::String(name.to_string()),
            );
            m
        };
        let dirs = vec![
            Directive::Open(
                Open::new(d(2020, 1, 1), "Assets:Broker:Tech").with_meta(group_meta("Tech")),
            ),
            Directive::Open(
                Open::new(d(2020, 1, 1), "Assets:Broker:Broken").with_meta(group_meta("Broken")),
            ),
            Directive::Transaction(
                Transaction::new(d(2020, 1, 2), "buy")
                    .with_synthesized_posting(Posting::new("Assets:Broker:Tech", money(10, "AAPL")))
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-1000, "USD"))),
            ),
            // Elided in-scope leg → net units unknown → this group (and TOTAL) can't
            // be valued, but the Tech group is untouched.
            Directive::Transaction(
                Transaction::new(d(2020, 3, 1), "elided")
                    .with_synthesized_posting(Posting::auto("Assets:Broker:Broken"))
                    .with_synthesized_posting(Posting::new("Assets:Bank", money(-500, "USD"))),
            ),
            Directive::Price(Price::new(d(2020, 12, 31), "AAPL", money(130, "USD"))),
        ];
        let ctx = DisplayContext::new();
        let mut out = Vec::new();
        let r = report_returns(
            &dirs,
            &["USD".to_string()],
            &["Assets:Broker".to_string()],
            &[],
            None,
            Some("2020-12-31"),
            true,
            &ctx,
            &OutputFormat::Text,
            &mut out,
            &mut crate::cmd::report_cmd::CollectedDiagnostics::default(),
        );
        // The report is written AND the outcome reports it is partial (2 of 3
        // scopes unvaluable: Broken and TOTAL). The non-zero exit is the CLI
        // boundary's job, mapped from this outcome; here we assert the producer's
        // contract directly, without an Err-after-write.
        assert_eq!(
            r.expect("a partial report is Ok(Partial), not Err"),
            ReturnsOutcome::Partial {
                unvaluable: 2,
                total: 3
            },
        );
        let out = String::from_utf8(out).unwrap();
        assert!(
            out.contains("1300"),
            "the valuable Tech group is still rendered:\n{out}"
        );
        let broken = out
            .lines()
            .find(|l| l.starts_with("Broken"))
            .expect("Broken row");
        assert!(
            broken.contains("n/a"),
            "unvaluable group is n/a: {broken:?}"
        );
        let total_line = out
            .lines()
            .find(|l| l.starts_with("TOTAL"))
            .expect("TOTAL row");
        assert!(
            total_line.contains("n/a"),
            "unvaluable TOTAL is n/a: {total_line:?}"
        );
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
