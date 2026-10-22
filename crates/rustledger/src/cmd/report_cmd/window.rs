//! The date window shared by `report balances`, `balsheet`, `income`,
//! `journal`, `holdings` and `budget` (#2643).
//!
//! One set of flags, one parser, one meaning everywhere:
//!
//! - `--from DATE`: the window's first day (inclusive).
//! - `--to DATE`: the day after the window (EXCLUSIVE), as `budget`'s `--to`
//!   always was and as Fava's time filter is.
//! - `--year YYYY`: `--from YYYY-01-01 --to (YYYY+1)-01-01`.
//! - `--time EXPR`: Fava's time-filter syntax, parsed exactly as Fava parses
//!   it ([`super::fava_time`]).
//!
//! `--time` and `--year` each define the whole window, so they combine with
//! nothing else; `--from` and `--to` combine with each other.
//!
//! The window is applied by CLAMPING the ledger, never by filtering it: see
//! [`clamp_to_window`].

use anyhow::{Context, Result, bail};
use rustledger_core::{Directive, NaiveDate};

use super::fava_time;

/// The window flags, flattened into each report that takes them.
#[derive(clap::Args, Debug, Clone, Default, PartialEq, Eq)]
pub struct DateWindow {
    /// Start of the window, inclusive (`YYYY-MM-DD`).
    /// (No short flag: `-f` is the global `--format`.)
    #[arg(long, value_name = "DATE")]
    pub from: Option<String>,
    /// End of the window, EXCLUSIVE (`YYYY-MM-DD`): the first day NOT
    /// reported. A single day is `--from D --to <the day after D>`.
    #[arg(long, value_name = "DATE")]
    pub to: Option<String>,
    /// One calendar year: `--from YYYY-01-01 --to (YYYY+1)-01-01`.
    /// Combines with no other window flag.
    #[arg(long, value_name = "YYYY")]
    pub year: Option<String>,
    /// A window in Fava's time-filter syntax: `2024`, `2024-Q1`, `2024-03`,
    /// `2024-W05`, `2024-03-15`, `FY2024`, `FY2024-Q2`, ranges such as
    /// `2024-01 - 2024-03` or `2024-01 to 2024-03`, and the relative `year`,
    /// `quarter`, `month`, `week`, `day`, `fiscal_year`, `fiscal_quarter`,
    /// optionally offset (`year-1`, `month+2`). Fiscal years follow the
    /// ledger's `custom "fava-option" "fiscal-year-end" "MM-DD"`.
    /// Combines with no other window flag.
    #[arg(long, value_name = "EXPR")]
    pub time: Option<String>,
}

/// The bounds a [`DateWindow`] resolved to. Either may be open: each report
/// decides what an open bound means (the whole ledger for the clamped
/// reports; `budget` keeps its own defaults).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ResolvedWindow {
    /// Inclusive first day.
    pub from: Option<NaiveDate>,
    /// Exclusive end.
    pub to: Option<NaiveDate>,
}

/// Parse a `--from`/`--to` date: `YYYY-MM-DD` only.
///
/// The message is the one `report budget` has always given.
pub fn parse_ymd(s: &str) -> Result<NaiveDate> {
    s.parse()
        .with_context(|| format!("invalid date {s:?} (expected YYYY-MM-DD)"))
}

impl DateWindow {
    /// Whether any window flag was given.
    #[must_use]
    pub const fn is_set(&self) -> bool {
        self.from.is_some() || self.to.is_some() || self.year.is_some() || self.time.is_some()
    }

    /// Resolve the flags to bounds.
    ///
    /// `fye` and `today` are only read by `--time` (fiscal and relative
    /// forms).
    ///
    /// # Errors
    ///
    /// A conflicting combination, an unparsable value, or a window whose
    /// end is not after its begin.
    pub fn resolve(
        &self,
        fye: fava_time::FiscalYearEnd,
        today: NaiveDate,
    ) -> Result<ResolvedWindow> {
        // `--time` and `--year` each name the whole window. clap does not
        // enforce this (ag-rledger builds the arguments without clap), so the
        // check lives here, once, for both surfaces.
        let given = |set: bool, name: &'static str| set.then_some(name);
        if let Some(time) = &self.time {
            let others: Vec<&str> = [
                given(self.from.is_some(), "--from"),
                given(self.to.is_some(), "--to"),
                given(self.year.is_some(), "--year"),
            ]
            .into_iter()
            .flatten()
            .collect();
            if !others.is_empty() {
                bail!(
                    "--time cannot be combined with {}: --time {time:?} already names the whole \
                     window",
                    others.join(" or ")
                );
            }
            let (from, to) = fava_time::time_window(time, fye, today)?;
            return Ok(ResolvedWindow {
                from: Some(from),
                to: Some(to),
            });
        }
        if let Some(year) = &self.year {
            let others: Vec<&str> = [
                given(self.from.is_some(), "--from"),
                given(self.to.is_some(), "--to"),
            ]
            .into_iter()
            .flatten()
            .collect();
            if !others.is_empty() {
                bail!(
                    "--year cannot be combined with {}: --year {year} already names the whole \
                     window (--from {year}-01-01 --to <the next year>-01-01)",
                    others.join(" or ")
                );
            }
            let n: i16 = Some(year.as_str())
                .filter(|y| y.len() == 4 && y.bytes().all(|b| b.is_ascii_digit()))
                .and_then(|y| y.parse().ok())
                .filter(|y| (1..=9998).contains(y))
                .with_context(|| format!("invalid --year {year:?} (expected a year, YYYY)"))?;
            let from = NaiveDate::new(n, 1, 1).context("--year")?;
            let to = NaiveDate::new(n + 1, 1, 1).context("--year")?;
            return Ok(ResolvedWindow {
                from: Some(from),
                to: Some(to),
            });
        }
        let from = self.from.as_deref().map(parse_ymd).transpose()?;
        let to = self.to.as_deref().map(parse_ymd).transpose()?;
        if let (Some(from), Some(to)) = (from, to)
            && from >= to
        {
            bail!(
                "--from ({from}) is not before --to ({to}); the window is empty \
                 (--to is EXCLUSIVE, so a single day is --from {from} --to <the next day>)"
            );
        }
        Ok(ResolvedWindow { from, to })
    }
}

/// The ledger, clamped to `[from, to)`.
///
/// Through [`rustledger_ops::clamp::clamp`] — the clamp rustfava uses for
/// Fava's time filter, modeled on beancount's `summarize.clamp_opt` — so
/// activity before the window becomes opening balances against
/// `account_previous_balances`, income and expenses before it are rolled into
/// `account_previous_earnings`, and nothing on or after `to` survives. A
/// balance sheet over the result still balances, which a date FILTER cannot
/// promise.
///
/// An open `from` summarizes nothing; an open `to` keeps everything to the
/// end of the ledger.
///
/// # Errors
///
/// A running balance before `from` that leaves `Decimal`'s range (#1863), or
/// an open `to` on a ledger with entries on the last representable day.
pub fn clamp_to_window(
    directives: &[Directive],
    window: ResolvedWindow,
    accounts: &rustledger_ops::clamp::ClampAccounts,
) -> Result<Vec<Directive>> {
    let begin = window.from.unwrap_or(NaiveDate::MIN);
    let end = match window.to {
        Some(to) => to,
        None => match directives.iter().map(Directive::date).max() {
            None => NaiveDate::MAX,
            Some(last) => last.tomorrow().map_err(|_| {
                anyhow::anyhow!(
                    "the ledger has entries on {last}, the last representable day, so a window \
                     without an end cannot include them; give --to"
                )
            })?,
        },
    };
    rustledger_ops::clamp::clamp(directives, begin, end, accounts)
        .map_err(|e| anyhow::anyhow!("cannot summarize the ledger before {begin}: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(s: &str) -> NaiveDate {
        s.parse().unwrap()
    }

    fn resolve(w: &DateWindow) -> Result<ResolvedWindow> {
        w.resolve(fava_time::END_OF_YEAR, d("2026-10-20"))
    }

    #[test]
    fn year_is_the_calendar_year() {
        let w = DateWindow {
            year: Some("2024".into()),
            ..Default::default()
        };
        assert_eq!(
            resolve(&w).unwrap(),
            ResolvedWindow {
                from: Some(d("2024-01-01")),
                to: Some(d("2025-01-01"))
            }
        );
    }

    #[test]
    fn time_uses_favas_syntax() {
        let w = DateWindow {
            time: Some("year-1".into()),
            ..Default::default()
        };
        assert_eq!(
            resolve(&w).unwrap(),
            ResolvedWindow {
                from: Some(d("2025-01-01")),
                to: Some(d("2026-01-01"))
            }
        );
    }

    #[test]
    fn conflicting_flags_are_rejected() {
        for (w, needle) in [
            (
                DateWindow {
                    time: Some("2024".into()),
                    from: Some("2024-01-01".into()),
                    ..Default::default()
                },
                "--time cannot be combined with --from",
            ),
            (
                DateWindow {
                    time: Some("2024".into()),
                    year: Some("2024".into()),
                    to: Some("2025-01-01".into()),
                    ..Default::default()
                },
                "--time cannot be combined with --to or --year",
            ),
            (
                DateWindow {
                    year: Some("2024".into()),
                    to: Some("2025-01-01".into()),
                    ..Default::default()
                },
                "--year cannot be combined with --to",
            ),
        ] {
            let err = resolve(&w).unwrap_err().to_string();
            assert!(err.contains(needle), "{err}");
        }
    }

    #[test]
    fn bad_values_are_rejected() {
        for w in [
            DateWindow {
                year: Some("24".into()),
                ..Default::default()
            },
            DateWindow {
                year: Some("9999".into()),
                ..Default::default()
            },
            DateWindow {
                from: Some("2024-02-30".into()),
                ..Default::default()
            },
            DateWindow {
                from: Some("2024-03-01".into()),
                to: Some("2024-03-01".into()),
                ..Default::default()
            },
            DateWindow {
                time: Some("2025 - 2024".into()),
                ..Default::default()
            },
            DateWindow {
                time: Some("today".into()),
                ..Default::default()
            },
        ] {
            assert!(resolve(&w).is_err(), "{w:?} must be rejected");
        }
    }

    #[test]
    fn from_and_to_alone_leave_the_other_bound_open() {
        let w = DateWindow {
            from: Some("2024-03-01".into()),
            ..Default::default()
        };
        assert_eq!(
            resolve(&w).unwrap(),
            ResolvedWindow {
                from: Some(d("2024-03-01")),
                to: None
            }
        );
    }
}
