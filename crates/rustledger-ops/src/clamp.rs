//! Clamp directives to a date range, summarizing pre-range balances.
//!
//! Typed port of the JSON-based `clamp_entries` (`rustledger-ffi-wasi`). Operates
//! on booked core [`Directive`]s instead of `serde_json::Value`, which removes
//! the posting/cost JSON parsing the old version had to do. See
//! rustledger/rustledger#1401.

use std::collections::HashMap;

use rustledger_core::{
    Amount, Cost, CostNumber, CostSpec, Decimal, Directive, IncompleteAmount, Inventory, Metadata,
    NaiveDate, Position, Posting, Span, Spanned, Transaction,
};

fn account_root(account: &str) -> &str {
    account.split(':').next().unwrap_or("")
}

fn is_balance_sheet(account: &str) -> bool {
    matches!(account_root(account), "Assets" | "Liabilities" | "Equity")
}

fn is_income_statement(account: &str) -> bool {
    matches!(account_root(account), "Income" | "Expenses")
}

/// Type-priority tiebreaker for the final sort (mirrors `clamp_entries`).
const fn type_priority(d: &Directive) -> u8 {
    match d {
        Directive::Open(_) => 0,
        Directive::Balance(_) => 1,
        Directive::Transaction(_) => 2,
        Directive::Close(_) => 10,
        _ => 5,
    }
}

/// Build a [`Position`] from a booked posting's units + optional cost spec.
/// Falls back to a cost-less position when the cost is absent or unresolved.
fn posting_position(units: &Amount, cost: Option<&CostSpec>) -> Position {
    let Some(spec) = cost else {
        return Position::simple(units.clone());
    };
    let Some(cost_number) = spec.number else {
        return Position::simple(units.clone());
    };
    // Per-unit value: PerUnit / PerUnitFromTotal yield it directly; a residual
    // Total spec is divided by |units| (matches the old JSON behavior).
    let per_unit = cost_number.per_unit().or(match cost_number {
        CostNumber::Total { value } if !units.number.is_zero() => Some(value / units.number.abs()),
        _ => None,
    });
    let (Some(number), Some(currency)) = (per_unit, spec.currency.clone()) else {
        return Position::simple(units.clone());
    };
    Position::with_cost(
        units.clone(),
        Cost {
            number,
            currency,
            date: spec.date,
            label: spec.label.clone(),
        },
    )
}

/// A synthesized posting (used for summary/earnings transactions).
fn synthetic_posting(
    account: &str,
    number: Decimal,
    currency: &rustledger_core::Currency,
    cost: Option<CostSpec>,
) -> Spanned<Posting> {
    Spanned::new(
        Posting {
            account: account.into(),
            units: Some(IncompleteAmount::from(Amount {
                number,
                currency: currency.clone(),
            })),
            cost,
            price: None,
            flag: None,
            meta: Metadata::default(),
            comments: Vec::new(),
            trailing_comments: Vec::new(),
        },
        Span::ZERO,
    )
}

fn synthetic_transaction(date: NaiveDate, postings: Vec<Spanned<Posting>>) -> Directive {
    Directive::Transaction(Transaction {
        date,
        flag: 'S',
        payee: None,
        narration: "Opening balance".into(),
        tags: Vec::new(),
        links: Vec::new(),
        meta: Metadata::default(),
        postings,
        trailing_comments: Vec::new(),
    })
}

/// One opening-balance transaction for an account's inventory.
fn summary_transaction(account: &str, inventory: &Inventory, date: NaiveDate) -> Directive {
    let mut postings = Vec::new();
    for position in inventory.positions() {
        let cost = position.cost.as_ref().map(|c| CostSpec {
            number: Some(CostNumber::PerUnit { value: c.number }),
            currency: Some(c.currency.clone()),
            date: c.date,
            label: c.label.clone(),
            merge: false,
        });
        postings.push(synthetic_posting(
            account,
            position.units.number,
            &position.units.currency,
            cost,
        ));
    }
    // Balancing Equity:Opening-Balances posting per position.
    for position in inventory.positions() {
        postings.push(synthetic_posting(
            "Equity:Opening-Balances",
            -position.units.number,
            &position.units.currency,
            None,
        ));
    }
    synthetic_transaction(date, postings)
}

/// Close Income/Expenses P&L totals to Equity:Earnings:Previous.
fn earnings_transaction(pnl: &HashMap<String, Decimal>, date: NaiveDate) -> Option<Directive> {
    let mut currencies: Vec<&String> = pnl.keys().collect();
    currencies.sort();
    let mut postings = Vec::new();
    for currency in currencies {
        let number = pnl[currency];
        if number.is_zero() {
            continue;
        }
        let cur: rustledger_core::Currency = currency.as_str().into();
        postings.push(synthetic_posting(
            "Equity:Earnings:Previous",
            number,
            &cur,
            None,
        ));
        postings.push(synthetic_posting(
            "Equity:Opening-Balances",
            -number,
            &cur,
            None,
        ));
    }
    if postings.is_empty() {
        return None;
    }
    Some(synthetic_transaction(date, postings))
}

/// Clamp `directives` to `[begin, end)`, synthesizing opening balances from
/// pre-`begin` activity and carrying forward the latest prices.
#[must_use]
pub fn clamp(directives: &[Directive], begin: NaiveDate, end: NaiveDate) -> Vec<Directive> {
    clamp_indexed(directives, begin, end)
        .into_iter()
        .map(|(d, _)| d)
        .collect()
}

/// Like [`clamp`], but tags each output with its source-input index.
///
/// Each output directive is paired with the index of the input directive it was
/// passed through from (`Some(i)`), or `None` when synthesized (an
/// opening-balance / earnings summary). This lets callers restore the original
/// source provenance (filename/lineno) on pass-through entries — an in-window
/// transaction or a carried-forward price keeps its real location, rather than
/// every output being attributed to a synthetic `<clamped>` source (the loss
/// that forced the JSON-path workaround in rustledger/rustledger#1425).
#[must_use]
pub fn clamp_indexed(
    directives: &[Directive],
    begin: NaiveDate,
    end: NaiveDate,
) -> Vec<(Directive, Option<usize>)> {
    let mut balances: HashMap<String, Inventory> = HashMap::new();
    let mut latest_prices: HashMap<(String, String), (NaiveDate, Directive, usize)> =
        HashMap::new();
    let mut filtered: Vec<(Directive, usize)> = Vec::new();

    for (i, d) in directives.iter().enumerate() {
        let date = d.date();
        if date < begin {
            match d {
                Directive::Transaction(t) => {
                    for sp in &t.postings {
                        let p = &sp.value;
                        if let Some(units) = p.units.as_ref().and_then(IncompleteAmount::as_amount)
                        {
                            let pos = posting_position(units, p.cost.as_ref());
                            balances.entry(p.account.to_string()).or_default().add(pos);
                        }
                    }
                }
                Directive::Price(pr) => {
                    let key = (pr.currency.to_string(), pr.amount.currency.to_string());
                    let keep = latest_prices.get(&key).is_none_or(|(d0, _, _)| date >= *d0);
                    if keep {
                        latest_prices.insert(key, (date, d.clone(), i));
                    }
                }
                Directive::Open(_) => filtered.push((d.clone(), i)),
                _ => {}
            }
        } else if date < end && !matches!(d, Directive::Commodity(_)) {
            filtered.push((d.clone(), i));
        }
    }

    // Opening-balance summaries for balance-sheet accounts (sorted by name).
    let mut bs_accounts: Vec<(&String, &Inventory)> = balances
        .iter()
        .filter(|(account, inv)| is_balance_sheet(account) && !inv.is_empty())
        .collect();
    bs_accounts.sort_by_key(|(account, _)| (*account).clone());
    // Synthesized summaries carry no source directive (`None`).
    let mut summaries: Vec<(Directive, Option<usize>)> = bs_accounts
        .into_iter()
        .map(|(account, inv)| (summary_transaction(account, inv, begin), None))
        .collect();

    // Earnings: roll up Income/Expenses P&L.
    let mut pnl: HashMap<String, Decimal> = HashMap::new();
    for (account, inv) in &balances {
        if is_income_statement(account) {
            for position in inv.positions() {
                *pnl.entry(position.units.currency.to_string()).or_default() +=
                    position.units.number;
            }
        }
    }
    if let Some(earnings) = earnings_transaction(&pnl, begin) {
        summaries.push((earnings, None));
    }

    let mut all: Vec<(Directive, Option<usize>)> = Vec::new();
    // Carried-forward prices: pass-through from their pre-`begin` source.
    all.extend(latest_prices.into_values().map(|(_, d, i)| (d, Some(i))));
    // Synthesized summaries: no source directive.
    all.append(&mut summaries);
    // In-range entries and pre-`begin` Opens: pass-through.
    all.extend(filtered.into_iter().map(|(d, i)| (d, Some(i))));
    all.sort_by(|a, b| {
        a.0.date()
            .cmp(&b.0.date())
            .then_with(|| type_priority(&a.0).cmp(&type_priority(&b.0)))
            // Core directives carry no content hash; a Display key keeps the
            // order deterministic (the JSON version sorted by meta.hash).
            .then_with(|| a.0.to_string().cmp(&b.0.to_string()))
            // Final tiebreaker so distinct entries with an identical
            // (date, type, Display) sort to a total order regardless of
            // `sort_by`'s instability. Synthesized entries (`None`) precede
            // pass-throughs by `Option` ordering.
            .then_with(|| a.1.cmp(&b.1))
    });
    all
}

#[cfg(test)]
mod tests {
    // Comparing interned strings to literals via `to_string()` is fine in tests.
    #![allow(clippy::cmp_owned)]

    use super::*;
    use rustledger_core::naive_date;
    use rustledger_parser::parse;

    fn dirs(src: &str) -> Vec<Directive> {
        parse(src).directives.into_iter().map(|s| s.value).collect()
    }
    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }
    fn is_summary(dir: &Directive) -> bool {
        matches!(dir, Directive::Transaction(t) if t.flag == 'S' && t.narration.to_string() == "Opening balance")
    }
    fn mentions(dir: &Directive, account: &str) -> bool {
        matches!(dir, Directive::Transaction(t)
            if t.postings.iter().any(|p| p.value.account.to_string() == account))
    }

    #[test]
    fn clamp_indexed_tracks_source_provenance() {
        let input = dirs(
            "2023-06-01 * \"old\"\n  Assets:Cash  100 USD\n  Equity:Opening-Balances  -100 USD\n\
             2024-02-01 * \"in range\"\n  Assets:Cash  -5 USD\n  Expenses:Food  5 USD\n",
        );
        let out = clamp_indexed(&input, d(2024, 1, 1), d(2024, 12, 31));

        // The in-range transaction is a pass-through pointing back at its input
        // (index 1), so a caller can restore its real filename/lineno.
        let in_range = out
            .iter()
            .find(|(dir, _)| {
                matches!(dir, Directive::Transaction(t)
                if t.narration.to_string() == "in range")
            })
            .expect("in-range txn present");
        assert_eq!(in_range.1, Some(1), "in-range entry maps back to input[1]");
        assert!(matches!(&input[1], Directive::Transaction(t)
            if t.narration.to_string() == "in range"));

        // The synthesized opening-balance summary has no source directive.
        let summary = out
            .iter()
            .find(|(dir, _)| is_summary(dir))
            .expect("summary present");
        assert_eq!(summary.1, None, "synthesized summary has no source index");

        // `clamp` is exactly `clamp_indexed` with the indices dropped.
        let plain = clamp(&input, d(2024, 1, 1), d(2024, 12, 31));
        let indexed: Vec<_> = out.into_iter().map(|(dir, _)| dir).collect();
        assert_eq!(
            plain, indexed,
            "clamp must equal clamp_indexed sans indices"
        );
    }

    #[test]
    fn summarizes_pre_begin_balance_into_opening() {
        let input = dirs(
            "2023-06-01 * \"old\"\n  Assets:Cash  100 USD\n  Equity:Opening-Balances  -100 USD\n\
             2024-02-01 * \"in range\"\n  Assets:Cash  -5 USD\n  Expenses:Food  5 USD\n",
        );
        let out = clamp(&input, d(2024, 1, 1), d(2024, 12, 31));

        // No pre-begin entries survive.
        assert!(out.iter().all(|dir| dir.date() >= d(2024, 1, 1)));
        // An opening-balance summary for Assets:Cash at `begin`.
        assert!(
            out.iter().any(|dir| is_summary(dir)
                && dir.date() == d(2024, 1, 1)
                && mentions(dir, "Assets:Cash")),
            "expected an opening-balance summary mentioning Assets:Cash",
        );
        // The in-range transaction is kept.
        assert!(out.iter().any(|dir| matches!(dir, Directive::Transaction(t)
            if t.narration.to_string() == "in range")));
    }

    #[test]
    fn drops_entries_after_end() {
        let input = dirs("2025-01-01 * \"future\"\n  Assets:Cash 1 USD\n  Expenses:X -1 USD\n");
        let out = clamp(&input, d(2024, 1, 1), d(2024, 12, 31));
        assert!(
            out.iter()
                .all(|dir| !matches!(dir, Directive::Transaction(t)
            if t.narration.to_string() == "future"))
        );
    }

    #[test]
    fn excludes_commodity_in_range() {
        let input = dirs("2024-03-01 commodity USD\n");
        let out = clamp(&input, d(2024, 1, 1), d(2024, 12, 31));
        assert!(
            out.iter()
                .all(|dir| !matches!(dir, Directive::Commodity(_)))
        );
    }

    #[test]
    fn keeps_pre_begin_open() {
        let input = dirs("2020-01-01 open Assets:Cash USD\n");
        let out = clamp(&input, d(2024, 1, 1), d(2024, 12, 31));
        assert!(out.iter().any(|dir| matches!(dir, Directive::Open(_))));
    }

    #[test]
    fn earnings_rolled_up_from_income() {
        // Pre-begin income produces an Equity:Earnings:Previous summary.
        let input =
            dirs("2023-05-01 * \"salary\"\n  Assets:Cash  1000 USD\n  Income:Salary  -1000 USD\n");
        let out = clamp(&input, d(2024, 1, 1), d(2024, 12, 31));
        assert!(
            out.iter()
                .any(|dir| mentions(dir, "Equity:Earnings:Previous")),
            "expected an earnings roll-up posting",
        );
    }
}
