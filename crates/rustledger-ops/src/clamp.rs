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
    let mut balances: HashMap<String, Inventory> = HashMap::new();
    let mut latest_prices: HashMap<(String, String), (NaiveDate, Directive)> = HashMap::new();
    let mut filtered: Vec<Directive> = Vec::new();

    for d in directives {
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
                    let keep = latest_prices.get(&key).is_none_or(|(d0, _)| date >= *d0);
                    if keep {
                        latest_prices.insert(key, (date, d.clone()));
                    }
                }
                Directive::Open(_) => filtered.push(d.clone()),
                _ => {}
            }
        } else if date < end && !matches!(d, Directive::Commodity(_)) {
            filtered.push(d.clone());
        }
    }

    // Opening-balance summaries for balance-sheet accounts (sorted by name).
    let mut bs_accounts: Vec<(&String, &Inventory)> = balances
        .iter()
        .filter(|(account, inv)| is_balance_sheet(account) && !inv.is_empty())
        .collect();
    bs_accounts.sort_by_key(|(account, _)| (*account).clone());
    let mut summaries: Vec<Directive> = bs_accounts
        .into_iter()
        .map(|(account, inv)| summary_transaction(account, inv, begin))
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
        summaries.push(earnings);
    }

    let mut prices: Vec<Directive> = latest_prices.into_values().map(|(_, d)| d).collect();

    let mut all = Vec::new();
    all.append(&mut prices);
    all.append(&mut summaries);
    all.append(&mut filtered);
    all.sort_by(|a, b| {
        a.date()
            .cmp(&b.date())
            .then_with(|| type_priority(a).cmp(&type_priority(b)))
            // Core directives carry no content hash; a Display key keeps the
            // order deterministic (the JSON version sorted by meta.hash).
            .then_with(|| a.to_string().cmp(&b.to_string()))
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
