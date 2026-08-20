//! Clamp directives to a date range, summarizing pre-range balances.
//!
//! Typed port of the JSON-based `clamp_entries` (`rustledger-ffi-wasi`). Operates
//! on booked core [`Directive`]s instead of `serde_json::Value`, which removes
//! the posting/cost JSON parsing the old version had to do. See
//! rustledger/rustledger#1401.

use std::collections::HashMap;

use rustledger_core::{
    AccountTypes, Amount, CostNumber, CostSpec, Decimal, Directive, IncompleteAmount, Inventory,
    Metadata, NaiveDate, OverflowError, Position, Posting, Span, Spanned, Transaction,
};

/// Account configuration for clamp's synthesized summaries (#1806).
///
/// Two things clamp used to hardcode, both broken on a ledger that renames
/// its roots or sets `account_previous_*`:
///
/// - **Classification** — which accounts are balance-sheet (carried forward
///   as opening balances) vs income-statement (rolled into earnings). Uses
///   the canonical [`AccountTypes`] rather than matching root strings, so a
///   `option "name_assets" "Activa"` ledger classifies its accounts instead
///   of silently summarizing nothing.
/// - **Summary account names** — the contra leg of the opening-balance
///   transaction (`account_previous_balances`) and the earnings rollup
///   target (`account_previous_earnings`).
///
/// [`Default`] reproduces beancount's defaults (and rledger's prior
/// hardcoded behavior), so a caller with no ledger options in hand — e.g.
/// the builder free `clamp` over a bare directive list — gets exactly what
/// it got before this config existed.
#[derive(Debug, Clone)]
pub struct ClampAccounts {
    /// Root-name classifier (config-aware; never matches root strings).
    pub types: AccountTypes,
    /// Contra account for synthesized opening balances
    /// (`account_previous_balances`).
    pub previous_balances: String,
    /// Rollup target for pre-window Income/Expenses P&L
    /// (`account_previous_earnings`).
    pub previous_earnings: String,
}

impl Default for ClampAccounts {
    fn default() -> Self {
        Self {
            types: AccountTypes::default(),
            previous_balances: "Equity:Opening-Balances".to_string(),
            previous_earnings: "Equity:Earnings:Previous".to_string(),
        }
    }
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
///
/// Delegates to the canonical [`Position::from_posting`] (→
/// `CostSpec::resolve`), which handles every `CostNumber` variant. The
/// previous hand-rolled per-unit ladder here had no `Compound` arm and
/// silently summarized compound-cost lots as cost-less, destroying their
/// basis in the clamped opening balance (L2). `date` is the posting's
/// transaction date — `resolve` uses it to fill lot dates the spec omits,
/// matching how the booking engine, query engine, and reports build lots.
fn posting_position(units: &Amount, cost: Option<&CostSpec>, date: NaiveDate) -> Position {
    Position::from_posting(units, cost, date)
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
            cost: cost.map(Box::new),
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

/// The cost spec to carry on a synthesized opening-balance posting for a held
/// lot, or `None` for a plain-currency position.
fn position_cost_spec(position: &Position) -> Option<CostSpec> {
    position.cost.as_ref().map(|c| CostSpec {
        number: Some(CostNumber::PerUnit { value: c.number }),
        currency: Some(c.currency.clone()),
        date: c.date,
        label: c.label.clone(),
        merge: false,
    })
}

/// One opening-balance transaction for an account's inventory. `contra` is
/// the balancing account (`ClampAccounts::previous_balances`).
fn summary_transaction(
    account: &str,
    inventory: &Inventory,
    date: NaiveDate,
    contra: &str,
) -> Directive {
    let mut postings = Vec::new();
    for position in inventory.positions() {
        postings.push(synthetic_posting(
            account,
            position.units.number,
            &position.units.currency,
            position_cost_spec(position),
        ));
    }
    // Balancing opening-balances posting per position. A held-at-cost lot
    // MUST carry the same cost here so the opening transaction balances by weight
    // (#1656): the asset leg's weight is `N * cost` in the cost currency, so a
    // bare-units contra leaves that weight unoffset and any at-cost view of the
    // clamped ledger stops summing to zero.
    for position in inventory.positions() {
        postings.push(synthetic_posting(
            contra,
            -position.units.number,
            &position.units.currency,
            position_cost_spec(position),
        ));
    }
    synthetic_transaction(date, postings)
}

/// Close Income/Expenses P&L totals to the earnings account, balanced
/// against the opening-balances contra. `earnings` is
/// `ClampAccounts::previous_earnings`; `contra` is
/// `ClampAccounts::previous_balances` (the same account the opening-balance
/// summaries balance against, so the two summary transactions net to zero
/// on that account).
fn earnings_transaction(
    pnl: &HashMap<String, Decimal>,
    date: NaiveDate,
    earnings: &str,
    contra: &str,
) -> Option<Directive> {
    let mut currencies: Vec<&String> = pnl.keys().collect();
    currencies.sort();
    let mut postings = Vec::new();
    for currency in currencies {
        let number = pnl[currency];
        if number.is_zero() {
            continue;
        }
        let cur: rustledger_core::Currency = currency.as_str().into();
        postings.push(synthetic_posting(earnings, number, &cur, None));
        postings.push(synthetic_posting(contra, -number, &cur, None));
    }
    if postings.is_empty() {
        return None;
    }
    Some(synthetic_transaction(date, postings))
}

/// Clamp `directives` to `[begin, end)`, synthesizing opening balances from
/// pre-`begin` activity and carrying forward the latest prices.
///
/// `accounts` supplies the classification and synthesized-summary account
/// names (#1806); pass [`ClampAccounts::default`] for beancount defaults.
///
/// # Errors
///
/// [`OverflowError`] when a pre-`begin` running balance leaves
/// `rust_decimal`'s range, so the opening-balance summary cannot be computed
/// (#1863). Reported rather than clamped: the summary is emitted as a
/// synthetic transaction that downstream consumers treat as real ledger data.
pub fn clamp(
    directives: &[Directive],
    begin: NaiveDate,
    end: NaiveDate,
    accounts: &ClampAccounts,
) -> Result<Vec<Directive>, OverflowError> {
    Ok(clamp_indexed(directives, begin, end, accounts)?
        .into_iter()
        .map(|(d, _)| d)
        .collect())
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
pub fn clamp_indexed(
    directives: &[Directive],
    begin: NaiveDate,
    end: NaiveDate,
    accounts: &ClampAccounts,
) -> Result<Vec<(Directive, Option<usize>)>, OverflowError> {
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
                            let pos = posting_position(units, p.cost.as_deref(), t.date);
                            balances
                                .entry(p.account.to_string())
                                .or_default()
                                .add(pos)?;
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
        .filter(|(account, inv)| accounts.types.is_balance_sheet(account) && !inv.is_empty())
        .collect();
    bs_accounts.sort_by_key(|(account, _)| (*account).clone());
    // Synthesized summaries carry no source directive (`None`).
    let mut summaries: Vec<(Directive, Option<usize>)> = bs_accounts
        .into_iter()
        .map(|(account, inv)| {
            (
                summary_transaction(account, inv, begin, &accounts.previous_balances),
                None,
            )
        })
        .collect();

    // Earnings: roll up Income/Expenses P&L.
    let mut pnl: HashMap<String, Decimal> = HashMap::new();
    for (account, inv) in &balances {
        if accounts.types.is_income_statement(account) {
            for position in inv.positions() {
                let slot = pnl.entry(position.units.currency.to_string()).or_default();
                *slot = slot
                    .checked_add(position.units.number)
                    .ok_or_else(|| OverflowError {
                        currency: position.units.currency.clone(),
                    })?;
            }
        }
    }
    if let Some(earnings) = earnings_transaction(
        &pnl,
        begin,
        &accounts.previous_earnings,
        &accounts.previous_balances,
    ) {
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
    Ok(all)
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

    /// #1806: on a ledger that renames its roots and its summary accounts,
    /// clamp must classify AND synthesize against the configured names, not
    /// the hardcoded `Assets`/`Equity:Opening-Balances` strings. This pins
    /// both hardcodings at once — the classifier (a renamed asset root must
    /// still be carried forward, which a string-match would silently drop,
    /// producing NO summary) and the contra/earnings account names.
    #[test]
    fn clamp_honors_renamed_roots_and_summary_accounts() {
        // Renamed roots: Activa (assets), Vermogen (equity), Inkomsten
        // (income). Pre-window activity: an asset buy funded by income.
        let src = "2023-01-01 open Activa:Bank\n\
                   2023-01-01 open Inkomsten:Loon\n\n\
                   2023-06-01 * \"pre-window pay\"\n  \
                   Activa:Bank  100.00 EUR\n  \
                   Inkomsten:Loon  -100.00 EUR\n";
        let directives = dirs(src);
        let accounts = ClampAccounts {
            types: AccountTypes {
                assets: "Activa".to_string(),
                liabilities: "Passiva".to_string(),
                equity: "Vermogen".to_string(),
                income: "Inkomsten".to_string(),
                expenses: "Uitgaven".to_string(),
            },
            previous_balances: "Vermogen:Beginsaldi".to_string(),
            previous_earnings: "Vermogen:Winst:Vorig".to_string(),
        };
        let clamped = clamp(&directives, d(2024, 1, 1), d(2024, 12, 31), &accounts)
            .expect("fixture fits in Decimal");

        // The renamed asset account IS carried forward (string-match on
        // "Assets" would have classified it as non-balance-sheet and
        // synthesized nothing — the silent-empty failure).
        let opening = clamped
            .iter()
            .find(|dd| is_summary(dd) && mentions(dd, "Activa:Bank"))
            .expect("renamed asset root must produce an opening balance");
        // ...balanced against the configured contra, NOT Equity:Opening-Balances.
        assert!(
            mentions(opening, "Vermogen:Beginsaldi"),
            "opening balance must use the configured contra account"
        );
        assert!(
            !clamped
                .iter()
                .any(|dd| mentions(dd, "Equity:Opening-Balances")),
            "the hardcoded default contra must not appear on a renamed ledger"
        );

        // Pre-window income rolls up to the configured earnings account.
        let earnings = clamped
            .iter()
            .find(|dd| is_summary(dd) && mentions(dd, "Vermogen:Winst:Vorig"))
            .expect("renamed income root must roll into the configured earnings account");
        assert!(
            mentions(earnings, "Vermogen:Beginsaldi"),
            "earnings rollup must balance against the configured contra"
        );
    }

    /// The `Default` config reproduces the pre-#1806 hardcoded behavior
    /// exactly, so existing callers (and the builder free `clamp`) are
    /// unaffected.
    #[test]
    fn clamp_accounts_default_matches_legacy_hardcoding() {
        let accounts = ClampAccounts::default();
        assert_eq!(accounts.previous_balances, "Equity:Opening-Balances");
        assert_eq!(accounts.previous_earnings, "Equity:Earnings:Previous");
        let src = "2023-01-01 open Assets:Bank\n\
                   2023-01-01 open Income:Salary\n\n\
                   2023-06-01 * \"pay\"\n  \
                   Assets:Bank  100.00 USD\n  \
                   Income:Salary  -100.00 USD\n";
        let clamped = clamp(&dirs(src), d(2024, 1, 1), d(2024, 12, 31), &accounts)
            .expect("fixture fits in Decimal");
        assert!(
            clamped
                .iter()
                .any(|dd| is_summary(dd) && mentions(dd, "Equity:Opening-Balances")),
            "default contra is Equity:Opening-Balances"
        );
        assert!(
            clamped
                .iter()
                .any(|dd| is_summary(dd) && mentions(dd, "Equity:Earnings:Previous")),
            "default earnings is Equity:Earnings:Previous"
        );
    }

    /// L2 regression: a pre-window lot bought at COMPOUND cost
    /// (`{a # b}`) must keep its cost basis in the clamped opening
    /// balance. The old hand-rolled per-unit ladder had no `Compound`
    /// arm and summarized the lot cost-less, destroying the basis.
    #[test]
    fn clamp_preserves_compound_cost_basis() {
        let src = "2024-01-01 open Assets:Broker\n\
                   2024-01-01 open Assets:Cash\n\n\
                   2024-01-05 * \"buy\"\n  \
                   Assets:Broker  10 WIDGET {5.00 # 10.00 USD}\n  \
                   Assets:Cash  -60.00 USD\n";
        let directives = dirs(src);
        let clamped = clamp(
            &directives,
            d(2024, 6, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");
        let summary = clamped
            .iter()
            .find(|dd| is_summary(dd) && mentions(dd, "Assets:Broker"))
            .expect("summary transaction for the pre-window lot");
        let Directive::Transaction(t) = summary else {
            unreachable!()
        };
        let broker = t
            .postings
            .iter()
            .find(|p| p.value.account.to_string() == "Assets:Broker")
            .expect("broker posting");
        let cost = broker
            .value
            .cost
            .as_ref()
            .and_then(|c| c.number)
            .expect("compound cost basis must survive clamping (was None pre-fix)");
        // resolve(): (10*5.00 + 10.00) / 10 = 6.00 per unit.
        assert_eq!(
            cost.per_unit(),
            Some(rust_decimal::Decimal::new(600, 2)),
            "summarized per-unit must be 6.00, got {cost:?}",
        );
    }

    #[test]
    fn clamp_indexed_tracks_source_provenance() {
        let input = dirs(
            "2023-06-01 * \"old\"\n  Assets:Cash  100 USD\n  Equity:Opening-Balances  -100 USD\n\
             2024-02-01 * \"in range\"\n  Assets:Cash  -5 USD\n  Expenses:Food  5 USD\n",
        );
        let out = clamp_indexed(
            &input,
            d(2024, 1, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");

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
        let plain = clamp(
            &input,
            d(2024, 1, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");
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
        let out = clamp(
            &input,
            d(2024, 1, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");

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
        let out = clamp(
            &input,
            d(2024, 1, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");
        assert!(
            out.iter()
                .all(|dir| !matches!(dir, Directive::Transaction(t)
            if t.narration.to_string() == "future"))
        );
    }

    #[test]
    fn excludes_commodity_in_range() {
        let input = dirs("2024-03-01 commodity USD\n");
        let out = clamp(
            &input,
            d(2024, 1, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");
        assert!(
            out.iter()
                .all(|dir| !matches!(dir, Directive::Commodity(_)))
        );
    }

    #[test]
    fn keeps_pre_begin_open() {
        let input = dirs("2020-01-01 open Assets:Cash USD\n");
        let out = clamp(
            &input,
            d(2024, 1, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");
        assert!(out.iter().any(|dir| matches!(dir, Directive::Open(_))));
    }

    #[test]
    fn earnings_rolled_up_from_income() {
        // Pre-begin income produces an Equity:Earnings:Previous summary.
        let input =
            dirs("2023-05-01 * \"salary\"\n  Assets:Cash  1000 USD\n  Income:Salary  -1000 USD\n");
        let out = clamp(
            &input,
            d(2024, 1, 1),
            d(2024, 12, 31),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");
        assert!(
            out.iter()
                .any(|dir| mentions(dir, "Equity:Earnings:Previous")),
            "expected an earnings roll-up posting",
        );
    }

    #[test]
    fn held_at_cost_opening_contra_keeps_its_cost() {
        // #1656: a held-at-cost lot summarized into the opening balance must keep
        // its cost on the Equity:Opening-Balances contra leg, or the opening
        // transaction does not balance by weight — the asset leg's weight is
        // `N * cost` in the cost currency, so a bare-units contra leaves it
        // unoffset and any at-cost view of the clamped ledger stops summing to 0.
        let input = dirs(
            "2000-01-01 open Assets:MC\n\
             2000-01-01 open Equity:Open\n\
             2000-01-02 * \"seed\"\n  Assets:MC   100 USD\n  Equity:Open  -100 USD\n\
             2000-01-03 * \"buy\"\n  Assets:MC    1 XYZ {50 USD}\n  Assets:MC  -50 USD\n",
        );
        // Clamp to a window AFTER all entries: everything becomes opening balance.
        let out = clamp(
            &input,
            d(2014, 1, 1),
            d(2015, 1, 1),
            &ClampAccounts::default(),
        )
        .expect("fixture fits in Decimal");

        let opening = out
            .iter()
            .find_map(|dir| match dir {
                Directive::Transaction(t)
                    if t.flag == 'S' && t.narration.to_string() == "Opening balance" =>
                {
                    Some(t)
                }
                _ => None,
            })
            .expect("an Opening balance summary is synthesized");

        let xyz_contra = opening
            .postings
            .iter()
            .find(|p| {
                p.value.account.to_string() == "Equity:Opening-Balances"
                    && p.value
                        .units
                        .as_ref()
                        .and_then(IncompleteAmount::as_amount)
                        .is_some_and(|a| a.currency.to_string() == "XYZ")
            })
            .expect("an Equity:Opening-Balances contra for the XYZ lot");
        assert!(
            xyz_contra.value.cost.is_some(),
            "held-at-cost contra must keep its cost (#1656), got bare units",
        );
    }
}
