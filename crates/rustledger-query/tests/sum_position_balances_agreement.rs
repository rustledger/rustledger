//! Property: `sum(position) ... GROUP BY account` agrees with `BALANCES`
//! for every account and every `FROM` subset (#2394).
//!
//! Generated ledgers hold up to three accounts booking with AVERAGE (on the
//! `open`, or through the ledger's default method), FIFO or STRICT, two
//! commodities, two cost currencies, and buys, sales, explicit-cost shorts
//! and the issue's short-beside-a-long transaction. A transaction booking
//! rejects is left out, so every ledger is one `check` accepts. For each
//! `FROM` filter the two queries realize the same postings, and:
//!
//! - an AVERAGE account's sum equals its `BALANCES` inventory presented as
//!   one pool per side ([`Inventory::merge_average`]). That presentation is
//!   the one documented difference: booking keeps an AVERAGE account's buys
//!   as separate lots until a sale merges them, and `sum(position)` shows
//!   the pool they already form;
//! - any other account's sum equals its `BALANCES` inventory exactly, as
//!   bean-query's does.
//!
//! A subset booking cannot realize makes `BALANCES` fail, and leaves
//! `sum(position)` the plain sum of its postings; the property counts those
//! as "not both defined" and the test asserts the generator still reaches
//! the realized cases, so the property cannot pass by skipping everything.

use proptest::prelude::*;
use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Decimal, Directive, Inventory};
use rustledger_query::{Executor, Value, parse};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

const COMMODITIES: [&str; 2] = ["X", "Y"];
const CURRENCIES: [&str; 2] = ["USD", "EUR"];
/// The `open` methods drawn from; `None` books with the ledger's default.
const OPEN_METHODS: [Option<&str>; 4] = [Some("AVERAGE"), None, Some("FIFO"), Some("STRICT")];
const DEFAULTS: [BookingMethod; 3] = [
    BookingMethod::Average,
    BookingMethod::Strict,
    BookingMethod::Fifo,
];
/// Entry-level filters keep or drop whole transactions. The posting-level
/// ones (#2414) keep some postings of an account and not others, the case
/// where `BALANCES` sums the selected postings rather than reading booking's
/// inventory.
const FILTERS: [&str; 7] = [
    "",
    " FROM date >= 2020-01-15",
    " FROM date < 2020-01-15",
    " FROM narration = 'even'",
    " FROM narration = 'odd'",
    " FROM number > 0",
    " FROM number < 0",
];

#[derive(Debug, Clone)]
enum Op {
    Buy {
        n: i64,
        cost: i64,
        cur: usize,
    },
    Sell {
        n: i64,
        price: i64,
        cur: usize,
    },
    Short {
        n: i64,
        cost: i64,
        cur: usize,
    },
    ShortAndLong {
        short: i64,
        long: i64,
        cost: i64,
        cur: usize,
    },
}

fn op() -> impl Strategy<Value = Op> {
    let n = 1i64..6;
    let cost = 95i64..106;
    let cur = 0usize..2;
    prop_oneof![
        3 => (n.clone(), cost.clone(), cur.clone()).prop_map(|(n, cost, cur)| Op::Buy { n, cost, cur }),
        3 => (n.clone(), cost.clone(), cur.clone()).prop_map(|(n, price, cur)| Op::Sell { n, price, cur }),
        1 => (n.clone(), cost.clone(), cur.clone()).prop_map(|(n, cost, cur)| Op::Short { n, cost, cur }),
        1 => (n.clone(), n, cost, cur).prop_map(|(short, long, cost, cur)| Op::ShortAndLong { short, long, cost, cur }),
    ]
}

/// `(account, commodity, op)` per transaction.
type Script = Vec<(usize, usize, Op)>;

fn transaction(k: usize, account: usize, commodity: usize, op: &Op) -> String {
    let date = if k < 28 {
        format!("2020-01-{:02}", k + 1)
    } else {
        format!("2020-02-{:02}", k - 27)
    };
    let narration = if k.is_multiple_of(2) { "even" } else { "odd" };
    let a = format!("Assets:A{account}");
    let x = COMMODITIES[commodity];
    let body = match *op {
        Op::Buy { n, cost, cur } => {
            format!(
                "  {a}  {n} {x} {{{cost} {}}}\n  Assets:Cash\n",
                CURRENCIES[cur]
            )
        }
        Op::Sell { n, price, cur } => format!(
            "  {a}  -{n} {x} {{}} @ {price} {c}\n  Assets:Cash  {} {c}\n  Income:PnL\n",
            n * price,
            c = CURRENCIES[cur],
        ),
        Op::Short { n, cost, cur } => {
            format!(
                "  {a}  -{n} {x} {{{cost} {}}}\n  Assets:Cash\n",
                CURRENCIES[cur]
            )
        }
        Op::ShortAndLong {
            short,
            long,
            cost,
            cur,
        } => format!(
            "  {a}  -{short} {x} {{{} {c}}}\n  {a}  {long} {x} {{{cost} {c}}}\n  Assets:Cash\n",
            cost - 1,
            c = CURRENCIES[cur],
        ),
    };
    format!("{date} * \"{narration}\"\n{body}")
}

/// Parse and book, as the loader does. `None` when booking rejects it.
fn book(source: &str, default: BookingMethod) -> Option<Vec<Directive>> {
    let parsed = rustledger_parser::parse(source);
    if !parsed.errors.is_empty() {
        return None;
    }
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(default);
    engine.register_account_methods(directives.iter());
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            engine.book_interpolate_apply(txn).ok()?;
        }
    }
    Some(directives)
}

/// The ledger, keeping only the transactions booking accepts in order.
fn ledger(opens: &[usize], script: &Script, default: BookingMethod) -> (String, Vec<Directive>) {
    let mut text = String::from("2020-01-01 open Assets:Cash\n2020-01-01 open Income:PnL\n");
    for (i, &m) in opens.iter().enumerate() {
        match OPEN_METHODS[m] {
            Some(method) => text.push_str(&format!("2020-01-01 open Assets:A{i} \"{method}\"\n")),
            None => text.push_str(&format!("2020-01-01 open Assets:A{i}\n")),
        }
    }
    let mut accepted = book(&text, default).expect("the opens book");
    let mut k = 0;
    for (account, commodity, op) in script {
        let candidate = text.clone() + &transaction(k, account % opens.len(), *commodity, op);
        if let Some(booked) = book(&candidate, default) {
            text = candidate;
            accepted = booked;
            k += 1;
        }
    }
    (text, accepted)
}

/// A position as compared: units, commodity, and its cost if any.
type Lot = (String, Decimal, Option<(Decimal, String, Option<String>)>);

fn lots(inv: &Inventory) -> Vec<Lot> {
    let mut lots: Vec<Lot> = inv
        .positions()
        .filter(|p| !p.units.number.is_zero())
        .map(|p| {
            (
                p.units.currency.to_string(),
                p.units.number.normalize(),
                p.cost.as_ref().map(|c| {
                    (
                        c.number.normalize(),
                        c.currency.to_string(),
                        c.date.map(|d| d.to_string()),
                    )
                }),
            )
        })
        .collect();
    lots.sort();
    lots
}

fn per_account(
    directives: &[Directive],
    default: BookingMethod,
    bql: &str,
) -> Result<BTreeMap<String, Inventory>, String> {
    let mut executor = Executor::new(directives);
    executor.set_booking_method(default);
    let result = executor
        .execute(&parse(bql).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    Ok(result
        .rows
        .iter()
        .filter_map(|row| match (&row[0], &row[1]) {
            (Value::String(a), Value::Inventory(inv)) => Some((a.clone(), (**inv).clone())),
            _ => None,
        })
        .collect())
}

static REALIZED_AVERAGE: AtomicUsize = AtomicUsize::new(0);
static MIXED_AVERAGE: AtomicUsize = AtomicUsize::new(0);
static UNREALIZABLE: AtomicUsize = AtomicUsize::new(0);

proptest! {
    // 256 by default; `PROPTEST_CASES` overrides it for a longer search.
    #![proptest_config(ProptestConfig {
        cases: std::env::var("PROPTEST_CASES").ok().and_then(|n| n.parse().ok()).unwrap_or(256),
        ..ProptestConfig::default()
    })]

    #[test]
    fn sum_position_agrees_with_balances(
        opens in prop::collection::vec(0usize..4, 1..4),
        default in 0usize..3,
        script in prop::collection::vec((0usize..3, 0usize..2, op()), 1..14),
    ) {
        let default = DEFAULTS[default];
        let (text, directives) = ledger(&opens, &script, default);
        for from in FILTERS {
            let Ok(balances) = per_account(&directives, default, &format!("BALANCES{from}")) else {
                // A subset booking cannot realize: BALANCES refuses it and
                // `sum(position)` keeps the plain sum. Not both defined.
                UNREALIZABLE.fetch_add(1, Ordering::Relaxed);
                continue;
            };
            // The filter as FROM, and as a WHERE on the same transaction
            // attributes, which keeps the same postings.
            let filtered = [from.to_owned(), from.replace(" FROM ", " WHERE ")];
            for filter in &filtered {
            let sums = per_account(
                &directives,
                default,
                &format!("SELECT account, sum(position){filter} GROUP BY account"),
            )
            .expect("sum(position) runs whenever BALANCES does");
            for (account, balance) in &balances {
                let Some(index) = account.strip_prefix("Assets:A") else { continue };
                let index: usize = index.parse().expect("an A account");
                let average = OPEN_METHODS[opens[index]].map_or(
                    default == BookingMethod::Average,
                    |m| m == "AVERAGE",
                );
                let want = if average {
                    let mut pooled = balance.clone();
                    pooled.merge_average().expect("fits");
                    if lots(balance).iter().any(|l| l.1.is_sign_negative())
                        && lots(balance).iter().any(|l| l.1.is_sign_positive() && l.2.is_some())
                    {
                        MIXED_AVERAGE.fetch_add(1, Ordering::Relaxed);
                    }
                    REALIZED_AVERAGE.fetch_add(1, Ordering::Relaxed);
                    lots(&pooled)
                } else {
                    lots(balance)
                };
                let got = sums.get(account).map(lots).unwrap_or_default();
                prop_assert_eq!(
                    &got, &want,
                    "{} ({}){}\n{}", account, if average { "AVERAGE" } else { "lot" }, filter, text
                );
            }
            }
        }
    }
}

/// The property must actually reach realized AVERAGE accounts, mixed ones
/// among them; a generator whose ledgers booking always rejected would pass
/// it vacuously.
#[test]
fn the_generator_reaches_mixed_average_accounts() {
    sum_position_agrees_with_balances();
    let realized = REALIZED_AVERAGE.load(Ordering::Relaxed);
    let mixed = MIXED_AVERAGE.load(Ordering::Relaxed);
    eprintln!(
        "realized AVERAGE accounts: {realized}, mixed: {mixed}, unrealizable subsets: {}",
        UNREALIZABLE.load(Ordering::Relaxed)
    );
    assert!(realized > 200, "only {realized} realized AVERAGE accounts");
    assert!(
        mixed > 10,
        "only {mixed} AVERAGE accounts held a long and a short"
    );
}
