//! Property: MIN and MAX are the first and last value ORDER BY gives (#2447).
//!
//! Generated ledgers hold groups (accounts) of mixed values: amounts in up to
//! four currencies, positions with and without cost, prices that are NULL on
//! most postings, and per-account inventories. For each operand, MIN/MAX over
//! a group must equal the first/last non-NULL value of the same group under
//! ORDER BY, on the default table and through a subquery. An operand route
//! that compared values some other way would break it.

use proptest::prelude::*;
use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive};
use rustledger_query::{Executor, Value, parse};

/// One posting: units number (never zero), currency index, whether it has a
/// cost (X only, positive only) and whether it has a price (EUR only).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Leg {
    number: i64,
    currency: usize,
}

const CURRENCIES: [&str; 4] = ["USD", "EUR", "X", "Y"];

fn leg() -> impl Strategy<Value = Leg> {
    (1i64..9, any::<bool>(), 0usize..4).prop_map(|(n, neg, currency)| {
        // X is held at cost, so it is only ever bought: a sale would need a
        // lot to reduce.
        let number = if neg && currency != 2 { -n } else { n };
        Leg { number, currency }
    })
}

fn ledger() -> impl Strategy<Value = String> {
    prop::collection::vec(prop::collection::vec(leg(), 1..6), 1..4).prop_map(|groups| {
        let mut text = String::from("2024-01-01 open Equity:Open\n");
        let mut day = 1;
        for (g, legs) in groups.iter().enumerate() {
            text.push_str(&format!("2024-01-01 open Assets:G{g}\n"));
            // Distinct legs only: two lots differing in nothing but their
            // date tie under ORDER BY without being equal values.
            let mut legs = legs.clone();
            legs.sort();
            legs.dedup();
            for leg in &legs {
                day += 1;
                let currency = CURRENCIES[leg.currency];
                let annotation = match currency {
                    "X" => format!(" {{{} USD}}", leg.number + 10),
                    "EUR" if leg.number > 0 => " @ 1.5 USD".to_string(),
                    _ => String::new(),
                };
                text.push_str(&format!(
                    "2024-02-{day:02} * \"t\"\n  Assets:G{g}  {} {currency}{annotation}\n  Equity:Open\n",
                    leg.number
                ));
            }
        }
        text
    })
}

fn run(ledger: &str, bql: &str) -> Vec<Vec<Value>> {
    let parsed = rustledger_parser::parse(ledger);
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(BookingMethod::Strict);
    engine.register_account_methods(directives.iter());
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            engine
                .book_interpolate_apply(txn)
                .unwrap_or_else(|e| panic!("fixture books: {e:?}\n{ledger}"));
        }
    }
    let query = parse(bql).unwrap_or_else(|e| panic!("{bql}: {e:?}"));
    Executor::new(&directives)
        .execute(&query)
        .unwrap_or_else(|e| panic!("{bql}: {e}\n{ledger}"))
        .rows
}

/// Per account, the first and last non-NULL value of `column` under ORDER BY.
fn order_by_ends(ledger: &str, column: &str) -> Vec<(Value, Value, Value)> {
    let ordered = run(
        ledger,
        &format!("SELECT account, {column} AS v ORDER BY account, v"),
    );
    let accounts = run(ledger, "SELECT DISTINCT account ORDER BY account");
    accounts
        .iter()
        .map(|a| {
            let vals: Vec<&Value> = ordered
                .iter()
                .filter(|r| r[0] == a[0] && r[1] != Value::Null)
                .map(|r| &r[1])
                .collect();
            let first = vals.first().map_or(Value::Null, |v| (*v).clone());
            let last = vals.last().map_or(Value::Null, |v| (*v).clone());
            (a[0].clone(), first, last)
        })
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn min_max_equal_order_by_ends(ledger in ledger()) {
        for column in ["units(position)", "position", "cost(position)", "price", "number"] {
            let expected = order_by_ends(&ledger, column);
            for bql in [
                format!("SELECT account, min({column}), max({column}) GROUP BY account ORDER BY account"),
                format!(
                    "SELECT account, min(v), max(v) FROM (SELECT account, {column} AS v) \
                     GROUP BY account ORDER BY account"
                ),
            ] {
                let got: Vec<(Value, Value, Value)> = run(&ledger, &bql)
                    .into_iter()
                    .map(|r| (r[0].clone(), r[1].clone(), r[2].clone()))
                    .collect();
                prop_assert_eq!(&got, &expected, "{}\n{}", bql, ledger);
            }
        }

        // Inventories: per-account sums from a subquery, aggregated again.
        let inner = "SELECT account, sum(position) AS s GROUP BY account";
        let ordered = run(&ledger, &format!("SELECT s FROM ({inner}) ORDER BY s"));
        let got = run(&ledger, &format!("SELECT min(s), max(s) FROM ({inner})"));
        prop_assert_eq!(
            &got,
            &vec![vec![ordered.first().unwrap()[0].clone(), ordered.last().unwrap()[0].clone()]],
            "{}", ledger
        );
    }
}
