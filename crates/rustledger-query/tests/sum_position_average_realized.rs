//! `sum(position)` over an AVERAGE account is realized through booking, the
//! way `BALANCES` realizes it (#2394).
//!
//! It used to sum the postings and pool every cost-bearing lot of the
//! commodity. A sale is a negative lot in that sum, and so is a short, so on
//! an account holding a long and a short the pool netted one into the other
//! and printed a lot nobody held. Python beancount has no AVERAGE booking
//! (`AVERAGE method is not supported`), so the reference here is rledger's
//! own `BALANCES`, which realizes through `BookingEngine::replay_transaction`.

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Decimal, Directive};
use rustledger_query::{Executor, Value, parse};
use std::str::FromStr;

/// Parse `source` and book it the way the loader does, with `default` for
/// accounts that declare no method.
fn booked(source: &str, default: BookingMethod) -> Vec<Directive> {
    let parsed = rustledger_parser::parse(source);
    assert!(
        parsed.errors.is_empty(),
        "fixture parses: {:?}",
        parsed.errors
    );
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(default);
    engine.register_account_methods(directives.iter());
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            engine
                .book_interpolate_apply(txn)
                .expect("the fixture books");
        }
    }
    directives
}

/// The `X` lots of the single inventory cell in `bql`'s only row, as
/// `(units, per-unit cost)`, sorted.
fn lots(directives: &[Directive], default: BookingMethod, bql: &str) -> Vec<(Decimal, Decimal)> {
    let mut executor = Executor::new(directives);
    executor.set_booking_method(default);
    let result = executor
        .execute(&parse(bql).expect("query parses"))
        .expect("query runs");
    assert_eq!(result.rows.len(), 1, "one row for the account: {bql}");
    let inv = result.rows[0]
        .iter()
        .find_map(|v| match v {
            Value::Inventory(inv) => Some(inv.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("an inventory cell: {:?}", result.rows[0]));
    let mut lots: Vec<(Decimal, Decimal)> = inv
        .positions()
        .filter(|p| p.units.currency.as_str() == "X")
        .map(|p| {
            (
                p.units.number,
                p.cost.as_ref().expect("a lot at cost").number,
            )
        })
        .collect();
    lots.sort();
    lots
}

fn d(s: &str) -> Decimal {
    Decimal::from_str(s).expect("literal")
}

const SUM: &str = "SELECT account, sum(position) WHERE account = 'Assets:Stock' GROUP BY account";
const BALANCES: &str = "BALANCES WHERE account = 'Assets:Stock'";

/// The issue's ledger: a short at 101 and a long at 102, then a sale from
/// the long pool. The sum reported `1 X {104 USD}`, a lot the account never
/// held; booking holds `3 X {102}` and `-2 X {101}`.
#[test]
fn a_long_and_a_short_stay_two_pools() {
    let ledger = booked(
        r#"
2020-01-01 open Assets:Stock X "AVERAGE"
2020-01-01 open Assets:Cash
2020-01-01 open Income:PnL

2020-01-01 * "a short at 101 and a long at 102"
  Assets:Stock  -2 X {101 USD}
  Assets:Stock   5 X {102 USD}
  Assets:Cash  -308 USD

2020-01-05 * "sell 2 from the long pool"
  Assets:Stock  -2 X {} @ 110 USD
  Assets:Cash   220 USD
  Income:PnL
"#,
        BookingMethod::Strict,
    );
    let sum = lots(&ledger, BookingMethod::Strict, SUM);
    assert_eq!(sum, vec![(d("-2"), d("101")), (d("3"), d("102"))]);
    assert_eq!(sum, lots(&ledger, BookingMethod::Strict, BALANCES));
}

/// A posting-level `FROM` (#2414) that keeps some of an AVERAGE account's
/// postings and not others (the `Y` buy is left out): `BALANCES` is then the
/// selected postings' sum as `sum(position)` computes it, on an account
/// holding two longs, a short, and a sale from the long pool.
#[test]
fn a_partly_selected_account_is_realized_like_the_sum() {
    let ledger = booked(
        r#"
2020-01-01 open Assets:Stock "AVERAGE"
2020-01-01 open Assets:Cash
2020-01-01 open Income:PnL

2020-01-01 * "two longs and a short"
  Assets:Stock  10 X {100 USD}
  Assets:Stock  10 X {110 USD}
  Assets:Stock  -2 X {101 USD}
  Assets:Cash

2020-01-05 * "sell 2 from the long pool"
  Assets:Stock  -2 X {} @ 120 USD
  Assets:Cash   240 USD
  Income:PnL

2020-02-01 * "a buy of another commodity, which the filter leaves out"
  Assets:Stock   1 Y {200 USD}
  Assets:Cash  -200 USD
"#,
        BookingMethod::Strict,
    );
    let from = "FROM currency = 'X' AND account = 'Assets:Stock'";
    let balances = lots(&ledger, BookingMethod::Strict, &format!("BALANCES {from}"));
    assert_eq!(balances, vec![(d("-2"), d("101")), (d("18"), d("105"))]);
    assert_eq!(
        balances,
        lots(
            &ledger,
            BookingMethod::Strict,
            &format!("SELECT account, sum(position) {from} GROUP BY account")
        )
    );
}

const TWO_BUYS_ONE_SALE: &str = r#"
2020-01-01 open Assets:Stock X "AVERAGE"
2020-01-01 open Assets:Cash
2020-01-01 open Income:PnL
2020-01-01 * "b1"
  Assets:Stock  10 X {100 USD}
  Assets:Cash
2020-02-01 * "b2"
  Assets:Stock  10 X {110 USD}
  Assets:Cash
2021-01-05 * "sell"
  Assets:Stock  -14 X {} @ 120 USD
  Assets:Cash   1680 USD
  Income:PnL
"#;

/// The single-sided case the old pooling already got right, kept right.
#[test]
fn a_single_sided_pool_is_unchanged() {
    let ledger = booked(TWO_BUYS_ONE_SALE, BookingMethod::Strict);
    let sum = lots(&ledger, BookingMethod::Strict, SUM);
    assert_eq!(sum, vec![(d("6"), d("105"))]);
    assert_eq!(sum, lots(&ledger, BookingMethod::Strict, BALANCES));
}

/// AVERAGE from `option "booking_method"`, with no method on the `open`.
/// Only the open's method was read, so the sale's lot was left beside the
/// lots it sold from: `10 {100}`, `10 {110}` and `-14 {105}`.
#[test]
fn the_ledger_default_method_counts() {
    let source = TWO_BUYS_ONE_SALE.replace(" X \"AVERAGE\"", "");
    let ledger = booked(&source, BookingMethod::Average);
    let sum = lots(&ledger, BookingMethod::Average, SUM);
    assert_eq!(sum, vec![(d("6"), d("105"))]);
    assert_eq!(sum, lots(&ledger, BookingMethod::Average, BALANCES));
}

/// A WHERE that keeps a sale but not what it sold from leaves booking
/// nothing to realize: 2 units bought in 2021 cannot cover a sale of 14. The
/// plain sum stands, each posting's lot as it was booked, rather than a pool
/// netting the sale into the buy (`-12 X {103.48…}`).
#[test]
fn a_subset_booking_cannot_realize_keeps_the_plain_sum() {
    let source = TWO_BUYS_ONE_SALE.replace(
        "2021-01-05 * \"sell\"",
        "2021-01-01 * \"b3\"\n  Assets:Stock  2 X {130 USD}\n  Assets:Cash\n2021-01-05 * \"sell\"",
    );
    assert!(source.contains("b3"), "the buy is spliced in");
    let ledger = booked(&source, BookingMethod::Strict);
    let sum = lots(
        &ledger,
        BookingMethod::Strict,
        "SELECT account, sum(position) WHERE account = 'Assets:Stock' AND year = 2021 \
         GROUP BY account",
    );
    // The sale was booked at the whole pool's 2360 / 22.
    let booked_at = d("107.27272727272727272727272727");
    assert_eq!(sum, vec![(d("-14"), booked_at), (d("2"), d("130"))]);
}
