//! A lot's sales add up to exactly what it cost (#2425).
//!
//! `3 X {{500 USD}}` resolves to a per-unit cost of 500/3, which `Decimal`
//! rounds to 166.6666666666666666666666667, and `3 ×` that is not 500. A lot
//! kept only that per-unit cost, so selling it whole was booked at
//! 500.0000000000000000000000001 and failed against `500 USD` with `residual
//! -1E-26 USD`; sold down in parts, the last sale carried the drift. The
//! inventory now keeps the lot's exact total: a partial sale takes `units ×
//! per-unit` and the lot keeps the rest, which the sale that empties it takes.

use rustledger_core::{Decimal, Directive};
use rustledger_loader::{Ledger, LoadOptions, load};
use std::collections::BTreeMap;
use std::io::Write;

fn load_source(source: &str) -> Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("lot-exact-total-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let options = LoadOptions {
        collect_capital_gains: true,
        ..LoadOptions::default()
    };
    load(f.path(), &options).expect("the ledger loads")
}

/// `value` as an integer count of 1e-28, so sums of 28-digit numbers are
/// exact: adding them as `Decimal`s rounds whenever the sum needs a 29th
/// digit, which would blur exactly the drift these tests look for. Scaled in
/// `i128`, since a `Decimal` above ~7.9 cannot itself hold 28 decimals.
const fn exact(value: Decimal) -> i128 {
    let shift = 28 - value.scale();
    value
        .mantissa()
        .checked_mul(10_i128.pow(shift))
        .expect("the test's values fit in i128 at scale 28")
}

/// The sum of what every booked posting to `account` weighs, by the balance
/// check's own rule, as [`exact`] units.
fn weight_sum(ledger: &Ledger, account: &str) -> i128 {
    ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .flat_map(|t| t.postings.iter())
        .filter(|p| p.account.as_str() == account)
        .map(|p| {
            let units = p.amount().expect("booked units").number;
            let number = p
                .cost
                .as_deref()
                .and_then(|c| c.number)
                .expect("a booked cost");
            exact(rustledger_booking::cost_number_weight(units, &number).expect("fits in Decimal"))
        })
        .sum()
}

/// The issue's ledger: a `{{500 USD}}` lot sold whole for `500 USD`.
#[test]
fn a_whole_total_cost_lot_sold_at_its_total_balances() {
    let ledger = load_source(
        r#"2024-01-01 open Assets:B X "FIFO"
2024-01-01 open Assets:C

2024-01-02 * "buy"
  Assets:B  3 X {{500 USD}}
  Assets:C

2024-02-01 * "sell the whole lot"
  Assets:B  -3 X {}
  Assets:C  500 USD
"#,
    );
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    assert_eq!(weight_sum(&ledger, "Assets:B"), 0);
}

/// Deterministic pseudo-random numbers, so the sweep's ledger is the same on
/// every run.
struct Lcg(u64);

impl Lcg {
    const fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % n
    }
}

/// 200 accounts of one to three `{{T}}` lots (long and short, FIFO and
/// AVERAGE), each sold down in one to four sales. Most of these totals do
/// not divide evenly by their units. For every account the booked weights
/// net to exactly zero and the realized lot values add up to exactly what
/// the lots cost. A covered short realizes its lot value as the gain's
/// proceeds, since the roles swap.
///
/// Totals run up to 999,999. A partial sale's basis is fitted to the lot's
/// total, so every remainder stays exact however many integer digits the
/// total has; without that, 79 of 600 such sell-downs missed by up to 1E-23.
#[test]
fn every_generated_lot_sold_down_realizes_exactly_its_total() {
    let mut rng = Lcg(0x2425);
    let mut source = String::from("2024-01-01 open Assets:C\n2024-01-01 open Income:G\n");
    let mut expected: BTreeMap<String, i128> = BTreeMap::new();
    for i in 0..200_u64 {
        let method = if i % 2 == 0 { "FIFO" } else { "AVERAGE" };
        let sign: i64 = if i % 4 >= 2 { -1 } else { 1 };
        let account = format!("Assets:P{i}");
        let commodity = format!(
            "X{}{}",
            char::from(b'A' + u8::try_from(i % 26).unwrap()),
            char::from(b'A' + u8::try_from(i / 26).unwrap())
        );
        source.push_str(&format!(
            "2024-01-01 open {account} {commodity} \"{method}\"\n"
        ));
        let mut units_held: i64 = 0;
        let mut cost: i64 = 0;
        for k in 0..=rng.below(3) {
            let units = 2 + rng.below(29) as i64;
            let total = 1 + rng.below(999_999) as i64;
            source.push_str(&format!(
                "2024-01-{:02} * \"lot\"\n  {account}  {} {commodity} {{{{{total} USD}}}}\n  Assets:C\n",
                k + 2,
                sign * units
            ));
            units_held += units;
            cost += total;
        }
        let sales = 1 + rng.below(4) as i64;
        let mut left = units_held;
        for n in 0..sales {
            let take = if n + 1 == sales {
                left
            } else {
                (1 + rng.below(left as u64) as i64).min(left - (sales - n - 1))
            };
            if take <= 0 {
                continue;
            }
            left -= take;
            source.push_str(&format!(
                "2024-02-{:02} * \"sell {i}\"\n  {account}  {} {commodity} {{}} @ 1000 USD\n  Assets:C  {} USD\n  Income:G\n",
                n + 1,
                -sign * take,
                sign * take * 1000
            ));
        }
        assert_eq!(left, 0, "the sales take every unit");
        expected.insert(account, exact(Decimal::from(cost)));
    }

    let ledger = load_source(&source);
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);

    for account in expected.keys() {
        assert_eq!(
            weight_sum(&ledger, account),
            0,
            "{account}: the lots' purchases and sales net to exactly zero"
        );
    }

    let mut realized: BTreeMap<String, i128> = BTreeMap::new();
    for g in &ledger.capital_gains {
        let lot_value = if g.short_sale {
            &g.proceeds
        } else {
            &g.cost_basis
        };
        *realized.entry(g.account.to_string()).or_default() += exact(lot_value.number);
    }
    assert_eq!(
        realized, expected,
        "each account realizes exactly what its lots cost"
    );
}

/// A sale that empties a lot or pool in one posting takes exactly what it
/// cost, at any magnitude: 200 accounts of one to three `{{T}}` lots of up
/// to 999,999, long and short, FIFO and AVERAGE, each sold whole.
#[test]
fn every_whole_sale_is_exact() {
    let mut rng = Lcg(0x2425_0001);
    let mut source = String::from("2024-01-01 open Assets:C\n");
    let mut accounts = Vec::new();
    for i in 0..200_u64 {
        let method = if i % 2 == 0 { "FIFO" } else { "AVERAGE" };
        let sign: i64 = if i % 4 >= 2 { -1 } else { 1 };
        let account = format!("Assets:W{i}");
        let commodity = format!(
            "X{}{}",
            char::from(b'A' + u8::try_from(i % 26).unwrap()),
            char::from(b'A' + u8::try_from(i / 26).unwrap())
        );
        source.push_str(&format!(
            "2024-01-01 open {account} {commodity} \"{method}\"\n"
        ));
        let mut units_held: i64 = 0;
        let mut cost: i64 = 0;
        for k in 0..=rng.below(3) {
            let units = 2 + rng.below(29) as i64;
            let total = 1 + rng.below(999_999) as i64;
            source.push_str(&format!(
                "2024-01-{:02} * \"lot\"\n  {account}  {} {commodity} {{{{{total} USD}}}}\n  Assets:C\n",
                k + 2,
                sign * units
            ));
            units_held += units;
            cost += total;
        }
        // Sold for exactly what the lots cost, in whole dollars: no
        // tolerance, so any residual at all is an error.
        source.push_str(&format!(
            "2024-02-01 * \"sell {i}\"\n  {account}  {} {commodity} {{}}\n  Assets:C  {} USD\n",
            -sign * units_held,
            sign * cost
        ));
        accounts.push(account);
    }

    let ledger = load_source(&source);
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    for account in &accounts {
        assert_eq!(weight_sum(&ledger, account), 0, "{account}");
    }
}
