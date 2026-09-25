//! Selling a whole AVERAGE or `{*}` pool balances exactly (#2417).
//!
//! 1 X at 100 and 2 X at 200 average 166.66…, which `Decimal` rounds. Booking
//! priced a sale of all three at `3 × 166.6666666666666666666666667`, which
//! is 500.00…01, so a sale for `500 USD`, whose whole-dollar amounts infer no
//! tolerance, failed to balance by 1E-26 USD. The lots cost exactly 500, and
//! that is the basis a sale of all of them takes, in the balance and in the
//! realized gain alike.

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

fn ledger(method: &str, spec: &str) -> String {
    format!(
        r#"2024-01-01 open Assets:B X "{method}"
2024-01-01 open Assets:C
2024-01-01 open Income:G

2024-01-02 * "a"
  Assets:B  1 X {{100 USD}}
  Assets:C

2024-01-03 * "b"
  Assets:B  2 X {{200 USD}}
  Assets:C

2024-02-01 * "sell the whole pool"
  Assets:B  -3 X {spec} @ 200 USD
  Assets:C  600 USD
  Income:G  -100 USD
"#
    )
}

fn load_source(source: &str) -> rustledger_loader::Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("whole-pool-")
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

#[test]
fn a_whole_pool_sale_balances_and_realizes_the_exact_basis() {
    for (method, spec) in [("AVERAGE", "{}"), ("FIFO", "{*}")] {
        let ledger = load_source(&ledger(method, spec));
        assert!(
            ledger.errors.is_empty(),
            "{method} {spec}: the lots cost exactly 500; got {:?}",
            ledger.errors
        );

        let sale = ledger
            .directives
            .iter()
            .filter_map(|d| match &d.value {
                Directive::Transaction(t) if t.narration.as_str() == "sell the whole pool" => {
                    Some(t)
                }
                _ => None,
            })
            .flat_map(|t| t.postings.iter())
            .find(|p| p.account.as_str() == "Assets:B")
            .expect("the sale");
        let number = sale
            .cost
            .as_deref()
            .and_then(|c| c.number)
            .expect("booked cost");
        assert_eq!(
            number.total(),
            Some(rustledger_core::Decimal::from(500)),
            "{method} {spec}: the booked cost carries the exact total"
        );

        let basis: Vec<_> = ledger
            .capital_gains
            .iter()
            .map(|g| g.cost_basis.number)
            .collect();
        assert_eq!(
            basis,
            vec![rustledger_core::Decimal::from(500)],
            "{method} {spec}: the realized basis is the exact total"
        );
    }
}

/// The same, over 200 generated pools: long and short, AVERAGE and `{*}`,
/// two to four lots of 1–30 units at 1–999 USD, each sold whole at a price.
/// About one in twenty of these pools has an average that `3 × 166.66…67`
/// style rounding throws off; the pre-fix build failed 13 of 240 in the
/// review sweep. Every sale must balance, and every realized basis must be
/// the lots' exact total (its proceeds, for a covered short). A fixed linear congruential generator keeps the
/// ledger the same on every run.
#[test]
fn every_generated_whole_pool_sale_balances_and_realizes_its_exact_total() {
    let mut state: u64 = 0x2417;
    let mut next = |n: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % n
    };
    let mut source = String::from("2024-01-01 open Assets:C\n2024-01-01 open Income:G\n");
    let mut expected = std::collections::BTreeMap::new();
    for i in 0..200 {
        let (method, spec) = if i % 2 == 0 {
            ("AVERAGE", "{}")
        } else {
            ("FIFO", "{*}")
        };
        let sign: i64 = if i % 4 >= 2 { -1 } else { 1 };
        let lots: Vec<(i64, i64)> = (0..2 + next(3))
            .map(|_| (1 + next(30) as i64, 1 + next(999) as i64))
            .collect();
        let units: i64 = lots.iter().map(|(u, _)| u).sum();
        let total: i64 = lots.iter().map(|(u, c)| u * c).sum();
        let account = format!("Assets:P{i}");
        let commodity = format!(
            "X{}{}",
            (b'A' + (i % 26) as u8) as char,
            (b'A' + (i / 26) as u8) as char
        );
        source.push_str(&format!(
            "2024-01-01 open {account} {commodity} \"{method}\"\n"
        ));
        for (k, (u, c)) in lots.iter().enumerate() {
            source.push_str(&format!(
                "2024-01-{:02} * \"lot\"\n  {account}  {} {commodity} {{{c} USD}}\n  Assets:C\n",
                k + 2,
                sign * u
            ));
        }
        source.push_str(&format!(
            "2024-02-01 * \"sell {i}\"\n  {account}  {} {commodity} {spec} @ 1000 USD\n  Assets:C  {} USD\n  Income:G\n",
            -sign * units,
            sign * units * 1000
        ));
        expected.insert(account, rustledger_core::Decimal::from(total));
    }

    let ledger = load_source(&source);
    assert!(
        ledger.errors.is_empty(),
        "every whole-pool sale balances: {:?}",
        ledger.errors
    );
    // Covering a short swaps the roles: the lot's value is what the short
    // was sold for, so the pool's total is the gain's PROCEEDS there.
    let realized: std::collections::BTreeMap<_, _> = ledger
        .capital_gains
        .iter()
        .map(|g| {
            let lot_value = if g.short_sale {
                &g.proceeds
            } else {
                &g.cost_basis
            };
            (g.account.to_string(), lot_value.number)
        })
        .collect();
    assert_eq!(
        realized, expected,
        "each realized lot value is the pool's exact total"
    );
}
