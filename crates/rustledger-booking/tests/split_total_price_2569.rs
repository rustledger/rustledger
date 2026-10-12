//! A total price (`@@`) on a reduction that booking splits across several
//! lots (#2569).
//!
//! Booking turns a reduction that takes from several lots into one posting per
//! lot. Each split used to keep the written `@@ T`, and `normalize_prices` then
//! divided it by the split's OWN units: 1000 units sold for 6000.00 USD across
//! two lots of 500 showed `@ 12.00` on both. Beancount 3.2 converts `@@` to a
//! per-unit price in its parser, before booking, so each split carries
//! `T / |units sold|` = 6.00, and that is the sale's price: the BQL `price`
//! column, `implicit_prices` and plugins all read it.
//!
//! Each split now carries `@ T / |units sold|`, divided once by the rule an
//! unsplit posting's `@@` goes through (`rustledger_core::per_unit_price`).

use rust_decimal_macros::dec;
use rustledger_booking::{BookingEngine, normalize_prices};
use rustledger_core::{
    Amount, BookingMethod, CostNumber, CostSpec, Decimal, IncompleteAmount, Posting,
    PriceAnnotation, PriceKind, Transaction,
};

fn txn(day: u32, postings: Vec<Posting>) -> Transaction {
    let date = rustledger_core::naive_date(2020, 1, day).expect("valid date");
    postings.into_iter().fold(
        Transaction::new(date, "t"),
        Transaction::with_synthesized_posting,
    )
}

fn buy(day: u32, n: Decimal, cost: Decimal) -> Transaction {
    txn(
        day,
        vec![
            Posting::new("Assets:B", Amount::new(n, "X")).with_cost(
                CostSpec::empty()
                    .with_number(CostNumber::PerUnit { value: cost })
                    .with_currency("USD"),
            ),
            Posting::auto("Equity:Opening"),
        ],
    )
}

/// `-sold X {} @@ total USD`, cash for the total, gains elided.
fn sale(sold: Decimal, total: Decimal) -> Transaction {
    txn(
        28,
        vec![
            Posting::new("Assets:B", Amount::new(-sold, "X"))
                .with_cost(CostSpec::empty())
                .with_price(PriceAnnotation::total(Amount::new(total, "USD"))),
            Posting::new("Assets:Cash", Amount::new(total, "USD")),
            Posting::auto("Income:G"),
        ],
    )
}

/// Book the buys, then the sale; return the sale's split `Assets:B` postings
/// as `(units, price kind, price number)` after `normalize_prices`, the
/// loader's finalize step.
fn split_prices(
    method: BookingMethod,
    lots: &[(Decimal, Decimal)],
    sold: Decimal,
    total: Decimal,
) -> Vec<(Decimal, PriceKind, Decimal)> {
    let mut engine = BookingEngine::with_method(method);
    for (day, (n, cost)) in (1..).zip(lots) {
        engine
            .book_interpolate_apply(&mut buy(day, *n, *cost))
            .expect("buy books");
    }
    let mut sale = sale(sold, total);
    engine
        .book_interpolate_apply(&mut sale)
        .expect("the sale books");
    normalize_prices(&mut sale);
    sale.postings
        .iter()
        .filter(|p| p.account.as_str() == "Assets:B")
        .map(|p| {
            let price = p.price.as_deref().expect("every split keeps a price");
            let amount = price
                .amount
                .as_ref()
                .and_then(IncompleteAmount::as_amount)
                .expect("a complete price");
            assert_eq!(amount.currency.as_str(), "USD");
            (p.amount().expect("units").number, price.kind, amount.number)
        })
        .collect()
}

#[test]
fn the_issue_case_prices_each_split_at_the_whole_sale_per_unit() {
    let splits = split_prices(
        BookingMethod::Fifo,
        &[(dec!(500), dec!(10.00)), (dec!(500), dec!(20.00))],
        dec!(1000),
        dec!(6000.00),
    );
    assert_eq!(splits.len(), 2, "the sale splits into two postings");
    for (units, kind, price) in &splits {
        assert_eq!(*units, dec!(-500));
        assert_eq!(*kind, PriceKind::Unit);
        // Beancount 3.2: `price= 6.00 USD` on both booked postings.
        assert_eq!(price.to_string(), "6.00", "not 6000.00 / 500 = 12.00");
    }
}

/// Every split shows the price an UNSPLIT sale of the same units at the same
/// total shows, whatever the lot sizes and however the total divides.
#[test]
fn every_split_shows_the_unsplit_sale_price() {
    let cases: &[(&[(Decimal, Decimal)], Decimal, Decimal)] = &[
        // Uneven lots, a total that does not divide evenly.
        (
            &[(dec!(1), dec!(5)), (dec!(2), dec!(6)), (dec!(4), dec!(7))],
            dec!(7),
            dec!(1000.00),
        ),
        // 6000.01 over 1000: exact, 6.00001.
        (
            &[(dec!(250), dec!(5)), (dec!(750), dec!(6))],
            dec!(1000),
            dec!(6000.01),
        ),
        // A partial sale larger than any one lot, so every method splits
        // it, with fractional units.
        (
            &[
                (dec!(0.5), dec!(5)),
                (dec!(1.25), dec!(6)),
                (dec!(3), dec!(7)),
            ],
            dec!(4),
            dec!(10),
        ),
        // N lots.
        (
            &[
                (dec!(1), dec!(1)),
                (dec!(1), dec!(2)),
                (dec!(1), dec!(3)),
                (dec!(1), dec!(4)),
                (dec!(1), dec!(5)),
                (dec!(1), dec!(6)),
            ],
            dec!(6),
            dec!(100.00),
        ),
    ];
    for method in [
        BookingMethod::Fifo,
        BookingMethod::Lifo,
        BookingMethod::Hifo,
        BookingMethod::Strict,
    ] {
        for (lots, sold, total) in cases {
            // STRICT sells only every lot a `{}` spec matches.
            let lots_total: Decimal = lots.iter().map(|(n, _)| *n).sum();
            if method == BookingMethod::Strict && *sold != lots_total {
                continue;
            }
            let unsplit = split_prices(method, &[(*sold, dec!(1))], *sold, *total);
            assert_eq!(unsplit.len(), 1);
            let (_, unsplit_kind, unsplit_price) = unsplit[0];
            assert_eq!(unsplit_kind, PriceKind::Unit);

            let splits = split_prices(method, lots, *sold, *total);
            assert!(splits.len() > 1, "{method:?} {lots:?}: the sale splits");
            let split_units: Decimal = splits.iter().map(|(u, _, _)| *u).sum();
            assert_eq!(split_units, -*sold, "{method:?} {lots:?}");
            for (units, kind, price) in &splits {
                assert_eq!(*kind, PriceKind::Unit, "{method:?} {lots:?} {units}");
                assert_eq!(
                    price.to_string(),
                    unsplit_price.to_string(),
                    "{method:?} {lots:?}: the split of {units} shows the sale's price"
                );
            }
        }
    }
}

/// When `T / |units sold|` cannot be represented, each split carries its
/// exact pro-rata share of the total as its own `@@`, so the splits still
/// add up to what the sale fetched instead of each claiming all of it.
#[test]
fn an_unrepresentable_per_unit_price_keeps_each_splits_share_of_the_total() {
    // Overflow: 7e27 over 0.01 units is 7e29 per unit, past `Decimal::MAX`
    // (~7.9e28).
    let splits = split_prices(
        BookingMethod::Fifo,
        &[(dec!(0.004), dec!(1)), (dec!(0.006), dec!(1))],
        dec!(0.01),
        dec!(7000000000000000000000000000),
    );
    assert_eq!(splits.len(), 2);
    let shares: Vec<String> = splits
        .iter()
        .map(|(_, kind, price)| {
            assert_eq!(*kind, PriceKind::Total, "the share stays a total");
            price.to_string()
        })
        .collect();
    assert_eq!(
        shares,
        // `prorate`'s scale is Python's ideal exponent: 0 + 3 - 2 places.
        [
            "2800000000000000000000000000.0",
            "4200000000000000000000000000.0"
        ]
    );

    // Underflow: 0.01 over 1e27 units is 1e-29 per unit, which `Decimal`
    // rounds to 0 without failing. A zero price for money paid is invented.
    let splits = split_prices(
        BookingMethod::Fifo,
        &[
            (dec!(400000000000000000000000000), dec!(0)),
            (dec!(600000000000000000000000000), dec!(0)),
        ],
        dec!(1000000000000000000000000000),
        dec!(0.01),
    );
    let shares: Vec<(PriceKind, String)> = splits
        .iter()
        .map(|(_, kind, price)| (*kind, price.to_string()))
        .collect();
    assert_eq!(
        shares,
        [
            (PriceKind::Total, "0.004".to_string()),
            (PriceKind::Total, "0.006".to_string())
        ]
    );
}

/// An unsplit `@@` that underflows is left as written by `normalize_prices`
/// rather than becoming a price of zero.
#[test]
fn normalize_prices_keeps_a_total_that_underflows() {
    let mut t = txn(
        1,
        vec![
            Posting::new(
                "Assets:B",
                Amount::new(dec!(1000000000000000000000000000), "X"),
            )
            .with_price(PriceAnnotation::total(Amount::new(dec!(0.01), "USD"))),
            Posting::auto("Assets:Cash"),
        ],
    );
    normalize_prices(&mut t);
    let price = t.postings[0].price.as_deref().expect("price kept");
    assert_eq!(price.kind, PriceKind::Total);
    assert_eq!(
        price.amount.as_ref().and_then(IncompleteAmount::as_amount),
        Some(&Amount::new(dec!(0.01), "USD"))
    );
}
