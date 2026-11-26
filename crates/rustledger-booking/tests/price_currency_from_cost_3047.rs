//! A price written without a currency on a posting at cost takes the cost's
//! currency (#3047, reported by tomelliot).
//!
//! Beancount's `booking_full.categorize_by_currency` fills it ("price_currency
//! is MISSING and cost_currency is a str"), so `-2 STK {5 USD} @ 7` books with
//! the price `7 USD`. rledger kept a bare `NumberOnly` price, which every reader
//! of the price annotation (BQL's `price`, `implicit_prices`) saw as no price.
//!
//! Every case below was checked against beancount 3.2.3 (`bean-query ...
//! "SELECT position, price"`):
//!
//! | posting                          | beancount's booked price |
//! |----------------------------------|--------------------------|
//! | `-2 STK {5 USD, 2020-01-02} @ 7` | `7 USD`                  |
//! | `2 STK {5 USD} @ 6`              | `6 USD`                  |
//! | `-2 STK {...} @@ 14`             | `@@ 14 USD` (7 USD/unit) |
//! | `2 STK {5} @ 6` beside USD cash  | `6 USD`, cost `5 USD`    |
//! | `-2 STK {5} @ 7` beside USD cash | `7 USD`, cost `5 USD`    |
//! | `-2 STK {5 EUR} @ 7`, USD cash   | `7 EUR`                  |
//! | `2 STK {} @ 6` beside USD cash   | `6 USD`                  |
//! | `STK {5 USD} @ 6` (units elided) | `6 USD`                  |

use rust_decimal_macros::dec;
use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, CostNumber, CostSpec, Decimal, IncompleteAmount, Posting, PriceAnnotation, PriceKind,
    Transaction,
};

fn txn(day: u32, postings: Vec<Posting>) -> Transaction {
    let date = rustledger_core::naive_date(2020, 1, day).expect("valid date");
    postings.into_iter().fold(
        Transaction::new(date, "t"),
        Transaction::with_synthesized_posting,
    )
}

fn cash(account: &str, number: Decimal, currency: &str) -> Posting {
    Posting::new(account, Amount::new(number, currency))
}

/// `{<cost> <currency>}`, either part omitted with `None`.
fn spec(cost: Option<Decimal>, currency: Option<&str>) -> CostSpec {
    let s = CostSpec::empty();
    let s = match cost {
        Some(value) => s.with_number(CostNumber::PerUnit { value }),
        None => s,
    };
    match currency {
        Some(c) => s.with_currency(c),
        None => s,
    }
}

/// `Assets:S  <n> STK {<spec>}`.
fn stk(n: Decimal, spec: CostSpec) -> Posting {
    Posting::new("Assets:S", Amount::new(n, "STK")).with_cost(spec)
}

/// `@ <number>` (or `@@ <number>`), with no currency.
fn bare_number_price(kind: PriceKind, number: Decimal) -> PriceAnnotation {
    let amount = Some(IncompleteAmount::NumberOnly(number));
    PriceAnnotation { kind, amount }
}

/// The issue's opening lot: `2 STK {5 USD}` bought for `-10 USD`.
fn buy_usd() -> Transaction {
    txn(
        2,
        vec![
            stk(dec!(2), spec(Some(dec!(5)), Some("USD"))),
            cash("Assets:C", dec!(-10), "USD"),
        ],
    )
}

/// Book `history`, then `last` through both public entry points (which must
/// agree), and return `last`'s booked postings on `Assets:S` as
/// `(units, cost currency, price kind, price number, price currency)`.
fn booked_prices(
    history: Vec<Transaction>,
    last: Transaction,
) -> Vec<(Decimal, String, PriceKind, Decimal, String)> {
    let mut engine = BookingEngine::new();
    for mut t in history {
        engine
            .book_interpolate_apply(&mut t)
            .expect("history books");
    }
    let viewed = engine
        .book_and_interpolate(&last)
        .expect("book_and_interpolate books")
        .transaction;
    let mut applied = last;
    engine
        .book_interpolate_apply(&mut applied)
        .expect("book_interpolate_apply books");
    assert_eq!(
        viewed.postings, applied.postings,
        "book_and_interpolate and book_interpolate_apply disagree"
    );
    applied
        .postings
        .iter()
        .filter(|p| p.account.as_str() == "Assets:S")
        .map(|p| {
            let units = p.amount().expect("units booked");
            let cost_currency = p
                .cost
                .as_deref()
                .and_then(|c| c.currency.as_deref())
                .expect("cost currency booked")
                .to_owned();
            let price = p.price.as_deref().expect("price kept");
            let amount = price
                .amount
                .as_ref()
                .and_then(IncompleteAmount::as_amount)
                .unwrap_or_else(|| panic!("price left incomplete: {price:?}"));
            (
                units.number,
                cost_currency,
                price.kind,
                amount.number,
                amount.currency.to_string(),
            )
        })
        .collect()
}

fn usd(
    units: Decimal,
    kind: PriceKind,
    price: Decimal,
) -> (Decimal, String, PriceKind, Decimal, String) {
    (units, "USD".into(), kind, price, "USD".into())
}

#[test]
fn test_book_reduction_price_takes_cost_currency() {
    let sell = txn(
        5,
        vec![
            stk(dec!(-2), spec(Some(dec!(5)), Some("USD")))
                .with_price(bare_number_price(PriceKind::Unit, dec!(7))),
            cash("Assets:C", dec!(14), "USD"),
            Posting::auto("Income:G"),
        ],
    );
    assert_eq!(
        booked_prices(vec![buy_usd()], sell),
        vec![usd(dec!(-2), PriceKind::Unit, dec!(7))]
    );
}

#[test]
fn test_book_augmentation_price_takes_cost_currency() {
    let buy = txn(
        5,
        vec![
            stk(dec!(2), spec(Some(dec!(5)), Some("USD")))
                .with_price(bare_number_price(PriceKind::Unit, dec!(6))),
            cash("Assets:C", dec!(-10), "USD"),
        ],
    );
    assert_eq!(
        booked_prices(vec![], buy),
        vec![usd(dec!(2), PriceKind::Unit, dec!(6))]
    );
}

#[test]
fn test_book_total_price_takes_cost_currency_and_stays_total() {
    let sell = txn(
        5,
        vec![
            stk(dec!(-2), spec(Some(dec!(5)), Some("USD")))
                .with_price(bare_number_price(PriceKind::Total, dec!(14))),
            cash("Assets:C", dec!(14), "USD"),
            Posting::auto("Income:G"),
        ],
    );
    assert_eq!(
        booked_prices(vec![buy_usd()], sell),
        vec![usd(dec!(-2), PriceKind::Total, dec!(14))]
    );
}

/// `{5}` names no currency either: beancount's `replace_currencies` gives the
/// cost AND the price the one group currency, USD.
#[test]
fn test_book_inferred_cost_currency_reaches_the_price() {
    let buy = txn(
        5,
        vec![
            stk(dec!(2), spec(Some(dec!(5)), None))
                .with_price(bare_number_price(PriceKind::Unit, dec!(6))),
            cash("Assets:C", dec!(-10), "USD"),
        ],
    );
    assert_eq!(
        booked_prices(vec![], buy),
        vec![usd(dec!(2), PriceKind::Unit, dec!(6))]
    );

    let sell = txn(
        5,
        vec![
            stk(dec!(-2), spec(Some(dec!(5)), None))
                .with_price(bare_number_price(PriceKind::Unit, dec!(7))),
            cash("Assets:C", dec!(14), "USD"),
            Posting::auto("Income:G"),
        ],
    );
    assert_eq!(
        booked_prices(vec![buy_usd()], sell),
        vec![usd(dec!(-2), PriceKind::Unit, dec!(7))]
    );
}

/// An empty `{}` takes its cost currency from booking (a reduction, from the
/// matched lot; an augmentation, from the residual), and the price follows.
#[test]
fn test_book_empty_cost_spec_price_follows_the_booked_cost() {
    let sell = txn(
        5,
        vec![
            stk(dec!(-2), spec(None, None)).with_price(bare_number_price(PriceKind::Unit, dec!(7))),
            cash("Assets:C", dec!(14), "USD"),
            Posting::auto("Income:G"),
        ],
    );
    assert_eq!(
        booked_prices(vec![buy_usd()], sell),
        vec![usd(dec!(-2), PriceKind::Unit, dec!(7))]
    );

    let buy = txn(
        5,
        vec![
            stk(dec!(2), spec(None, None)).with_price(bare_number_price(PriceKind::Unit, dec!(6))),
            cash("Assets:C", dec!(-10), "USD"),
        ],
    );
    assert_eq!(
        booked_prices(vec![], buy),
        vec![usd(dec!(2), PriceKind::Unit, dec!(6))]
    );
}

/// The cost's currency wins even when every other leg is in another one:
/// beancount books `7 EUR`, and the gain absorbs both currencies.
#[test]
fn test_book_price_takes_cost_currency_not_the_other_legs() {
    let buy_eur = txn(
        2,
        vec![
            stk(dec!(2), spec(Some(dec!(5)), Some("EUR"))),
            cash("Assets:C", dec!(-10), "EUR"),
        ],
    );
    let sell = txn(
        5,
        vec![
            stk(dec!(-2), spec(Some(dec!(5)), Some("EUR")))
                .with_price(bare_number_price(PriceKind::Unit, dec!(7))),
            cash("Assets:C", dec!(14), "USD"),
            Posting::auto("Income:G"),
        ],
    );
    assert_eq!(
        booked_prices(vec![buy_eur], sell),
        vec![(
            dec!(-2),
            "EUR".into(),
            PriceKind::Unit,
            dec!(7),
            "EUR".into()
        )]
    );
}

/// A reduction spanning two lots is expanded into one posting per lot, and
/// each keeps the completed price.
#[test]
fn test_book_expanded_reduction_keeps_the_completed_price_on_every_lot() {
    let buy_six = txn(
        3,
        vec![
            stk(dec!(2), spec(Some(dec!(6)), Some("USD"))),
            cash("Assets:C", dec!(-12), "USD"),
        ],
    );
    let sell = txn(
        5,
        vec![
            stk(dec!(-4), spec(None, None)).with_price(bare_number_price(PriceKind::Unit, dec!(7))),
            cash("Assets:C", dec!(28), "USD"),
            Posting::auto("Income:G"),
        ],
    );
    assert_eq!(
        booked_prices(vec![buy_usd(), buy_six], sell),
        vec![
            usd(dec!(-2), PriceKind::Unit, dec!(7)),
            usd(dec!(-2), PriceKind::Unit, dec!(7)),
        ]
    );
}

/// A price on a cost-less posting is unchanged: its currency still comes from
/// the balance (the weight IS the price there), not from this rule.
#[test]
fn test_book_cost_less_price_currency_still_comes_from_the_balance() {
    let mut engine = BookingEngine::new();
    let mut t = txn(
        5,
        vec![
            cash("Assets:A", dec!(100.00), "EUR")
                .with_price(bare_number_price(PriceKind::Unit, dec!(1.20))),
            cash("Assets:B", dec!(-120.00), "USD"),
        ],
    );
    engine.book_interpolate_apply(&mut t).expect("books");
    let price = t.postings[0].price.as_deref().expect("price kept");
    assert_eq!(
        price.amount.as_ref().and_then(IncompleteAmount::as_amount),
        Some(&Amount::new(dec!(1.20), "USD"))
    );
}
