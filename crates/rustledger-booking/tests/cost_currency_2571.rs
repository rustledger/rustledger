//! A reduction's cost currency, and its price's, against the lots it sells
//! (#2571).
//!
//! A sale whose proceeds are in another currency than the lot's cost cannot
//! have its gain computed without a rate, yet booked: an interpolated gains
//! posting absorbed both currencies and nothing was reported. Beancount 3.2.3
//! refuses both shapes, and every case below was checked against it
//! (`bean-check`, plus `bean-query` for the booked lots):
//!
//! - a reduction priced in another currency than its cost: "Cost and price
//!   currencies must match: EUR != USD";
//! - a cost spec written without a currency (`{}`) takes one from
//!   `booking_full.categorize_by_currency`: its price's, else the other
//!   postings' one currency group when it is the only undetermined posting,
//!   else the one cost currency the account holds. Beside USD cash that is
//!   USD, and an account holding only EUR lots has "No position matches".
//!
//! Three cases are NOT beancount's answer, and are pinned so that changing them
//! is a decision rather than an accident; see the #2571 PR:
//! - an augmentation priced in another currency than its cost still books
//!   (beancount: "Cost and price currencies must match"); nothing is
//!   disposed of, so no gain is computed from the two;
//! - a `{}` sale no step resolves (only auto-postings beside it, lots in two
//!   cost currencies) sells by the account's method (beancount: "Failed to
//!   categorize posting");
//! - a `{}` sale of X whose other postings are in X itself reads the cost
//!   currency from the account (beancount: X, then "No position matches").

use rust_decimal_macros::dec;
use rustledger_booking::{BookingEngine, BookingError};
use rustledger_core::{
    Amount, BookingMethod, CostNumber, CostSpec, Decimal, IncompleteAmount, Posting,
    PriceAnnotation, Transaction,
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

/// `account  <n> HOOL {<spec>}`.
fn hool(account: &str, n: Decimal, spec: CostSpec) -> Posting {
    Posting::new(account, Amount::new(n, "HOOL")).with_cost(spec)
}

/// Buy `n` HOOL at `cost` `currency` into `account`.
fn buy(day: u32, account: &str, n: Decimal, cost: Decimal, currency: &str) -> Transaction {
    txn(
        day,
        vec![
            hool(account, n, spec(Some(cost), Some(currency))),
            cash("Equity:Opening", -(n * cost), currency),
        ],
    )
}

/// Book `history` (which must succeed) under `method`, then `last`. Returns
/// the booked postings of `last` as `account units {cost}` strings, or the
/// error. Both public entry points must agree on it.
fn book(
    method: BookingMethod,
    history: Vec<Transaction>,
    last: Transaction,
) -> Result<Vec<String>, BookingError> {
    let mut engine = BookingEngine::with_method(method);
    for mut t in history {
        engine
            .book_interpolate_apply(&mut t)
            .expect("history books");
    }
    let viewed = engine.book_and_interpolate(&last).map(|r| r.transaction);
    let mut applied = last;
    let result = engine.book_interpolate_apply(&mut applied);
    assert_eq!(
        viewed.is_ok(),
        result.is_ok(),
        "book_and_interpolate and book_interpolate_apply disagree: {viewed:?} vs {result:?}"
    );
    result?;
    Ok(applied
        .postings
        .iter()
        .map(|p| {
            let units = p.amount().expect("every posting booked");
            let cost = p.cost.as_deref().map_or(String::new(), |c| {
                format!(
                    " {{{} {}}}",
                    c.number
                        .and_then(|n| n.per_unit())
                        .expect("booked per-unit"),
                    c.currency.as_deref().expect("booked currency")
                )
            });
            format!("{} {} {}{cost}", p.account, units.number, units.currency)
        })
        .collect())
}

fn eur_lots() -> Vec<Transaction> {
    vec![buy(2, "Assets:Stock", dec!(2), dec!(11.00), "EUR")]
}

/// `-1 HOOL {}`, `Assets:Cash 13.00 <cash>`, `Income:Gains`.
fn sell_empty_beside(cash_currency: &str) -> Transaction {
    txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), spec(None, None)),
            cash("Assets:Cash", dec!(13.00), cash_currency),
            Posting::auto("Income:Gains"),
        ],
    )
}

fn assert_no_lot_in(result: Result<Vec<String>, BookingError>, currency: &str) {
    match result {
        Err(BookingError::NoLotInInferredCostCurrency {
            cost, commodity, ..
        }) => {
            assert_eq!(cost.as_str(), currency);
            assert_eq!(commodity.as_str(), "HOOL");
        }
        other => panic!("expected NoLotInInferredCostCurrency({currency}), got {other:?}"),
    }
}

fn assert_cost_price_mismatch(result: Result<Vec<String>, BookingError>) {
    match result {
        Err(BookingError::CostPriceCurrencyMismatch { cost, price, .. }) => {
            assert_eq!((cost.as_str(), price.as_str()), ("EUR", "USD"));
        }
        other => panic!("expected CostPriceCurrencyMismatch, got {other:?}"),
    }
}

/// The issue's ledger A: `-2 HOOL {11.00 EUR} @ 14.50 USD`. It booked
/// `Income:Gains 22.00 EUR -29.00 USD` with no error.
#[test]
fn a_reduction_priced_in_another_currency_than_its_cost_is_refused() {
    for price in [
        PriceAnnotation::unit(Amount::new(dec!(14.50), "USD")),
        PriceAnnotation::total(Amount::new(dec!(29.00), "USD")),
    ] {
        let sell = txn(
            5,
            vec![
                hool(
                    "Assets:Stock",
                    dec!(-2),
                    spec(Some(dec!(11.00)), Some("EUR")),
                )
                .with_price(price),
                cash("Assets:Cash", dec!(29.00), "USD"),
                Posting::auto("Income:Gains"),
            ],
        );
        assert_cost_price_mismatch(book(BookingMethod::Strict, eur_lots(), sell));
    }
}

/// The issue's ledger B: `{}` beside USD cash takes USD as its cost currency,
/// and the account's lots cost EUR. It sold the EUR lot and booked
/// `Income:Gains 11.00 EUR -13.00 USD`.
#[test]
fn an_empty_cost_beside_cash_in_another_currency_matches_no_lot() {
    for method in [
        BookingMethod::Strict,
        BookingMethod::Fifo,
        BookingMethod::Lifo,
        BookingMethod::Hifo,
        // The two that pool the account ignore the spec's filter, so they are
        // checked after the pool is chosen. No oracle: beancount supports
        // neither (and refuses every `{*}`).
        BookingMethod::Average,
    ] {
        assert_no_lot_in(book(method, eur_lots(), sell_empty_beside("USD")), "USD");
    }
}

#[test]
fn a_merge_beside_cash_in_another_currency_matches_no_lot() {
    let mut merge = spec(None, None);
    merge.merge = true;
    let sell = txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), merge),
            cash("Assets:Cash", dec!(13.00), "USD"),
            Posting::auto("Income:Gains"),
        ],
    );
    assert_no_lot_in(book(BookingMethod::Fifo, eur_lots(), sell), "USD");
}

/// The control: beside cash in the lots' own currency the same sale books.
#[test]
fn an_empty_cost_beside_cash_in_the_lots_currency_books() {
    let got = book(BookingMethod::Strict, eur_lots(), sell_empty_beside("EUR")).unwrap();
    assert_eq!(
        got,
        [
            "Assets:Stock -1 HOOL {11.00 EUR}",
            "Assets:Cash 13.00 EUR",
            "Income:Gains -2.00 EUR",
        ]
    );
}

/// The price names the cost currency of a `{}` before anything else does.
#[test]
fn an_empty_cost_takes_its_prices_currency() {
    let sell = txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), spec(None, None))
                .with_price(PriceAnnotation::unit(Amount::new(dec!(13.00), "USD"))),
            cash("Assets:Cash", dec!(13.00), "USD"),
            Posting::auto("Income:Gains"),
        ],
    );
    assert_no_lot_in(book(BookingMethod::Fifo, eur_lots(), sell), "USD");
}

/// A cost number with its currency elided, `{11.00}`, is resolved the same way.
#[test]
fn a_cost_number_without_a_currency_takes_the_groups_currency() {
    let sell = txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), spec(Some(dec!(11.00)), None)),
            cash("Assets:Cash", dec!(13.00), "USD"),
            Posting::auto("Income:Gains"),
        ],
    );
    assert_no_lot_in(book(BookingMethod::Fifo, eur_lots(), sell), "USD");
}

/// FIFO with an older EUR lot and a newer USD one: USD cash makes the cost
/// currency USD, so the USD lot is sold, not the oldest. Beancount sells the
/// USD lot too.
#[test]
fn the_groups_currency_selects_among_lots_in_two_cost_currencies() {
    let history = vec![
        buy(2, "Assets:Stock", dec!(2), dec!(11.00), "EUR"),
        buy(3, "Assets:Stock", dec!(1), dec!(12.00), "USD"),
    ];
    let got = book(BookingMethod::Fifo, history, sell_empty_beside("USD")).unwrap();
    assert_eq!(
        got,
        [
            "Assets:Stock -1 HOOL {12.00 USD}",
            "Assets:Cash 13.00 USD",
            "Income:Gains -1.00 USD",
        ]
    );
}

/// Units and cost currencies come from ONE categorization of the transaction
/// as written. The cash number has no currency, so the `{}` is not the only
/// undetermined posting and its cost currency is the account's, EUR, while
/// the cash takes its account's USD. Resolving the cash first would have made
/// it a USD group and the `{}` USD with it, refusing what beancount books.
#[test]
fn a_currency_less_cash_number_leaves_the_cost_currency_to_the_account() {
    let history = vec![
        buy(2, "Assets:Stock", dec!(2), dec!(11.00), "EUR"),
        txn(
            2,
            vec![
                cash("Assets:Cash", dec!(100.00), "USD"),
                Posting::auto("Equity:Opening"),
            ],
        ),
    ];
    let sell = txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), spec(None, None)),
            Posting::with_incomplete("Assets:Cash", IncompleteAmount::NumberOnly(dec!(13))),
            Posting::auto("Income:Gains"),
        ],
    );
    let got = book(BookingMethod::Fifo, history, sell).unwrap();
    assert_eq!(
        got,
        [
            "Assets:Stock -1 HOOL {11.00 EUR}",
            "Assets:Cash 13 USD",
            "Income:Gains 11.00 EUR",
            "Income:Gains -13 USD",
        ]
    );
}

/// Two `{}` sales are two undetermined postings, so neither takes the cash's
/// currency: each takes its account's, and beancount books both EUR lots.
#[test]
fn two_empty_costs_each_take_their_accounts_cost_currency() {
    let history = vec![
        buy(2, "Assets:Stock", dec!(2), dec!(11.00), "EUR"),
        buy(2, "Assets:Stock2", dec!(2), dec!(11.00), "EUR"),
    ];
    let sell = txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), spec(None, None)),
            hool("Assets:Stock2", dec!(-1), spec(None, None)),
            cash("Assets:Cash", dec!(26.00), "USD"),
            Posting::auto("Income:Gains"),
        ],
    );
    let got = book(BookingMethod::Strict, history, sell).unwrap();
    assert_eq!(got[0], "Assets:Stock -1 HOOL {11.00 EUR}");
    assert_eq!(got[1], "Assets:Stock2 -1 HOOL {11.00 EUR}");
}

/// Pinned divergence: beancount refuses this augmentation; it disposes of
/// nothing, so no gain is computed across the two currencies.
#[test]
fn an_augmentation_priced_in_another_currency_still_books() {
    let buy_priced = txn(
        5,
        vec![
            hool(
                "Assets:Stock",
                dec!(2),
                spec(Some(dec!(11.00)), Some("EUR")),
            )
            .with_price(PriceAnnotation::unit(Amount::new(dec!(14.50), "USD"))),
            cash("Equity:Opening", dec!(-22.00), "EUR"),
        ],
    );
    let got = book(BookingMethod::Strict, eur_lots(), buy_priced).unwrap();
    assert_eq!(got[0], "Assets:Stock 2 HOOL {11.00 EUR}");
}

/// Pinned divergence: no step resolves this `{}` (an auto-posting beside it,
/// lots in two cost currencies), so it sells by the account's method, FIFO's
/// oldest lot. Beancount refuses it ("Failed to categorize posting").
#[test]
fn an_unresolved_empty_cost_sells_by_the_accounts_method() {
    let history = vec![
        buy(2, "Assets:Stock", dec!(2), dec!(11.00), "EUR"),
        buy(3, "Assets:Stock", dec!(1), dec!(12.00), "USD"),
    ];
    let sell = txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), spec(None, None)),
            Posting::auto("Income:Gains"),
        ],
    );
    let got = book(BookingMethod::Fifo, history, sell).unwrap();
    assert_eq!(got[0], "Assets:Stock -1 HOOL {11.00 EUR}");
}

/// AVERAGE pools the account and used to ignore the spec, so a written cost
/// currency the pool is not held in sold the EUR pool for USD, recording a
/// gain across the two. No oracle: beancount does not support AVERAGE.
#[test]
fn an_average_pool_in_another_cost_currency_than_written_matches_no_lot() {
    let sell = txn(
        5,
        vec![
            hool("Assets:Stock", dec!(-1), spec(None, Some("USD")))
                .with_price(PriceAnnotation::unit(Amount::new(dec!(13.00), "USD"))),
            cash("Assets:Cash", dec!(13.00), "USD"),
            Posting::auto("Income:Gains"),
        ],
    );
    match book(BookingMethod::Average, eur_lots(), sell) {
        Err(BookingError::Inventory(e)) => assert!(
            matches!(e.error, rustledger_core::BookingError::NoMatchingLot { .. }),
            "{e:?}"
        ),
        other => panic!("expected NoMatchingLot, got {other:?}"),
    }
}

/// Pinned divergence: the only other group is the commodity itself (`10 HOOL`
/// moved in beside the sale). Beancount takes HOOL as the sale's cost
/// currency and finds no position; no lot of HOOL is held at a cost in HOOL,
/// so the account's one cost currency, EUR, is read instead and the sale
/// books, as it did before #2571.
#[test]
fn the_commoditys_own_postings_do_not_name_its_cost_currency() {
    let sell = txn(
        5,
        vec![
            Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")),
            Posting::new("Equity:Opening", Amount::new(dec!(-10), "HOOL")),
            hool("Assets:Stock", dec!(-1), spec(None, None)),
            Posting::auto("Assets:Cash"),
        ],
    );
    let got = book(BookingMethod::Fifo, eur_lots(), sell).unwrap();
    assert!(
        got.contains(&"Assets:Stock -1 HOOL {11.00 EUR}".to_string()),
        "{got:?}"
    );
}
