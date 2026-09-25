//! Booking carries a lot's exact total into the sale that empties it (#2425).
//!
//! A lot bought as `{{500 USD}}` of 3 has a per-unit cost of 500/3, rounded.
//! The engine records the lot's total when it adds the lot, and the sale that
//! empties it is booked as `PerUnitFromTotal` with that total, so the balance
//! weighs 500, not `3 × 166.66…67`.

use rustledger_booking::BookingEngine;
use rustledger_core::{Amount, BookingMethod, CostNumber, CostSpec, Decimal, Posting, Transaction};

fn d(n: i64) -> Decimal {
    Decimal::from(n)
}

fn date(day: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(2024, 1, day).unwrap()
}

fn spec(number: Option<CostNumber>) -> CostSpec {
    CostSpec {
        number,
        currency: Some("USD".into()),
        date: None,
        label: None,
        merge: false,
    }
}

/// An engine holding `(units, total)` lots of X, each bought as `{{total}}`.
fn engine(lots: &[(i64, i64)]) -> BookingEngine {
    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
    for (day, &(units, total)) in (1u32..).zip(lots) {
        let mut buy = Posting::new("Assets:B", Amount::new(d(units), "X"));
        buy.cost = Some(Box::new(spec(Some(CostNumber::Total { value: d(total) }))));
        let txn = Transaction::new(date(day), "buy")
            .with_synthesized_posting(buy)
            .with_synthesized_posting(Posting::new(
                "Assets:C",
                Amount::new(d(-total * units.signum()), "USD"),
            ));
        let booked = engine.book(&txn).expect("the buy books");
        engine.apply(&booked.transaction).expect("and applies");
    }
    engine
}

/// The booked cost numbers of a sale of `units` X with `{}`.
fn sell(engine: &BookingEngine, units: i64) -> Vec<CostNumber> {
    let mut sale = Posting::new("Assets:B", Amount::new(d(units), "X"));
    sale.cost = Some(Box::new(CostSpec {
        currency: None,
        ..spec(None)
    }));
    let txn = Transaction::new(date(20), "sell")
        .with_synthesized_posting(sale)
        .with_synthesized_posting(Posting::new("Assets:C", Amount::new(d(1), "USD")));
    engine
        .book(&txn)
        .expect("the sale books")
        .transaction
        .postings
        .iter()
        .filter(|p| p.account.as_str() == "Assets:B")
        .map(|p| {
            p.cost
                .as_deref()
                .and_then(|c| c.number)
                .expect("a booked cost")
        })
        .collect()
}

const fn total_of(number: &CostNumber) -> Option<Decimal> {
    match number {
        CostNumber::PerUnitFromTotal(b) => Some(b.total),
        _ => None,
    }
}

#[test]
fn selling_a_whole_total_cost_lot_books_its_total() {
    let booked = sell(&engine(&[(3, 500)]), -3);
    assert_eq!(
        booked.iter().map(total_of).collect::<Vec<_>>(),
        vec![Some(d(500))]
    );
}

#[test]
fn covering_a_whole_short_total_cost_lot_books_its_total() {
    let booked = sell(&engine(&[(-3, 500)]), 3);
    assert_eq!(
        booked.iter().map(total_of).collect::<Vec<_>>(),
        vec![Some(d(500))]
    );
}

/// A short `{{500 USD}}` lot covered in two parts: the lot keeps the rest of
/// its (negative) total, and the cover that empties it books exactly that,
/// so the two covers add up to 500.
#[test]
fn a_short_total_cost_lot_covered_in_parts_adds_up_to_its_total() {
    let mut engine = engine(&[(-3, 500)]);
    let mut covered = Decimal::ZERO;
    for units in [1, 2] {
        let mut cover = Posting::new("Assets:B", Amount::new(d(units), "X"));
        cover.cost = Some(Box::new(CostSpec {
            currency: None,
            ..spec(None)
        }));
        let txn = Transaction::new(date(20), "cover")
            .with_synthesized_posting(cover)
            .with_synthesized_posting(Posting::new("Assets:C", Amount::new(d(-1), "USD")));
        let booked = engine.book(&txn).expect("the cover books");
        let posting = &booked.transaction.postings[0];
        let number = posting.cost.as_deref().and_then(|c| c.number).unwrap();
        covered += rustledger_booking::cost_number_weight(d(units), &number).unwrap();
        engine.apply(&booked.transaction).expect("and applies");
    }
    assert_eq!(covered, d(500));
}

/// A negative total cost (E4005, still booked) keeps its sign through the
/// engine, so the sale that empties the lot books -500, not +500.
#[test]
fn a_negative_total_cost_lot_books_its_signed_total() {
    let booked = sell(&engine(&[(3, -500)]), -3);
    assert_eq!(
        booked.iter().map(total_of).collect::<Vec<_>>(),
        vec![Some(d(-500))]
    );
}

/// A FIFO sale of two whole `{{T}}` lots expands into one posting per lot,
/// each booked at its own lot's total.
#[test]
fn an_expanded_sale_books_each_lots_total() {
    let booked = sell(&engine(&[(3, 500), (3, 700)]), -6);
    assert_eq!(
        booked.iter().map(total_of).collect::<Vec<_>>(),
        vec![Some(d(500)), Some(d(700))]
    );
}

/// A lot bought at a per-unit cost is sold at it: no total to carry, and
/// the booked cost is unchanged.
#[test]
fn a_per_unit_lot_books_per_unit() {
    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
    let mut buy = Posting::new("Assets:B", Amount::new(d(3), "X"));
    buy.cost = Some(Box::new(spec(Some(CostNumber::PerUnit { value: d(100) }))));
    let txn = Transaction::new(date(1), "buy")
        .with_synthesized_posting(buy)
        .with_synthesized_posting(Posting::new("Assets:C", Amount::new(d(-300), "USD")));
    let booked = engine.book(&txn).unwrap();
    engine.apply(&booked.transaction).unwrap();
    assert_eq!(
        sell(&engine, -3),
        vec![CostNumber::PerUnit { value: d(100) }]
    );
}
