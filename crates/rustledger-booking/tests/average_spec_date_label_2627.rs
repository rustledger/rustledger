//! A date or label on an AVERAGE sale's cost spec is refused (#2627).
//!
//! The pool an AVERAGE sale takes from is undated and unlabeled, so a date or
//! label on the sale describes no lot, as on a `{*}` sale (#2398). Every
//! public booking entry point must report it the same way.

use rust_decimal_macros::dec;
use rustledger_booking::{BookingEngine, BookingError};
use rustledger_core::{
    Amount, BookingError as CoreError, BookingMethod, CostNumber, CostSpec, Posting,
    PriceAnnotation, Transaction,
};

fn date(d: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(2024, 1, d).expect("valid date")
}

/// An AVERAGE engine holding one lot of 10 X at 10.00 EUR, bought on day 2
/// with the label `lot-a`.
fn engine() -> BookingEngine {
    let mut engine = BookingEngine::with_method(BookingMethod::Average);
    let mut buy = Transaction::new(date(2), "buy")
        .with_synthesized_posting(
            Posting::new("Assets:B", Amount::new(dec!(10), "X")).with_cost(
                CostSpec::empty()
                    .with_number(CostNumber::PerUnit { value: dec!(10.00) })
                    .with_currency("EUR")
                    .with_date(date(2))
                    .with_label("lot-a"),
            ),
        )
        .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(-100.00), "EUR")));
    engine
        .book_interpolate_apply(&mut buy)
        .expect("a dated, labeled buy books");
    engine
}

fn sale(spec: CostSpec) -> Transaction {
    Transaction::new(date(20), "sell")
        .with_synthesized_posting(
            Posting::new("Assets:B", Amount::new(dec!(-1), "X"))
                .with_cost(spec)
                .with_price(PriceAnnotation::unit(Amount::new(dec!(15), "EUR"))),
        )
        .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(15), "EUR")))
        .with_synthesized_posting(Posting::auto("Income:G"))
}

/// What each entry point says about selling with `spec`: `None` when it
/// books, else the `stated` date or label of the refusal.
fn verdict(spec: &CostSpec) -> Option<String> {
    let engine = engine();
    let txn = sale(spec.clone());
    let outcome = |r: Result<(), BookingError>| match r {
        Ok(()) => None,
        Err(BookingError::Inventory(e)) => match e.error {
            CoreError::AverageSpecDateOrLabel { currency, stated } => {
                assert_eq!(currency.as_str(), "X");
                assert_eq!(e.account.as_str(), "Assets:B");
                Some(stated)
            }
            other => panic!("expected AverageSpecDateOrLabel, got {other}"),
        },
        Err(other) => panic!("expected an inventory error, got {other}"),
    };
    let booked = outcome(engine.book(&txn).map(|_| ()));
    let interpolated = outcome(engine.book_and_interpolate(&txn).map(|_| ()));
    let mut applied = txn;
    let mut engine = engine;
    let applied = outcome(engine.book_interpolate_apply(&mut applied).map(|_| ()));
    assert_eq!(booked, interpolated, "book vs book_and_interpolate");
    assert_eq!(booked, applied, "book vs book_interpolate_apply");
    booked
}

#[test]
fn a_date_or_label_names_no_lot_in_the_pool() {
    // The very date and label the pool's only lot was bought with: the sale
    // takes from the pool, which has neither.
    assert_eq!(
        verdict(&CostSpec::empty().with_date(date(2))),
        Some("2024-01-02".into())
    );
    assert_eq!(
        verdict(&CostSpec::empty().with_label("lot-a")),
        Some("\"lot-a\"".into())
    );
    // A date beside a correct cost and currency; the date is named first when
    // both are written.
    assert_eq!(
        verdict(
            &CostSpec::empty()
                .with_number(CostNumber::PerUnit { value: dec!(10.00) })
                .with_currency("EUR")
                .with_date(date(9))
                .with_label("lot-a")
        ),
        Some("2024-01-09".into())
    );
}

#[test]
fn a_spec_without_a_date_or_label_still_books() {
    assert_eq!(verdict(&CostSpec::empty()), None);
    assert_eq!(verdict(&CostSpec::empty().with_currency("EUR")), None);
}

#[test]
fn the_message_says_what_to_do() {
    let e = CoreError::AverageSpecDateOrLabel {
        currency: "X".into(),
        stated: "2024-01-02".into(),
    };
    assert_eq!(
        e.with_account("Assets:B".into()).to_string(),
        "Assets:B: AVERAGE pool of X is one lot with no date or label, so the cost spec's \
         2024-01-02 describes no lot; remove it"
    );
}
