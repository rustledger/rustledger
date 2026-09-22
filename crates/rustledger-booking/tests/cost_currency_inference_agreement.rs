//! `book` classifies a cost spec with the currency it will book it with
//! (#2384 review).
//!
//! A cost spec written without a currency, `{102}`, is booked with one
//! inferred from the price or the other postings. `apply` then asks whether
//! the booked posting reduces, of `{102 USD}`. If `book` asked of `{102}`,
//! where a missing currency matches any, the two could disagree: holding a
//! long at 102 EUR and a short at 101 USD, `book` matched the EUR lot as the
//! posting's own side and booked an augmentation that `apply` then refused.

use rust_decimal_macros::dec;
use rustledger_booking::BookingEngine;
use rustledger_core::{Amount, BookingMethod, CostSpec, Decimal, Posting, Transaction};

fn spec(cost: Decimal, currency: Option<&str>) -> CostSpec {
    let s = CostSpec::empty().with_number(rustledger_core::CostNumber::PerUnit { value: cost });
    match currency {
        Some(c) => s.with_currency(c),
        None => s,
    }
}

fn stock(n: Decimal, cost: Decimal, currency: Option<&str>) -> Posting {
    Posting::new("Assets:Stock", Amount::new(n, "X")).with_cost(spec(cost, currency))
}

/// Seed a long at 102 `long_currency` and a short at 101 USD, then buy 3 at
/// `{102}` paid in USD. Returns what `book` said and, if it booked, what
/// `apply` said.
fn buy_at_102_beside(long_currency: &str) -> (bool, Option<bool>) {
    let day = |d| rustledger_core::naive_date(2020, 1, d).unwrap();
    let mut engine = BookingEngine::with_method(BookingMethod::Strict);
    let seed = Transaction::new(day(1), "seed")
        .with_synthesized_posting(stock(dec!(5), dec!(102), Some(long_currency)))
        .with_synthesized_posting(Posting::new(
            "Assets:Funding",
            Amount::new(dec!(-510), long_currency),
        ))
        .with_synthesized_posting(stock(dec!(-2), dec!(101), Some("USD")))
        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(202), "USD")));
    let booked = engine.book(&seed).expect("the seed books");
    engine.apply(&booked.transaction).expect("the seed applies");

    let buy = Transaction::new(day(5), "buy 3 at 102")
        .with_synthesized_posting(stock(dec!(3), dec!(102), None))
        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-306), "USD")));
    match engine.book(&buy) {
        Ok(booked) => (true, Some(engine.apply(&booked.transaction).is_ok())),
        Err(_) => (false, None),
    }
}

#[test]
fn a_long_in_another_cost_currency_is_not_the_own_side() {
    // The buy is booked in USD and there is no lot at 102 USD on either side,
    // so it is refused, as beancount refuses it. By `book`, not by `apply`
    // after `book` accepted it.
    assert_eq!(buy_at_102_beside("EUR"), (false, None));
}

#[test]
fn a_long_in_the_inferred_cost_currency_is_the_own_side() {
    assert_eq!(buy_at_102_beside("USD"), (true, Some(true)));
}
