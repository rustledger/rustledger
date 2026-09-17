//! A `@@` total price must still produce a gain when only the intermediate
//! product of the per-lot pro-rata leaves `Decimal`'s range (#2346).

use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, BookingMethod, CostNumber, CostSpec, Decimal, Posting, PriceAnnotation, Transaction,
};

fn dec(s: &str) -> Decimal {
    Decimal::from_str_exact(s).expect("literal parses")
}

#[test]
fn a_total_price_gain_survives_an_overflowing_intermediate_product() {
    let units = dec("1000000000000000"); // 1e15
    let proceeds = dec("500000000000000"); // 5e14
    let per_unit_cost = Decimal::new(1, 2); // 0.01

    // The premise: the pro-rata's PRODUCT does not fit, while its answer does.
    assert!(
        proceeds.checked_mul(units).is_none(),
        "this test is pointless unless the intermediate product overflows"
    );

    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);

    let buy = Transaction::new(
        rustledger_core::naive_date(2024, 1, 1).expect("date"),
        "buy",
    )
    .with_synthesized_posting(
        Posting::new("Assets:Stock", Amount::new(units, "CORP")).with_cost(
            CostSpec::empty()
                .with_number(CostNumber::PerUnit {
                    value: per_unit_cost,
                })
                .with_currency("USD"),
        ),
    )
    .with_synthesized_posting(Posting::new(
        "Assets:Cash",
        Amount::new(-(units * per_unit_cost), "USD"),
    ));
    engine.apply(&buy).expect("the buy fits");

    // Sell the whole holding for a single `@@` total.
    let sell = Transaction::new(
        rustledger_core::naive_date(2024, 6, 1).expect("date"),
        "sell at a total price",
    )
    .with_synthesized_posting(
        Posting::new("Assets:Stock", Amount::new(-units, "CORP"))
            .with_cost(CostSpec::empty())
            .with_price(PriceAnnotation::total(Amount::new(proceeds, "USD"))),
    )
    .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(proceeds, "USD")));

    let booked = engine
        .book(&sell)
        .expect("a representable share must not be reported as an overflow");

    let gain = booked
        .gains
        .first()
        .expect("selling a cost-bearing lot at a price records a gain");
    assert_eq!(
        gain.proceeds.number, proceeds,
        "the single lot is the whole sale, so its share is the whole total"
    );
    assert_eq!(
        gain.cost_basis.number,
        units * per_unit_cost,
        "and its basis is the lot's cost value"
    );
}
