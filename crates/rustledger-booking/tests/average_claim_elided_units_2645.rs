//! An AVERAGE sale whose units are elided has its stated cost checked too
//! (#2645).
//!
//! `book` matches lots only for postings whose units are written, so a sale
//! like `Assets:B  X {99.00 EUR}` skipped #2603's claim check: interpolation
//! solved its units from the cash and `apply` reduced the pool. The posting
//! weighed 99 while the pool gave up a unit at 10, and the 89 EUR gain was
//! never booked. Both booking entry points now check it once its units are
//! known, against the pool `apply` reduces, by the rule `book` uses.

use rust_decimal_macros::dec;
use rustledger_booking::{BookingEngine, BookingError};
use rustledger_core::{
    Amount, BookingError as CoreError, BookingMethod, CostNumber, CostSpec, Decimal,
    IncompleteAmount, Posting, Transaction,
};

fn date(d: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(2024, 1, d).expect("valid date")
}

/// An engine whose `Assets:B` books `method`, holding 10 X at 100.00 USD and
/// 5 X at 120.00 USD: an AVERAGE pool of 1600/15 = 106.666… USD.
fn engine(method: BookingMethod) -> BookingEngine {
    let mut engine = BookingEngine::with_method(method);
    for (day, units, cost) in [(2, dec!(10), dec!(100.00)), (3, dec!(5), dec!(120.00))] {
        let mut buy = Transaction::new(date(day), "buy")
            .with_synthesized_posting(
                Posting::new("Assets:B", Amount::new(units, "X")).with_cost(
                    CostSpec::empty()
                        .with_number(CostNumber::PerUnit { value: cost })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:C"));
        engine.book_interpolate_apply(&mut buy).expect("buy books");
    }
    engine
}

/// `Assets:B  X {<cost> <currency>}`, units elided, against `cash` USD.
fn elided_sale(cost: Decimal, currency: &str, cash: Decimal) -> Transaction {
    let mut sale = Posting::new("Assets:B", Amount::new(dec!(0), "X")).with_cost(
        CostSpec::empty()
            .with_number(CostNumber::PerUnit { value: cost })
            .with_currency(currency),
    );
    sale.units = Some(IncompleteAmount::CurrencyOnly("X".into()));
    Transaction::new(date(20), "sell, units elided")
        .with_synthesized_posting(sale)
        .with_synthesized_posting(Posting::new("Assets:C", Amount::new(cash, currency)))
}

/// What both entry points say: `book_and_interpolate` followed by `apply`
/// (the LSP's path), and `book_interpolate_apply` (the loader's). They must
/// agree; the error is returned.
fn verdict(method: BookingMethod, txn: &Transaction) -> Result<(), CoreError> {
    let mut a = engine(method);
    let first = a
        .book_and_interpolate(txn)
        .and_then(|r| a.apply(&r.transaction));
    let mut b = engine(method);
    let mut applied = txn.clone();
    let second = b.book_interpolate_apply(&mut applied).map(|_| ());
    let unwrap = |r: Result<(), BookingError>| match r {
        Ok(()) => Ok(()),
        Err(BookingError::Inventory(e)) => Err(e.error),
        Err(other) => panic!("expected an inventory error, got {other}"),
    };
    let (first, second) = (unwrap(first), unwrap(second));
    assert_eq!(first, second, "the two entry points disagree");
    first
}

#[test]
fn the_issue_case_is_refused() {
    let err = verdict(
        BookingMethod::Average,
        &elided_sale(dec!(999.00), "USD", dec!(999.00)),
    )
    .expect_err("999.00 is not the pool's 106.67");
    assert_eq!(
        err,
        CoreError::AverageSpecMismatch {
            currency: "X".into(),
            stated: Amount::new(dec!(999.00), "USD"),
            pool: Amount::new(dec!(106.67), "USD"),
            total: false,
        }
    );
}

/// The rule is #2603's: a correct rounding of the exact pool at the
/// precision written holds, anything else is refused.
#[test]
fn a_correct_rounding_holds_and_nothing_else_does() {
    for (claim, holds) in [
        (dec!(106.67), true),
        (dec!(107), true),
        (dec!(106.7), true),
        (dec!(106.666667), true),
        (dec!(106.66), false),
        (dec!(106.6), false),
        (dec!(106), false),
    ] {
        let got = verdict(
            BookingMethod::Average,
            &elided_sale(claim, "USD", claim * dec!(2)),
        );
        assert_eq!(got.is_ok(), holds, "{claim}: {got:?}");
    }
}

/// #2589's currency check, which `book` makes for a written `{EUR}`, holds
/// here too.
#[test]
fn a_currency_the_pool_is_not_held_in_is_refused() {
    let err = verdict(
        BookingMethod::Average,
        &elided_sale(dec!(106.67), "EUR", dec!(106.67)),
    )
    .expect_err("the pool is held in USD");
    assert!(matches!(err, CoreError::NoMatchingLot { .. }), "{err:?}");
}

/// Under FIFO a written cost is a filter on the lots, as before: 999 matches
/// no lot, and 100.00 sells from the 100.00 lot.
#[test]
fn other_methods_are_unchanged() {
    assert!(
        verdict(
            BookingMethod::Fifo,
            &elided_sale(dec!(100.00), "USD", dec!(200.00))
        )
        .is_ok()
    );
}

/// An elided-units posting that turns out to be a buy states the new lot's
/// cost, which is no claim about the pool.
#[test]
fn an_elided_units_buy_is_not_a_claim() {
    let buy = elided_sale(dec!(999.00), "USD", dec!(-999.00));
    assert_eq!(verdict(BookingMethod::Average, &buy), Ok(()));
}
