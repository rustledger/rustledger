//! A sale written with its units elided books exactly as the same sale with
//! its units written (#2647).
//!
//! `book` matches lots only for postings whose units are written, so an
//! elided-units sale (`Assets:B  X {10.00 EUR} @ 15.00 EUR`) was booked by
//! nobody: interpolation solved its units and `apply` reduced the inventory.
//! It recorded no capital gain under any method, an AVERAGE sale kept the
//! written (rounded) cost instead of the pool's exact one, and the written
//! cost was never checked against the pool (#2645). Booking now solves the
//! units first and books the sale as if they had been written.

use rust_decimal_macros::dec;
use rustledger_booking::{BookingEngine, BookingError, CapitalGain};
use rustledger_core::{
    Amount, BookingError as CoreError, BookingMethod, CostNumber, CostSpec, Decimal,
    IncompleteAmount, Posting, PriceAnnotation, Transaction,
};

fn date(d: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(2024, 1, d).expect("valid date")
}

fn per_unit(cost: Decimal) -> CostSpec {
    CostSpec::empty()
        .with_number(CostNumber::PerUnit { value: cost })
        .with_currency("USD")
}

/// Lots of X bought on days 2, 3, …: 10 at 10.00, 5 at 12.50, 4 at 10.00.
/// Two lots share a cost, so a `{10.00 USD}` sale can span both.
fn engine(method: BookingMethod) -> BookingEngine {
    let mut engine = BookingEngine::with_method(method);
    for (day, units, cost) in [
        (2, dec!(10), dec!(10.00)),
        (3, dec!(5), dec!(12.50)),
        (4, dec!(4), dec!(10.00)),
    ] {
        let mut buy = Transaction::new(date(day), "buy")
            .with_synthesized_posting(
                Posting::new("Assets:B", Amount::new(units, "X")).with_cost(per_unit(cost)),
            )
            .with_synthesized_posting(Posting::auto("Equity:O"));
        engine.book_interpolate_apply(&mut buy).expect("buy books");
    }
    engine
}

/// Sell `units` X at `cost` (the spec) for `price` each, with the cash and
/// the gain written. `units: None` elides them.
fn sale(
    units: Option<Decimal>,
    sold: Decimal,
    cost: Decimal,
    price: Decimal,
    gain: Decimal,
) -> Transaction {
    let mut posting = Posting::new("Assets:B", Amount::new(units.unwrap_or_default(), "X"))
        .with_cost(per_unit(cost))
        .with_price(PriceAnnotation::unit(Amount::new(price, "USD")));
    if units.is_none() {
        posting.units = Some(IncompleteAmount::CurrencyOnly("X".into()));
    }
    Transaction::new(date(20), "sell")
        .with_synthesized_posting(posting)
        .with_synthesized_posting(Posting::new("Assets:C", Amount::new(sold * price, "USD")))
        .with_synthesized_posting(Posting::new("Income:G", Amount::new(-gain, "USD")))
}

/// What a sale books: its postings, its gains, and the account's lots after
/// it, through both entry points, which must agree.
#[derive(Debug, PartialEq)]
struct Booked {
    postings: Vec<String>,
    gains: Vec<String>,
    lots: Vec<String>,
}

fn book(method: BookingMethod, txn: &Transaction) -> Result<Booked, CoreError> {
    let show_gain = |g: &CapitalGain| {
        format!(
            "{} {} basis {} proceeds {} acquired {:?}",
            g.units,
            g.currency,
            g.cost_basis.number.normalize(),
            g.proceeds.number.normalize(),
            g.acquired_date
        )
    };
    let unwrap = |e: BookingError| match e {
        BookingError::Inventory(e) => e.error,
        other => panic!("expected an inventory error, got {other}"),
    };
    // `book_and_interpolate_with_gains` + `apply`: the loader's path before
    // the one-step entry point, and the LSP's.
    let mut a = engine(method);
    let first = a.book_and_interpolate_with_gains(txn).map_err(unwrap);
    // `book_interpolate_apply`: the loader's path.
    let mut b = engine(method);
    let mut applied = txn.clone();
    let second = b.book_interpolate_apply(&mut applied).map_err(unwrap);
    let first = first.and_then(|(r, gains)| {
        a.apply(&r.transaction).map_err(unwrap)?;
        Ok((r.transaction, gains))
    });
    match (first, second) {
        (Ok((t1, g1)), Ok(g2)) => {
            assert_eq!(t1, applied, "the two entry points book differently");
            let (s1, s2): (Vec<String>, Vec<String>) = (
                g1.iter().map(show_gain).collect(),
                g2.iter().map(show_gain).collect(),
            );
            assert_eq!(s1, s2, "the two entry points record different gains");
            let postings = applied
                .postings
                .iter()
                .filter(|p| p.account.as_str() == "Assets:B")
                .map(|p| {
                    let c = p.cost.as_deref().expect("booked cost");
                    format!(
                        "{} X {{{:?} {:?} {:?}}}",
                        p.amount().expect("units").number.normalize(),
                        c.number,
                        c.currency,
                        c.date
                    )
                })
                .collect();
            let mut lots: Vec<String> = b
                .inventory(&"Assets:B".into())
                .expect("inventory")
                .positions()
                .map(|p| format!("{} {:?}", p.units.number.normalize(), p.cost))
                .collect();
            lots.sort();
            Ok(Booked {
                postings,
                gains: g2.iter().map(show_gain).collect(),
                lots,
            })
        }
        (Err(e1), Err(e2)) => {
            assert_eq!(e1, e2, "the two entry points refuse differently");
            Err(e1)
        }
        (first, second) => panic!("entry points disagree: {first:?} vs {second:?}"),
    }
}

/// Under every method, the elided sale books, records and leaves exactly
/// what the written one does, including a sale spanning two lots.
#[test]
fn an_elided_units_sale_books_as_the_written_one() {
    for method in [
        BookingMethod::Fifo,
        BookingMethod::Lifo,
        BookingMethod::Hifo,
        BookingMethod::Strict,
    ] {
        for (sold, cost) in [
            (dec!(2), dec!(10.00)),
            (dec!(14), dec!(10.00)),
            (dec!(5), dec!(12.50)),
        ] {
            // STRICT sells from several lots only when it takes all of them.
            if method == BookingMethod::Strict && sold == dec!(2) {
                continue;
            }
            let price = dec!(15.00);
            let gain = sold * (price - cost);
            let written = book(method, &sale(Some(-sold), sold, cost, price, gain))
                .unwrap_or_else(|e| panic!("{method:?} {sold}: written sale fails: {e}"));
            let elided = book(method, &sale(None, sold, cost, price, gain))
                .unwrap_or_else(|e| panic!("{method:?} {sold}: elided sale fails: {e}"));
            assert!(
                !written.gains.is_empty(),
                "{method:?} {sold}: a disposal is recorded"
            );
            assert_eq!(written, elided, "{method:?} {sold} @ {cost}");
        }
    }
}

/// An AVERAGE pool of 10 at 10.00, 5 at 12.50 and 4 at 10.00 is 202.50 / 19
/// = 10.657… per unit. A sale of the whole pool, written as the correct
/// rounding 10.66, books the pool's exact total 202.50, not 19 × 10.66 =
/// 202.54, written or elided alike.
#[test]
fn an_elided_units_average_sale_carries_the_pools_exact_cost() {
    let sold = dec!(19);
    let price = dec!(10.66);
    let tx = |units| sale(units, sold, dec!(10.66), price, dec!(0));
    let written = book(BookingMethod::Average, &tx(Some(-sold))).map(|b| b.gains);
    let elided = book(BookingMethod::Average, &tx(None)).map(|b| b.gains);
    assert_eq!(written, elided);
    let gains = elided.expect("books");
    assert_eq!(gains.len(), 1);
    assert!(gains[0].contains("basis 202.5 "), "{gains:?}");
}

/// The cost an elided-units AVERAGE sale states is checked against the pool
/// as a written one's is (#2603, #2645).
#[test]
fn an_elided_units_average_sale_stating_a_wrong_cost_is_refused() {
    let tx = |units| sale(units, dec!(1), dec!(99.00), dec!(99.00), dec!(0));
    let written = book(BookingMethod::Average, &tx(Some(dec!(-1))));
    let elided = book(BookingMethod::Average, &tx(None));
    assert!(
        matches!(elided, Err(CoreError::AverageSpecMismatch { .. })),
        "{elided:?}"
    );
    assert_eq!(written, elided);
}

/// An elided-units posting that turns out to be a buy books as the written
/// buy: the lot it adds, dated by the transaction.
#[test]
fn an_elided_units_buy_books_as_the_written_one() {
    let buy = |units: Option<Decimal>| {
        let mut posting = Posting::new("Assets:B", Amount::new(units.unwrap_or_default(), "X"))
            .with_cost(per_unit(dec!(20.00)));
        if units.is_none() {
            posting.units = Some(IncompleteAmount::CurrencyOnly("X".into()));
        }
        Transaction::new(date(20), "buy")
            .with_synthesized_posting(posting)
            .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(-60.00), "USD")))
    };
    for method in [BookingMethod::Fifo, BookingMethod::Average] {
        assert_eq!(
            book(method, &buy(Some(dec!(3)))),
            book(method, &buy(None)),
            "{method:?}"
        );
    }
}
