//! A cost written on an AVERAGE sale is checked against the pool, not dropped
//! (#2603).
//!
//! An AVERAGE reduction sells at the pool's average cost. Under every other
//! method a written cost is a filter that a lot must pass, but here it was
//! ignored: `-1 X {99.00 EUR}` from a pool held at 11.00 EUR booked at 11.00.
//! The claim now holds when it is a correct rounding of the pool's EXACT
//! average at the precision written (half a unit in its last place,
//! inclusive), the rule a `{*}` claim follows (#2398), whatever the
//! transaction's other postings say. Beancount has no
//! AVERAGE booking, so there is no oracle; this is rledger's definition,
//! documented under E4001 in `docs/reference/errors.md` and in ADR 0007.

use rust_decimal_macros::dec;
use rustledger_booking::{BookingEngine, BookingError};
use rustledger_core::{
    Amount, BookingError as CoreError, BookingMethod, CostNumber, CostSpec, Decimal, Posting,
    Transaction,
};

const STOCK: &str = "Assets:Stock";

fn txn(day: u32, postings: Vec<Posting>) -> Transaction {
    let date = rustledger_core::naive_date(2024, 1, day).expect("valid date");
    postings.into_iter().fold(
        Transaction::new(date, "t"),
        Transaction::with_synthesized_posting,
    )
}

fn per_unit(value: Decimal, currency: &str) -> CostSpec {
    CostSpec::empty()
        .with_number(CostNumber::PerUnit { value })
        .with_currency(currency)
}

fn total(value: Decimal, currency: &str) -> CostSpec {
    CostSpec::empty()
        .with_number(CostNumber::Total { value })
        .with_currency(currency)
}

/// Buy `n` X at `cost` into the stock account, one transaction per lot.
fn buys(lots: &[(Decimal, Decimal)], currency: &str) -> Vec<Transaction> {
    (1u32..)
        .zip(lots)
        .map(|(day, &(n, cost))| {
            txn(
                day,
                vec![
                    Posting::new(STOCK, Amount::new(n, "X")).with_cost(per_unit(cost, currency)),
                    Posting::new("Equity:Opening", Amount::new(-(n * cost), currency)),
                ],
            )
        })
        .collect()
}

/// 10 X at 10 and 10 X at 12 EUR: a pool of 20 at 11.00 EUR.
fn eur_pool() -> Vec<Transaction> {
    buys(&[(dec!(10), dec!(10)), (dec!(10), dec!(12))], "EUR")
}

/// 1 X at 100 and 2 X at 200 USD: a pool of 3 at 500/3 = 166.666… USD, an
/// average no decimal can write out.
fn thirds_pool() -> Vec<Transaction> {
    buys(&[(dec!(1), dec!(100)), (dec!(2), dec!(200))], "USD")
}

/// Sell `n` X with `spec`, with a cash posting of `cash` and an elided gains
/// posting, or with the cash posting elided (and no gains posting) for `None`.
fn sale(n: Decimal, spec: CostSpec, cash: Option<Amount>) -> Transaction {
    let mut postings = vec![Posting::new(STOCK, Amount::new(n, "X")).with_cost(spec)];
    match cash {
        Some(amount) => {
            postings.push(Posting::new("Assets:Cash", amount));
            postings.push(Posting::auto("Income:Gains"));
        }
        None => postings.push(Posting::auto("Assets:Cash")),
    }
    txn(20, postings)
}

/// Book `history` on an AVERAGE account, then `last`, through all three
/// public entry points, which must agree. Returns the booked cost of the
/// sale's first posting, or the error.
fn book(history: Vec<Transaction>, last: &Transaction) -> Result<Decimal, BookingError> {
    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
    engine.set_account_method(STOCK.into(), BookingMethod::Average);
    for mut t in history {
        engine
            .book_interpolate_apply(&mut t)
            .expect("history books");
    }
    let booked = engine.book(last).map(|b| b.transaction);
    let viewed = engine.book_and_interpolate(last).map(|r| r.transaction);
    let mut applied = last.clone();
    let result = engine.book_interpolate_apply(&mut applied);
    assert_eq!(
        (booked.is_ok(), viewed.is_ok()),
        (result.is_ok(), result.is_ok()),
        "the entry points disagree: {booked:?} / {viewed:?} / {result:?}"
    );
    result?;
    Ok(applied.postings[0]
        .cost
        .as_deref()
        .and_then(|c| c.number)
        .and_then(|n| n.per_unit())
        .expect("a booked cost"))
}

/// The mismatch booking reported, as `(stated, pool, total)`.
fn mismatch(result: Result<Decimal, BookingError>) -> (Amount, Amount, bool) {
    match result {
        Err(BookingError::Inventory(e)) => match e.error {
            CoreError::AverageSpecMismatch {
                currency,
                stated,
                pool,
                total,
            } => {
                assert_eq!(currency.as_str(), "X");
                assert_eq!(e.account.as_str(), STOCK);
                (stated, pool, total)
            }
            other => panic!("expected an AVERAGE spec mismatch, got {other}"),
        },
        Err(other) => panic!("expected an AVERAGE spec mismatch, got {other}"),
        Ok(cost) => panic!("the stated cost must be checked, not dropped (booked at {cost})"),
    }
}

fn amount(n: Decimal, currency: &str) -> Amount {
    Amount::new(n, currency)
}

/// The issue's case: 99.00 EUR stated, the pool is 11.00 EUR.
#[test]
fn a_cost_the_pool_is_not_is_refused_naming_the_pool() {
    let result = book(
        eur_pool(),
        &sale(
            dec!(-1),
            per_unit(dec!(99.00), "EUR"),
            Some(amount(dec!(99.00), "EUR")),
        ),
    );
    let (stated, pool, total) = mismatch(result.clone());
    assert_eq!(stated, amount(dec!(99.00), "EUR"));
    assert_eq!(pool, amount(dec!(11.00), "EUR"));
    assert!(!total);
    let message = result.unwrap_err().to_string();
    assert!(
        message.contains("AVERAGE pool of X costs 11.00 EUR per unit, not the 99.00 EUR"),
        "{message}"
    );
}

#[test]
fn the_pools_own_cost_books() {
    let cost = book(
        eur_pool(),
        &sale(
            dec!(-1),
            per_unit(dec!(11.00), "EUR"),
            Some(amount(dec!(11.00), "EUR")),
        ),
    );
    assert_eq!(cost.unwrap(), dec!(11));
}

/// 10 X at 100 and 5 X at 120 USD: a pool of 15 at 1600/15 = 106.666… USD,
/// the pool #2398's `{*}` tests use.
fn sixteen_hundred_pool() -> Vec<Transaction> {
    buys(&[(dec!(10), dec!(100)), (dec!(5), dec!(120))], "USD")
}

/// The decided rule (#2603): a claim holds when it is a correct rounding of
/// the pool's exact average at the precision written, half a unit in its last
/// place, inclusive. `{106.67}` and `{107}` round 106.666… correctly;
/// `{160.67}` does not.
#[test]
fn a_claim_holds_when_it_is_a_correct_rounding_of_the_average() {
    let cash = Some(amount(dec!(106.67), "USD"));
    for ok in [dec!(106.67), dec!(106.7), dec!(107), dec!(106.666667)] {
        assert!(
            book(
                sixteen_hundred_pool(),
                &sale(dec!(-1), per_unit(ok, "USD"), cash.clone())
            )
            .is_ok(),
            "{ok} rounds 106.666… correctly"
        );
    }
    for (bad, shown) in [
        (dec!(160.67), dec!(106.67)),
        (dec!(106.66), dec!(106.67)),
        (dec!(106), dec!(107)),
        (dec!(106.6), dec!(106.7)),
    ] {
        let (stated, pool, total) = mismatch(book(
            sixteen_hundred_pool(),
            &sale(dec!(-1), per_unit(bad, "USD"), cash.clone()),
        ));
        assert_eq!(stated, amount(bad, "USD"));
        assert_eq!(
            pool,
            amount(shown, "USD"),
            "{bad}: the pool to the places written"
        );
        assert!(!total);
    }
}

/// The rule reads only the claim and the pool, never the transaction's other
/// postings: `{106.67 USD}` beside cash written to the tenth of a cent holds
/// (the transaction-tolerance rule this replaces refused it), as it does
/// beside cash to the cent, beside whole dollars, and with the cash elided.
#[test]
fn the_verdict_does_not_depend_on_the_other_postings() {
    for cash in [
        Some(amount(dec!(106.667), "USD")),
        Some(amount(dec!(106.67), "USD")),
        Some(amount(dec!(107), "USD")),
        None,
    ] {
        for ok in [dec!(106.67), dec!(107)] {
            assert!(
                book(
                    sixteen_hundred_pool(),
                    &sale(dec!(-1), per_unit(ok, "USD"), cash.clone())
                )
                .is_ok(),
                "{ok} beside {cash:?}"
            );
        }
        let _ = mismatch(book(
            sixteen_hundred_pool(),
            &sale(dec!(-1), per_unit(dec!(106.66), "USD"), cash.clone()),
        ));
    }
}

/// Exactly half a unit away holds: a pool of 100.5 is 100 or 101 to whole
/// units, whichever way the author rounded the tie. To tenths it is 100.5,
/// and 100.4 or 100.6 (0.1 away, more than 0.05) is refused.
#[test]
fn exactly_half_a_unit_away_holds() {
    let pool = || buys(&[(dec!(10), dec!(100)), (dec!(10), dec!(101))], "USD");
    for ok in [dec!(100), dec!(101), dec!(100.5), dec!(100.500)] {
        assert!(
            book(pool(), &sale(dec!(-1), per_unit(ok, "USD"), None)).is_ok(),
            "{ok}"
        );
    }
    for bad in [dec!(100.4), dec!(100.6), dec!(100.499), dec!(99)] {
        let _ = mismatch(book(pool(), &sale(dec!(-1), per_unit(bad, "USD"), None)));
    }
}

/// A `{{T}}` total is compared as a total against what the units sold cost
/// at the exact average, with half a unit in T's last place: it is not
/// divided by the units first.
#[test]
fn a_total_cost_is_compared_as_a_total() {
    let cash = |n| Some(amount(n, "USD"));
    // The whole pool of 3 cost exactly 500.
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-3), total(dec!(500.00), "USD"), cash(dec!(500.00)))
        )
        .is_ok()
    );
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-3), total(dec!(500), "USD"), cash(dec!(500)))
        )
        .is_ok()
    );
    // One unit's share, 166.666…, to the cent.
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-1), total(dec!(166.67), "USD"), cash(dec!(166.67)))
        )
        .is_ok()
    );
    // 500.01 is 0.01 from 500, more than half a cent. Divided by 3 first it
    // would be 0.0033 a unit and pass: the total is compared as a total.
    let (stated, pool, is_total) = mismatch(book(
        thirds_pool(),
        &sale(dec!(-3), total(dec!(500.01), "USD"), cash(dec!(500.01))),
    ));
    assert!(is_total);
    assert_eq!(stated, amount(dec!(500.01), "USD"));
    assert_eq!(pool, amount(dec!(500.00), "USD"));
    let (_, pool, _) = mismatch(book(
        thirds_pool(),
        &sale(dec!(-3), total(dec!(510.00), "USD"), cash(dec!(510.00))),
    ));
    assert_eq!(pool, amount(dec!(500.00), "USD"));
    // Two units of 500/3 cost 333.333…: 333.33 holds, 333.34 does not.
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-2), total(dec!(333.33), "USD"), cash(dec!(333.33)))
        )
        .is_ok()
    );
    let (_, pool, _) = mismatch(book(
        thirds_pool(),
        &sale(dec!(-2), total(dec!(333.34), "USD"), cash(dec!(333.34))),
    ));
    assert_eq!(pool, amount(dec!(333.33), "USD"));
}

/// A compound `{a # b}` states the total `a × units + b`, its two parts each
/// rounded to the places written, so it holds within `units × w(a) + w(b)`
/// of what the units cost at the average (the reading `{*, a # b}` uses).
#[test]
fn a_compound_cost_is_held_to_both_parts_precision() {
    let spec = |a, b| {
        CostSpec::empty()
            .with_number(CostNumber::Compound {
                per_unit: a,
                total: b,
            })
            .with_currency("USD")
    };
    let cash = Some(amount(dec!(333.33), "USD"));
    // 2 units of 500/3 cost 333.333…: 166 × 2 + 1.33 = 333.33 is within
    // 2 × 0.5 + 0.005 of it; 167 × 2 + 0 = 334 within 2 × 0.5 + 0.5 (0.67 ≤
    // 1.5); 166.67 × 2 + 0.00 = 333.34 within 2 × 0.005 + 0.005.
    for (a, b) in [
        (dec!(166), dec!(1.33)),
        (dec!(167), dec!(0)),
        (dec!(166.67), dec!(0.00)),
    ] {
        assert!(
            book(thirds_pool(), &sale(dec!(-2), spec(a, b), cash.clone())).is_ok(),
            "{{{a} # {b}}}"
        );
    }
    // 165 × 2 + 0 = 330 is 3.33 away, more than 1.5.
    let (stated, pool, is_total) = mismatch(book(
        thirds_pool(),
        &sale(dec!(-2), spec(dec!(165), dec!(0)), cash.clone()),
    ));
    assert!(is_total);
    assert_eq!(stated, amount(dec!(330), "USD"));
    assert_eq!(pool, amount(dec!(333), "USD"));
    // 166.65 × 2 + 0.00 = 333.30 is 0.033 away, more than 2 × 0.005 + 0.005.
    let _ = mismatch(book(
        thirds_pool(),
        &sale(dec!(-2), spec(dec!(166.65), dec!(0.00)), cash),
    ));
}
/// Covering a short pool: the claim is the pool's per-unit cost, positive, as
/// for a long one.
#[test]
fn a_short_pool_is_held_to_its_average_too() {
    let shorts = vec![
        txn(
            1,
            vec![
                Posting::new(STOCK, Amount::new(dec!(-1), "X"))
                    .with_cost(per_unit(dec!(100), "USD")),
                Posting::new("Assets:Cash", Amount::new(dec!(100), "USD")),
            ],
        ),
        txn(
            2,
            vec![
                Posting::new(STOCK, Amount::new(dec!(-1), "X"))
                    .with_cost(per_unit(dec!(200), "USD")),
                Posting::new("Assets:Cash", Amount::new(dec!(200), "USD")),
            ],
        ),
    ];
    let cover = |cost| {
        sale(
            dec!(1),
            per_unit(cost, "USD"),
            Some(amount(dec!(-150.00), "USD")),
        )
    };
    assert_eq!(
        book(shorts.clone(), &cover(dec!(150.00))).unwrap(),
        dec!(150)
    );
    let (_, pool, _) = mismatch(book(shorts, &cover(dec!(140.00))));
    assert_eq!(pool, amount(dec!(150.00), "USD"));
}

/// An empty spec, or one naming only the currency, states no cost and books
/// at the pool as before.
#[test]
fn a_spec_without_a_number_still_books_at_the_pool() {
    assert_eq!(
        book(
            eur_pool(),
            &sale(
                dec!(-1),
                CostSpec::empty(),
                Some(amount(dec!(11.00), "EUR"))
            )
        )
        .unwrap(),
        dec!(11)
    );
    assert_eq!(
        book(
            eur_pool(),
            &sale(dec!(-1), CostSpec::empty().with_currency("EUR"), None)
        )
        .unwrap(),
        dec!(11)
    );
}

/// The currency is checked first (#2589), with its own error.
#[test]
fn a_wrong_currency_keeps_its_own_error() {
    let result = book(
        eur_pool(),
        &sale(
            dec!(-1),
            per_unit(dec!(11.00), "USD"),
            Some(amount(dec!(11.00), "USD")),
        ),
    );
    match result {
        Err(BookingError::Inventory(e)) => {
            assert!(matches!(e.error, CoreError::NoMatchingLot { .. }), "{e}");
        }
        other => panic!("expected no matching lot, got {other:?}"),
    }
}

/// `{*}` on an AVERAGE account states its claim through the merge's own check
/// (#2398), not this one, and still refuses a cost the pool is not.
#[test]
fn a_merge_spec_on_an_average_account_keeps_its_own_check() {
    let merge = |value| CostSpec {
        merge: true,
        ..per_unit(value, "EUR")
    };
    let cash = Some(amount(dec!(11.00), "EUR"));
    assert_eq!(
        book(
            eur_pool(),
            &sale(dec!(-1), merge(dec!(11.00)), cash.clone())
        )
        .unwrap(),
        dec!(11)
    );
    match book(eur_pool(), &sale(dec!(-1), merge(dec!(99.00)), cash)) {
        Err(BookingError::Inventory(e)) => {
            assert!(
                matches!(e.error, CoreError::MergeSpecMismatch { .. }),
                "{e}"
            );
        }
        other => panic!("expected a merge spec mismatch, got {other:?}"),
    }
}

/// A partial sale leaves the remainder with its exact total (#2427), and a
/// later claim is held against that, not against a rounded average.
#[test]
fn a_later_claim_is_held_to_the_remainders_exact_total() {
    let mut history = thirds_pool();
    history.push(sale(
        dec!(-1),
        CostSpec::empty(),
        Some(amount(dec!(166.67), "USD")),
    ));
    // 2 X left of the pool's 500, at whatever the first sale took.
    let cost = book(
        history.clone(),
        &sale(
            dec!(-2),
            total(dec!(333.33), "USD"),
            Some(amount(dec!(333.33), "USD")),
        ),
    );
    assert!(cost.is_ok(), "{cost:?}");
    let (_, pool, _) = mismatch(book(
        history,
        &sale(
            dec!(-2),
            total(dec!(340.00), "USD"),
            Some(amount(dec!(340.00), "USD")),
        ),
    ));
    assert_eq!(pool, amount(dec!(333.33), "USD"));
}
