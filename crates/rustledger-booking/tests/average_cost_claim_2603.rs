//! A cost written on an AVERAGE sale is checked against the pool, not dropped
//! (#2603).
//!
//! An AVERAGE reduction sells at the pool's average cost. Under every other
//! method a written cost is a filter that a lot must pass, but here it was
//! ignored: `-1 X {99.00 EUR}` from a pool held at 11.00 EUR booked at 11.00.
//! The claim now holds when it is within the transaction's tolerance for the
//! cost currency of the pool's EXACT average (a transaction with none there
//! falls back to the precision the claim is written to). Beancount has no
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

/// A rounded average holds within the transaction's tolerance: cash to the
/// cent gives USD 0.005, and 166.67 is 0.0033 from 500/3.
#[test]
fn a_rounded_average_holds_within_the_transactions_tolerance() {
    let cash = Some(amount(dec!(166.67), "USD"));
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-1), per_unit(dec!(166.67), "USD"), cash.clone())
        )
        .is_ok()
    );
    // 0.0067 away: outside 0.005.
    let (stated, pool, _) = mismatch(book(
        thirds_pool(),
        &sale(dec!(-1), per_unit(dec!(166.66), "USD"), cash),
    ));
    assert_eq!(stated, amount(dec!(166.66), "USD"));
    assert_eq!(pool, amount(dec!(166.67), "USD"));
}

/// Never looser than the transaction's tolerance: cash to the tenth of a cent
/// gives 0.0005, so 166.67 (0.0033 away) no longer holds, and the message
/// shows the pool to the place that tells the two apart.
#[test]
fn a_finer_transaction_tolerance_is_never_loosened() {
    let (stated, pool, _) = mismatch(book(
        thirds_pool(),
        &sale(
            dec!(-1),
            per_unit(dec!(166.67), "USD"),
            Some(amount(dec!(166.670), "USD")),
        ),
    ));
    assert_eq!(stated, amount(dec!(166.67), "USD"));
    assert_eq!(pool, amount(dec!(166.667), "USD"));
    assert!(
        book(
            thirds_pool(),
            &sale(
                dec!(-1),
                per_unit(dec!(166.667), "USD"),
                Some(amount(dec!(166.667), "USD")),
            ),
        )
        .is_ok()
    );
}

/// A transaction with no USD tolerance (cash elided) holds the claim to the
/// precision it is written to, as `{*}` does: half a unit in its last place.
#[test]
fn without_a_tolerance_the_claim_is_held_to_its_written_precision() {
    for ok in [dec!(166.67), dec!(166.7), dec!(167), dec!(166.666667)] {
        assert!(
            book(thirds_pool(), &sale(dec!(-1), per_unit(ok, "USD"), None)).is_ok(),
            "{ok} is 500/3 to its places"
        );
    }
    for (bad, shown) in [
        (dec!(166.66), dec!(166.67)),
        (dec!(166), dec!(167)),
        (dec!(100.00), dec!(166.67)),
    ] {
        let (_, pool, _) = mismatch(book(
            thirds_pool(),
            &sale(dec!(-1), per_unit(bad, "USD"), None),
        ));
        assert_eq!(pool, amount(shown, "USD"), "{bad}");
    }
}

/// A `{{T}}` total states `T / |units|`, compared against the pool's exact
/// total: the whole pool of 3 cost exactly 500.
#[test]
fn a_total_cost_is_compared_against_the_exact_pool_total() {
    let cash = |n| Some(amount(n, "USD"));
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-3), total(dec!(500.00), "USD"), cash(dec!(500.00)))
        )
        .is_ok()
    );
    // One unit's share, rounded to the cent: 0.0033 per unit from 500/3.
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-1), total(dec!(166.67), "USD"), cash(dec!(166.67)))
        )
        .is_ok()
    );
    let (stated, pool, is_total) = mismatch(book(
        thirds_pool(),
        &sale(dec!(-3), total(dec!(510.00), "USD"), cash(dec!(510.00))),
    ));
    assert!(is_total);
    assert_eq!(stated, amount(dec!(510.00), "USD"));
    assert_eq!(pool, amount(dec!(500.00), "USD"));
    // Within the 0.005 per-unit tolerance on each of 3 units is 0.015 on the
    // total; 500.02 is not.
    assert!(
        book(
            thirds_pool(),
            &sale(dec!(-3), total(dec!(500.01), "USD"), cash(dec!(500.01)))
        )
        .is_ok()
    );
    let (_, pool, _) = mismatch(book(
        thirds_pool(),
        &sale(dec!(-3), total(dec!(500.02), "USD"), cash(dec!(500.02))),
    ));
    assert_eq!(pool, amount(dec!(500.00), "USD"));
}

/// A compound `{a # b}` states `a + b / |units|`.
#[test]
fn a_compound_cost_states_its_combined_per_unit() {
    let spec = |a, b| {
        CostSpec::empty()
            .with_number(CostNumber::Compound {
                per_unit: a,
                total: b,
            })
            .with_currency("EUR")
    };
    let cash = Some(amount(dec!(22.00), "EUR"));
    assert!(
        book(
            eur_pool(),
            &sale(dec!(-2), spec(dec!(10), dec!(2.00)), cash.clone())
        )
        .is_ok()
    );
    let (stated, pool, is_total) = mismatch(book(
        eur_pool(),
        &sale(dec!(-2), spec(dec!(10), dec!(4.00)), cash),
    ));
    assert!(is_total);
    assert_eq!(stated, amount(dec!(24.00), "EUR"));
    assert_eq!(pool, amount(dec!(22.00), "EUR"));
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
