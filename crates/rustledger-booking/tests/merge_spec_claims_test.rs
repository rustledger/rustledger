//! What a `{*}` spec states besides the `*` is checked, not dropped (#2398).
//!
//! `{*}` computes its cost, so a cost, currency, date or label beside it can
//! only be a claim about the merged pool. Every one of them used to be
//! discarded without a word: `{*, 100.00 USD}` booked at the pool's 106.67, a
//! currency the pool is not held in passed, and so did a date or label naming
//! a lot the merge never builds.

use rustledger_booking::{BookingEngine, BookingError};
use rustledger_core::{
    Amount, BookingError as CoreError, BookingMethod, CostNumber, CostSpec, Decimal,
    MergeSpecMismatch, Posting, Transaction,
};

fn date(d: u32) -> rustledger_core::NaiveDate {
    rustledger_core::naive_date(2024, 1, d).unwrap()
}

fn dec(n: &str) -> Decimal {
    n.parse().unwrap()
}

fn amount(n: &str, cur: &str) -> Amount {
    Amount::new(dec(n), cur)
}

const fn merge() -> CostSpec {
    CostSpec {
        number: None,
        currency: None,
        date: None,
        label: None,
        merge: true,
    }
}

fn per_unit(n: &str) -> Option<CostNumber> {
    Some(CostNumber::PerUnit { value: dec(n) })
}

/// 10 X at 100 and 5 X at 120: a pool of 1600/15 = 106.666…, a quotient no
/// ledger can write out, which is the case the precision rule is for.
fn engine() -> BookingEngine {
    engine_with(&[("10", "100.00"), ("5", "120.00")])
}

/// An engine holding `(units, per-unit cost)` lots of X, bought on days 1, 2, ….
fn engine_with(lots: &[(&str, &str)]) -> BookingEngine {
    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
    for (day, (units, cost)) in (1u32..).zip(lots.iter().copied()) {
        let mut buy = Posting::new("Assets:Broker", amount(units, "X"));
        buy.cost = Some(Box::new(CostSpec {
            number: per_unit(cost),
            currency: Some("USD".into()),
            date: Some(date(day)),
            label: None,
            merge: false,
        }));
        let paid = -(dec(units) * dec(cost));
        let txn = Transaction::new(date(day), "buy")
            .with_synthesized_posting(buy)
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(paid, "USD")));
        engine.apply(&txn).expect("buys apply");
    }
    engine
}

/// Sell 5 X with `spec`, returning what booking said.
fn sell(spec: CostSpec) -> Result<Transaction, BookingError> {
    sell_from(&engine(), spec)
}

fn sell_from(engine: &BookingEngine, spec: CostSpec) -> Result<Transaction, BookingError> {
    let mut sale = Posting::new("Assets:Broker", amount("-5", "X"));
    sale.cost = Some(Box::new(spec));
    let txn = Transaction::new(date(10), "sell")
        .with_synthesized_posting(sale)
        .with_synthesized_posting(Posting::new("Assets:Cash", amount("650.00", "USD")));
    engine.book(&txn).map(|b| b.transaction)
}

/// The mismatch booking reported, or a panic naming what it did instead.
fn mismatch(spec: CostSpec) -> MergeSpecMismatch {
    match sell(spec) {
        Err(BookingError::Inventory(e)) => match e.error {
            CoreError::MergeSpecMismatch { currency, detail } => {
                assert_eq!(currency.as_str(), "X");
                detail
            }
            other => panic!("expected a merge spec mismatch, got {other}"),
        },
        Err(other) => panic!("expected a merge spec mismatch, got {other}"),
        Ok(_) => panic!("the claim must be checked, not dropped"),
    }
}

/// A per-unit cost holds when it is the pool at the precision written.
#[test]
fn a_per_unit_cost_is_the_pool_to_the_places_written() {
    for ok in ["106.67", "106.7", "107", "106.666667"] {
        let spec = CostSpec {
            number: per_unit(ok),
            currency: Some("USD".into()),
            ..merge()
        };
        assert!(
            sell(spec).is_ok(),
            "{ok} is the pool 106.666… written to its places"
        );
    }
    for (bad, pool) in [("106.66", "106.67"), ("100.00", "106.67"), ("106", "107")] {
        let spec = CostSpec {
            number: per_unit(bad),
            currency: Some("USD".into()),
            ..merge()
        };
        assert_eq!(
            mismatch(spec),
            MergeSpecMismatch::PerUnit {
                stated: amount(bad, "USD"),
                pool: amount(pool, "USD"),
            },
            "{bad}: the pool is reported to the places the spec writes"
        );
    }
}

/// Exactly half a unit away still holds: a pool of 100.5 is 100 or 101 to
/// whole units, depending only on which way the author rounded the tie.
#[test]
fn a_cost_exactly_half_a_unit_from_the_pool_holds() {
    for stated in ["100", "101"] {
        let spec = CostSpec {
            number: per_unit(stated),
            currency: Some("USD".into()),
            ..merge()
        };
        let halfway = engine_with(&[("10", "100"), ("10", "101")]);
        assert!(
            sell_from(&halfway, spec).is_ok(),
            "{stated} is the pool 100.5, rounded either way"
        );
    }
}

/// The message names the account, the commodity, and both numbers.
#[test]
fn the_message_says_what_the_pool_costs() {
    let spec = CostSpec {
        number: per_unit("100.00"),
        currency: Some("USD".into()),
        ..merge()
    };
    let err = sell(spec).expect_err("100.00 is not the pool");
    assert_eq!(
        err.to_string(),
        "Assets:Broker: {*} merge of X: the merged pool costs 106.67 USD per unit, \
         not the 100.00 USD the cost spec states"
    );
}

/// A total, and a compound cost, are checked as the total they state.
#[test]
fn a_total_or_compound_cost_is_checked_as_a_total() {
    let total = |n: &str| CostSpec {
        number: Some(CostNumber::Total { value: dec(n) }),
        currency: Some("USD".into()),
        ..merge()
    };
    let compound = |a: &str, b: &str| CostSpec {
        number: Some(CostNumber::Compound {
            per_unit: dec(a),
            total: dec(b),
        }),
        currency: Some("USD".into()),
        ..merge()
    };
    // 5 X at 106.666… cost 533.333….
    assert!(sell(total("533.33")).is_ok());
    assert!(sell(total("533")).is_ok());
    // 5 × 100.00 + 33.34 = 533.34: each part may be off by half a cent, and
    // the per-unit part's half cent counts once per unit.
    assert!(sell(compound("100.00", "33.34")).is_ok());
    assert_eq!(
        mismatch(total("550.00")),
        MergeSpecMismatch::Total {
            stated: amount("550.00", "USD"),
            pool: amount("533.33", "USD"),
        }
    );
    assert_eq!(
        mismatch(compound("100.00", "30.00")),
        MergeSpecMismatch::Total {
            stated: amount("530.00", "USD"),
            pool: amount("533.33", "USD"),
        }
    );
}

/// A correct total as long as `Decimal` holds is not refused for the pool's
/// rounding.
///
/// 37 at 292 and 29 at 734 pool at 32090/66 = 486.21…, which `Decimal`
/// rounds. Selling 50 checks the stated total against `50 × pool`, carrying
/// that rounding fifty times, while `1604500/66` rounds once: the two land
/// 0.000000000000000000000001 apart, which half a unit in the last place
/// written does not cover. One of 32 such refusals in 150 generated claims.
#[test]
fn a_full_precision_total_allows_for_the_pools_rounding() {
    let pool = engine_with(&[("37", "292"), ("29", "734")]);
    let stated = dec("1604500") / dec("66");
    let spec = CostSpec {
        number: Some(CostNumber::Total { value: stated }),
        currency: Some("USD".into()),
        ..merge()
    };
    let mut sale = Posting::new("Assets:Broker", amount("-50", "X"));
    sale.cost = Some(Box::new(spec));
    let txn = Transaction::new(date(10), "sell")
        .with_synthesized_posting(sale)
        .with_synthesized_posting(Posting::new("Assets:Cash", amount("24310.61", "USD")));
    pool.book(&txn)
        .expect("1604500/66 is what 50 units cost at 32090/66 per unit");
}

/// A correct total built from separately rounded parts is not refused either.
///
/// 38 at 873 and 8 at 523; selling 40 written as `40*33174/46 + 40*4184/46`,
/// as the parser evaluates it: two divisions, each rounded, then a rounded
/// sum. It lands two units in the last place from `40 × pool`, more than one
/// rounding explains, so a number that fills `Decimal`'s digits is held to the
/// place before its last.
#[test]
fn a_total_summed_from_rounded_parts_is_not_refused_for_its_last_digit() {
    let pool = engine_with(&[("38", "873"), ("8", "523")]);
    let stated = dec("40") * dec("33174") / dec("46") + dec("40") * dec("4184") / dec("46");
    let spec = CostSpec {
        number: Some(CostNumber::Total { value: stated }),
        currency: Some("USD".into()),
        ..merge()
    };
    let mut sale = Posting::new("Assets:Broker", amount("-40", "X"));
    sale.cost = Some(Box::new(spec));
    let txn = Transaction::new(date(10), "sell")
        .with_synthesized_posting(sale)
        .with_synthesized_posting(Posting::new("Assets:Cash", amount("32485.22", "USD")));
    pool.book(&txn)
        .expect("the parts sum to what 40 units cost at the pool's price");
    // Still a claim: the same total 0.01 off is refused.
    let mut off = txn;
    let cost = off.postings[0].cost.as_mut().unwrap();
    cost.number = Some(CostNumber::Total {
        value: stated + dec("0.01"),
    });
    assert!(
        pool.book(&off).is_err(),
        "a total 0.01 off is not the pool's"
    );
}

/// A currency must be the pool's; alone it asserts only that.
#[test]
fn a_currency_must_be_the_pools() {
    let with = |cur: &str, number| CostSpec {
        number,
        currency: Some(cur.into()),
        ..merge()
    };
    assert!(sell(with("USD", None)).is_ok());
    for number in [None, per_unit("106.67")] {
        assert_eq!(
            mismatch(with("EUR", number)),
            MergeSpecMismatch::Currency {
                stated: "EUR".into(),
                pool: "USD".into(),
            }
        );
    }
}

/// The merge builds one undated, unlabeled lot, so a date or label names none.
#[test]
fn a_date_or_label_describes_no_lot() {
    let dated = CostSpec {
        date: Some(date(1)),
        ..merge()
    };
    assert_eq!(
        mismatch(dated),
        MergeSpecMismatch::DateOrLabel {
            stated: "2024-01-01".into(),
        }
    );
    let labeled = CostSpec {
        label: Some("lot-a".into()),
        ..merge()
    };
    assert_eq!(
        mismatch(labeled),
        MergeSpecMismatch::DateOrLabel {
            stated: "\"lot-a\"".into(),
        }
    );
}

/// An accepted claim books the POOL, not the rounded number the spec wrote.
///
/// The stated cost is checked and then set aside: booking at 106.67 would
/// leave the sale and the pool 0.0033 apart per unit, and `apply` re-runs the
/// merge and compares it with what booking recorded (#2068).
#[test]
fn an_accepted_cost_books_the_pool_itself() {
    let spec = CostSpec {
        number: per_unit("106.67"),
        currency: Some("USD".into()),
        ..merge()
    };
    let booked = sell(spec).expect("106.67 is the pool, to cents");
    let cost = booked.postings[0].cost.as_deref().expect("booked cost");
    let pool = dec("1600") / dec("15");
    assert_eq!(cost.number.and_then(|n| n.per_unit()), Some(pool));
    assert!(cost.merge, "the marker is carried into apply");

    engine()
        .apply(&booked)
        .expect("the booked merge applies against the state it was booked on");
}

/// A stated cost of `-Decimal::MAX` is a mismatch, not a panic: `pool -
/// stated` leaves the range, and `rust_decimal` panics there.
#[test]
fn a_stated_cost_out_of_the_pools_range_is_reported_not_panicked() {
    let spec = CostSpec {
        number: per_unit("-79228162514264337593543950335"),
        currency: Some("USD".into()),
        ..merge()
    };
    let _ = sell(spec).expect_err("a cost that far from the pool is refused");
}
