//! Every realization of a booked ledger agrees with booking's record (#2390).
//!
//! Booking records on each posting whether it reduced lots or augmented the
//! inventory ([`rustledger_core::Posting::booking`]). Three consumers realize
//! the booked stream and now read that record instead of asking again:
//! `BookingEngine::apply`, this crate's inventory pass (`update_inventories`)
//! and the query's replay (`BookingEngine::begin_replay_as_booked`). Each was
//! once caught disagreeing with booking (#2368, #2380, #2384).
//!
//! The property, over every booking method, `{*}` merges, partial and
//! multi-lot reductions, same-transaction oversells, zero lots and cost-less
//! positions in an `AVERAGE` pool:
//!
//! 1. each consumer, reading the record, holds exactly the lots the booking
//!    engine holds;
//! 2. with the record forgotten, each consumer asks the inventory, and holds
//!    the same lots — the record changes no result, it only stops the
//!    question being asked twice;
//! 3. the validator reports the same diagnostics either way.
//!
//! `the_comparison_can_report_a_disagreement` shows the comparison is not
//! vacuous: a single flipped decision is reported.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_booking::BookingEngine;
use rustledger_core::{
    Amount, BookingDecision, BookingMethod, CostNumber, CostSpec, Directive, Inventory, NaiveDate,
    Open, Posting, Transaction, naive_date,
};

use crate::{ValidationOptions, ValidationSession};

const STOCK: &str = "Assets:Stock";
const CASH: &str = "Assets:Cash";

fn day(n: u32) -> NaiveDate {
    naive_date(2024, 1 + (n / 28) % 12, 1 + n % 28).expect("valid date")
}

/// One posting on the stock account.
#[derive(Debug, Clone)]
enum Leg {
    Buy {
        units: u32,
        cost: u32,
    },
    SellAt {
        units: u32,
        cost: u32,
    },
    SellAny {
        units: u32,
    },
    SellMerged {
        units: u32,
    },
    /// A cost-less position, which `AVERAGE` pools with the lots.
    Plain {
        units: i32,
    },
    /// A zero-unit lot (#2385).
    Zero {
        cost: u32,
    },
}

fn leg() -> impl Strategy<Value = Leg> {
    prop_oneof![
        3 => (1u32..6, 100u32..103).prop_map(|(units, cost)| Leg::Buy { units, cost }),
        3 => (1u32..6, 100u32..103).prop_map(|(units, cost)| Leg::SellAt { units, cost }),
        3 => (1u32..6).prop_map(|units| Leg::SellAny { units }),
        1 => (1u32..6).prop_map(|units| Leg::SellMerged { units }),
        1 => (-3i32..4).prop_map(|units| Leg::Plain { units }),
        1 => (100u32..103).prop_map(|cost| Leg::Zero { cost }),
    ]
}

fn method() -> impl Strategy<Value = BookingMethod> {
    prop::sample::select(vec![
        BookingMethod::Strict,
        BookingMethod::StrictWithSize,
        BookingMethod::Fifo,
        BookingMethod::Lifo,
        BookingMethod::Hifo,
        BookingMethod::Average,
        BookingMethod::None,
    ])
}

fn usd(cost: u32) -> CostSpec {
    CostSpec::empty()
        .with_number(CostNumber::PerUnit {
            value: Decimal::from(cost),
        })
        .with_currency("USD")
}

fn posting(leg: &Leg) -> Posting {
    let units = |n: i64| Amount::new(Decimal::from(n), "X");
    match *leg {
        Leg::Buy { units: n, cost } => Posting::new(STOCK, units(n.into())).with_cost(usd(cost)),
        Leg::SellAt { units: n, cost } => {
            Posting::new(STOCK, units(-i64::from(n))).with_cost(usd(cost))
        }
        Leg::SellAny { units: n } => {
            Posting::new(STOCK, units(-i64::from(n))).with_cost(CostSpec::empty())
        }
        Leg::SellMerged { units: n } => {
            Posting::new(STOCK, units(-i64::from(n))).with_cost(CostSpec::empty().with_merge())
        }
        Leg::Plain { units: n } => Posting::new(STOCK, units(n.into())),
        Leg::Zero { cost } => Posting::new(STOCK, units(0)).with_cost(usd(cost)),
    }
}

/// The ledger's opens and its transactions as written: seed buys, then the
/// generated transactions, each balanced by an elided cash posting.
fn ledger(
    account_method: Option<BookingMethod>,
    seeds: &[(u32, u32)],
    txns: &[Vec<Leg>],
) -> (Vec<Directive>, Vec<Transaction>) {
    let mut open = Open::new(day(0), STOCK);
    if let Some(m) = account_method {
        open = open.with_booking(m.to_string());
    }
    let opens = vec![
        Directive::Open(open),
        Directive::Open(Open::new(day(0), CASH)),
    ];
    let seed = seeds
        .iter()
        .map(|&(units, cost)| vec![Leg::Buy { units, cost }]);
    let written = seed
        .chain(txns.iter().cloned())
        .enumerate()
        .map(|(i, legs)| {
            let mut txn = Transaction::new(day(u32::try_from(i).unwrap_or(0) + 1), "generated");
            for leg in &legs {
                txn = txn.with_synthesized_posting(posting(leg));
            }
            txn.with_synthesized_posting(Posting::auto(CASH))
        })
        .collect();
    (opens, written)
}

/// The stock account's lots, normalized for comparison: non-empty
/// positions as `(units, cost)`, sorted.
fn lots(inv: Option<&Inventory>) -> Vec<String> {
    let mut out: Vec<String> = inv
        .map(|inv| {
            inv.positions()
                .filter(|p| !p.is_empty())
                .map(|p| format!("{:?} {:?}", p.units, p.cost))
                .collect()
        })
        .unwrap_or_default();
    out.sort();
    out
}

fn forgotten(booked: &[Transaction]) -> Vec<Transaction> {
    booked
        .iter()
        .cloned()
        .map(|mut txn| {
            txn.forget_booking();
            txn
        })
        .collect()
}

/// What each consumer holds after realizing `booked`.
#[derive(Debug, PartialEq)]
struct Realized {
    apply: Vec<String>,
    replay: Vec<String>,
    validator: Vec<String>,
    diagnostics: Vec<String>,
}

fn realize(default: BookingMethod, opens: &[Directive], booked: &[Transaction]) -> Realized {
    // A failure is part of what a consumer did: it is kept in its lots, so
    // it can only compare equal to booking's (which never has one) by not
    // happening. A booked transaction must apply and replay.
    let mut apply = BookingEngine::for_ledger(default, opens);
    let mut apply_failures = Vec::new();
    for txn in booked {
        if let Err(e) = apply.apply(txn) {
            apply_failures.push(format!("apply failed: {e}"));
        }
    }
    let mut replay = BookingEngine::for_ledger(default, opens);
    let mut replay_failures = Vec::new();
    for txn in booked {
        if let Err(e) = replay.replay_transaction_as_booked(txn) {
            replay_failures.push(format!("replay failed: {e}"));
        }
    }
    let directives: Vec<Directive> = opens
        .iter()
        .cloned()
        .chain(booked.iter().cloned().map(Directive::Transaction))
        .collect();
    let options = ValidationOptions {
        default_booking_method: default,
        ..ValidationOptions::default()
    };
    let today = day(400);
    let session = ValidationSession::new(options);
    let (session, mut errors) = session.run_early(&directives, today);
    let (session, late) = session.run_late(&directives, today);
    errors.extend(late);
    let validator = lots(session.state.inventory(STOCK));
    errors.extend(session.finalize());
    Realized {
        apply: [lots(apply.inventory(&STOCK.into())), apply_failures].concat(),
        replay: [lots(replay.inventory(&STOCK.into())), replay_failures].concat(),
        validator,
        diagnostics: errors.iter().map(ToString::to_string).collect(),
    }
}

/// Book the ledger the way the loader does, keeping what booked.
fn book(
    default: BookingMethod,
    opens: &[Directive],
    written: Vec<Transaction>,
) -> (BookingEngine, Vec<Transaction>) {
    let mut engine = BookingEngine::for_ledger(default, opens);
    let mut booked = Vec::new();
    for mut txn in written {
        if engine.book_interpolate_apply(&mut txn).is_ok() {
            booked.push(txn);
        }
    }
    (engine, booked)
}

fn check(
    default: BookingMethod,
    account_method: Option<BookingMethod>,
    seeds: &[(u32, u32)],
    txns: &[Vec<Leg>],
) -> Result<(), TestCaseError> {
    let (opens, written) = ledger(account_method, seeds, txns);
    let (engine, booked) = book(default, &opens, written);
    let held = lots(engine.inventory(&STOCK.into()));

    let recorded = realize(default, &opens, &booked);
    prop_assert_eq!(&recorded.apply, &held, "apply disagrees with booking");
    prop_assert_eq!(&recorded.replay, &held, "the replay disagrees with booking");
    prop_assert_eq!(
        &recorded.validator,
        &held,
        "the validator disagrees with booking"
    );

    let asked = realize(default, &opens, &forgotten(&booked));
    prop_assert_eq!(
        &asked,
        &recorded,
        "asking the inventory gives a different result than the record"
    );
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2048))]

    /// Small lots, so a transaction routinely sells a lot out and keeps
    /// selling (the same-transaction oversell the booking fuzzer misses).
    #[test]
    fn every_realization_agrees_with_the_record(
        default in method(),
        account_method in prop::option::of(method()),
        seeds in prop::collection::vec((1u32..5, 100u32..103), 1..4),
        txns in prop::collection::vec(prop::collection::vec(leg(), 1..5), 1..5),
    ) {
        check(default, account_method, &seeds, &txns)?;
    }
}

/// A sale past a lot its own transaction emptied, beside a buy: the #2368
/// shape, under every method.
#[test]
fn a_transaction_that_sells_past_a_lot_agrees_everywhere() {
    for m in [
        BookingMethod::Strict,
        BookingMethod::StrictWithSize,
        BookingMethod::Fifo,
        BookingMethod::Lifo,
        BookingMethod::Hifo,
        BookingMethod::Average,
        BookingMethod::None,
    ] {
        let txns = vec![vec![
            Leg::Buy {
                units: 9,
                cost: 101,
            },
            Leg::SellAt {
                units: 2,
                cost: 100,
            },
            Leg::SellAt {
                units: 2,
                cost: 100,
            },
        ]];
        check(m, None, &[(2, 100)], &txns).unwrap_or_else(|e| panic!("{m:?}: {e}"));
    }
}

/// The comparison reports a consumer that does not follow the record: one
/// decision flipped, and the realizations no longer match booking.
#[test]
fn the_comparison_can_report_a_disagreement() {
    // A buy beside the lot, which booking adds, recorded instead as a
    // reduction: a consumer that follows the record reduces lots that are
    // not there.
    let (opens, written) = ledger(
        None,
        &[(5, 100)],
        &[vec![Leg::Buy {
            units: 2,
            cost: 101,
        }]],
    );
    let (engine, mut booked) = book(BookingMethod::Fifo, &opens, written);
    let held = lots(engine.inventory(&STOCK.into()));
    let buy = booked
        .last_mut()
        .and_then(|txn| txn.postings.first_mut())
        .expect("the buy booked");
    assert_eq!(buy.booking, BookingDecision::Augment);
    buy.booking = BookingDecision::Reduce;
    let realized = realize(BookingMethod::Fifo, &opens, &booked);
    assert_ne!(realized.apply, held, "apply follows the flipped record");
    assert_ne!(
        realized.replay, held,
        "the replay follows the flipped record"
    );
    assert_ne!(
        realized.validator, held,
        "the validator follows the flipped record"
    );
    let asked = realize(BookingMethod::Fifo, &opens, &forgotten(&booked));
    assert_ne!(asked, realized, "and asking the inventory differs from it");
}

const ALL_METHODS: [BookingMethod; 7] = [
    BookingMethod::Strict,
    BookingMethod::StrictWithSize,
    BookingMethod::Fifo,
    BookingMethod::Lifo,
    BookingMethod::Hifo,
    BookingMethod::Average,
    BookingMethod::None,
];

/// The seed lots of #2958: 4 at 100 and 2 at 100.
const SEEDS_2958: [(u32, u32); 2] = [(4, 100), (2, 100)];

/// A transaction that sells the seed pool out, opens a short of 1 at 101,
/// and buys 5 at 102 and 5 at 100: under AVERAGE the account then holds a
/// short at 101 beside longs that average exactly 101 (#2958).
fn short_beside_longs_2958() -> Vec<Leg> {
    vec![
        Leg::SellAny { units: 6 },
        Leg::SellAt {
            units: 1,
            cost: 101,
        },
        Leg::Buy {
            units: 5,
            cost: 102,
        },
        Leg::Buy {
            units: 5,
            cost: 100,
        },
    ]
}

/// The stock account's units held long and short after booking `txns` on
/// the #2958 seeds.
fn sides_after(method: BookingMethod, txns: &[Vec<Leg>]) -> (Decimal, Decimal) {
    let (opens, written) = ledger(None, &SEEDS_2958, txns);
    let (engine, _) = book(method, &opens, written);
    let inv = engine
        .inventory(&STOCK.into())
        .expect("the account holds lots");
    let side = |long: bool| {
        inv.positions()
            .filter(|p| p.cost.is_some() && p.units.number.is_sign_positive() == long)
            .map(|p| p.units.number)
            .sum::<Decimal>()
    };
    (side(true), side(false))
}

/// The case proptest found for #2958, as it shrank (the committed seed in
/// `proptest-regressions/booking_record_tests.txt` replays it too).
///
/// Under AVERAGE the last sale, `-1 X {}`, sells from the longs, whose
/// average is 101, and books as `-1 X {101 USD}`. A short at 101 sits beside
/// them, so a consumer asking the inventory about the booked posting read
/// that cost as naming the short, and opened a second short where booking had
/// reduced the longs.
#[test]
fn an_average_sale_priced_like_a_short_beside_it_agrees_everywhere_2958() {
    let txns = vec![
        vec![
            Leg::SellAny { units: 1 },
            Leg::SellAny { units: 4 },
            Leg::Buy {
                units: 2,
                cost: 100,
            },
        ],
        vec![
            Leg::Buy {
                units: 5,
                cost: 102,
            },
            Leg::Buy {
                units: 5,
                cost: 100,
            },
            Leg::SellAny { units: 3 },
            Leg::SellAt {
                units: 1,
                cost: 101,
            },
        ],
        vec![Leg::SellAny { units: 1 }],
    ];
    for m in ALL_METHODS {
        for account in [None, Some(BookingMethod::Average)] {
            check(m, account, &SEEDS_2958, &txns)
                .unwrap_or_else(|e| panic!("{m:?} / {account:?}: {e}"));
        }
    }
    // And the sale reduced the longs: 9 left, the one short untouched.
    assert_eq!(
        sides_after(BookingMethod::Average, &txns),
        (Decimal::from(9), Decimal::from(-1))
    );
}

/// Shapes beside #2958's on the same account: several sales then a buy in
/// one transaction, partial and whole and over-reductions of the pool, a
/// sale stating the pool's average (which is also the short's cost), a sale
/// stating a cost that is neither, and a cover of the short.
#[test]
fn sales_beside_a_short_priced_at_the_pool_average_agree_everywhere_2958() {
    let at = |units, cost| Leg::SellAt { units, cost };
    let buy = |units, cost| Leg::Buy { units, cost };
    let any = |units| Leg::SellAny { units };
    let follow_ups: Vec<Vec<Leg>> = vec![
        vec![any(1)],
        vec![at(1, 101)],
        vec![any(1), any(4), buy(2, 100)],
        vec![any(3), at(3, 101), buy(1, 101)],
        vec![at(2, 101), any(2), buy(4, 102)],
        vec![any(5)],
        vec![any(10)],
        vec![any(5), any(5), any(1)],
        vec![any(12)],
        vec![at(1, 102)],
        vec![buy(1, 101)],
        vec![Leg::SellMerged { units: 2 }],
    ];
    for next in &follow_ups {
        let txns = vec![short_beside_longs_2958(), next.clone()];
        for m in ALL_METHODS {
            for account in [None, Some(BookingMethod::Average)] {
                check(m, account, &SEEDS_2958, &txns)
                    .unwrap_or_else(|e| panic!("{next:?} under {m:?} / {account:?}: {e}"));
            }
        }
    }
    // A sale stating the pool's average sells from the pool, as `{}` does,
    // rather than adding to the short that happens to cost the same.
    let stated = sides_after(
        BookingMethod::Average,
        &[short_beside_longs_2958(), vec![at(1, 101)]],
    );
    let elided = sides_after(
        BookingMethod::Average,
        &[short_beside_longs_2958(), vec![any(1)]],
    );
    assert_eq!(stated, (Decimal::from(9), Decimal::from(-1)));
    assert_eq!(stated, elided);
}

/// The mirror of [`short_beside_longs_2958`]: sells the seed pool out, then
/// opens a long of 1 at 101 and shorts of 5 at 102 and 5 at 100, so under
/// AVERAGE the account holds a long at 101 beside shorts that average
/// exactly 101.
fn long_beside_shorts_2958() -> Vec<Leg> {
    vec![
        Leg::SellAny { units: 6 },
        Leg::Buy {
            units: 1,
            cost: 101,
        },
        Leg::SellAt {
            units: 5,
            cost: 102,
        },
        Leg::SellAt {
            units: 5,
            cost: 100,
        },
    ]
}

/// The rule holds for a cover as it does for a sale (#2958): a buy stating
/// the shorts' average covers them, rather than opening a second long beside
/// the one that happens to cost the same.
#[test]
fn an_average_cover_priced_like_a_long_beside_it_agrees_everywhere_2958() {
    let txns = vec![
        long_beside_shorts_2958(),
        vec![Leg::Buy {
            units: 1,
            cost: 101,
        }],
    ];
    for m in ALL_METHODS {
        for account in [None, Some(BookingMethod::Average)] {
            check(m, account, &SEEDS_2958, &txns)
                .unwrap_or_else(|e| panic!("{m:?} / {account:?}: {e}"));
        }
    }
    // The buy covered the shorts: 9 short left, the one long untouched.
    assert_eq!(
        sides_after(BookingMethod::Average, &txns),
        (Decimal::from(1), Decimal::from(-9))
    );
}
